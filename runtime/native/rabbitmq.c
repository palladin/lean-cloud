/* RabbitMQ transport only; workflow interpretation stays in Lean.
 * Each worker owns separate publisher and consumer connections. */
#include <lean/lean.h>
#include <amqp.h>
#include <amqp_tcp_socket.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <sys/time.h>

typedef struct {
    amqp_connection_state_t publisher, consumer;
    char *queue;
    uint64_t sequence, delivery;
} cloud_queue;

static lean_obj_res error(const char *message) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}

static void disconnect(cloud_queue *q) {
    /* Destroying the sockets requeues unacknowledged deliveries. Never delete
       the durable queue, and never acknowledge from cleanup. */
    if (q->consumer) { amqp_destroy_connection(q->consumer); q->consumer = NULL; }
    if (q->publisher) { amqp_destroy_connection(q->publisher); q->publisher = NULL; }
    q->delivery = 0;
}
static void finalize(void *ptr) {
    cloud_queue *q = ptr;
    disconnect(q);
    free(q->queue);
    free(q);
}
static void foreach(void *ptr, b_lean_obj_arg fn) { (void)ptr; (void)fn; }
static lean_external_class *queue_class;
static pthread_once_t once = PTHREAD_ONCE_INIT;
static void register_class(void) { queue_class = lean_register_external_class(finalize, foreach); }

static int connect_one(amqp_connection_state_t *out, const char *host, int port,
                       const char *vhost, const char *user, const char *password) {
    *out = amqp_new_connection();
    if (!*out) return 0;
    amqp_socket_t *socket = amqp_tcp_socket_new(*out);
    struct timeval timeout = {10, 0};
    if (!socket || amqp_socket_open_noblock(socket, host, port, &timeout) != AMQP_STATUS_OK)
        return 0;
    amqp_set_rpc_timeout(*out, &timeout);
    if (amqp_login(*out, vhost, 0, 131072, 0, AMQP_SASL_METHOD_PLAIN,
                   user, password).reply_type != AMQP_RESPONSE_NORMAL) return 0;
    amqp_channel_open(*out, 1);
    return amqp_get_rpc_reply(*out).reply_type == AMQP_RESPONSE_NORMAL;
}

LEAN_EXPORT lean_obj_res lc_queue_open(b_lean_obj_arg host, uint32_t port,
    b_lean_obj_arg vhost, b_lean_obj_arg user, b_lean_obj_arg password,
    b_lean_obj_arg name, uint8_t create, uint8_t consume, lean_obj_arg world) {
    (void)world;
    cloud_queue *q = calloc(1, sizeof(*q));
    if (!q) return error("RabbitMQ allocation failed");
    q->queue = strdup(lean_string_cstr(name));
    if (!q->queue) { free(q); return error("RabbitMQ allocation failed"); }
    if (!connect_one(&q->publisher, lean_string_cstr(host), (int)port,
          lean_string_cstr(vhost), lean_string_cstr(user), lean_string_cstr(password))) {
        finalize(q); return error("RabbitMQ publisher connection failed");
    }
    amqp_table_entry_t entries[2] = {0};
    entries[0].key = amqp_cstring_bytes("x-queue-type");
    entries[0].value.kind = AMQP_FIELD_KIND_UTF8;
    entries[0].value.value.bytes = amqp_cstring_bytes("quorum");
    entries[1].key = amqp_cstring_bytes("x-delivery-limit");
    entries[1].value.kind = AMQP_FIELD_KIND_I32;
    entries[1].value.value.i32 = -1;
    amqp_table_t arguments = {2, entries};
    amqp_queue_declare(q->publisher, 1, amqp_cstring_bytes(q->queue), !create,
                       1, 0, 0, create ? arguments : amqp_empty_table);
    if (amqp_get_rpc_reply(q->publisher).reply_type != AMQP_RESPONSE_NORMAL) {
        finalize(q); return error("RabbitMQ queue declaration failed");
    }
    amqp_confirm_select(q->publisher, 1);
    if (amqp_get_rpc_reply(q->publisher).reply_type != AMQP_RESPONSE_NORMAL) {
        finalize(q); return error("RabbitMQ publisher confirms unavailable");
    }
    if (consume) {
        if (!connect_one(&q->consumer, lean_string_cstr(host), (int)port,
              lean_string_cstr(vhost), lean_string_cstr(user), lean_string_cstr(password))) {
            finalize(q); return error("RabbitMQ consumer connection failed");
        }
        amqp_basic_qos(q->consumer, 1, 0, 1, 0);
        if (amqp_get_rpc_reply(q->consumer).reply_type != AMQP_RESPONSE_NORMAL) {
            finalize(q); return error("RabbitMQ prefetch setup failed");
        }
        amqp_basic_consume(q->consumer, 1, amqp_cstring_bytes(q->queue),
                           amqp_empty_bytes, 0, 0, 0, amqp_empty_table);
        if (amqp_get_rpc_reply(q->consumer).reply_type != AMQP_RESPONSE_NORMAL) {
            finalize(q); return error("RabbitMQ consumer setup failed");
        }
    }
    pthread_once(&once, register_class);
    return lean_io_result_mk_ok(lean_alloc_external(queue_class, q));
}

LEAN_EXPORT lean_obj_res lc_queue_close(b_lean_obj_arg handle, lean_obj_arg world) {
    (void)world;
    disconnect(lean_get_external_data(handle));
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lc_queue_publish(b_lean_obj_arg handle, b_lean_obj_arg payload,
                                         lean_obj_arg world) {
    (void)world;
    cloud_queue *q = lean_get_external_data(handle);
    if (!q->publisher) return error("RabbitMQ publisher is closed");
    amqp_basic_properties_t properties = {0};
    properties._flags = AMQP_BASIC_DELIVERY_MODE_FLAG | AMQP_BASIC_CONTENT_TYPE_FLAG;
    properties.delivery_mode = 2;
    properties.content_type = amqp_cstring_bytes("application/json");
    amqp_bytes_t body = {lean_string_size(payload) - 1, (void *)lean_string_cstr(payload)};
    uint64_t sequence = ++q->sequence;
    if (amqp_basic_publish(q->publisher, 1, amqp_empty_bytes, amqp_cstring_bytes(q->queue),
                           1, 0, &properties, body) != AMQP_STATUS_OK) {
        disconnect(q); return error("RabbitMQ publish failed; outcome unknown");
    }
    /* Only one outstanding publication on this connection. A mandatory return
       is failure even if the broker would subsequently confirm it. */
    struct timeval timeout = {30, 0};
    amqp_frame_t frame;
    for (;;) {
        int status = amqp_simple_wait_frame_noblock(q->publisher, &frame, &timeout);
        if (status != AMQP_STATUS_OK) {
            disconnect(q); return error("RabbitMQ publish confirmation lost; outcome unknown");
        }
        if (frame.frame_type == AMQP_FRAME_HEARTBEAT) continue;
        if (frame.frame_type == AMQP_FRAME_METHOD && frame.channel == 1 &&
            frame.payload.method.id == AMQP_BASIC_ACK_METHOD) {
            amqp_basic_ack_t *ack = frame.payload.method.decoded;
            if (ack->delivery_tag == sequence) {
                amqp_maybe_release_buffers(q->publisher);
                return lean_io_result_mk_ok(lean_box(0));
            }
        }
        disconnect(q);
        return error("RabbitMQ publication rejected, unroutable, or unexpected confirmation");
    }
}

LEAN_EXPORT lean_obj_res lc_queue_receive(b_lean_obj_arg handle, lean_obj_arg world) {
    (void)world;
    cloud_queue *q = lean_get_external_data(handle);
    if (!q->consumer) return error("RabbitMQ consumer is closed");
    if (q->delivery) return error("RabbitMQ delivery must be acknowledged before receiving again");
    amqp_maybe_release_buffers(q->consumer);
    struct timeval timeout = {0, 250000};
    amqp_envelope_t envelope;
    amqp_rpc_reply_t reply = amqp_consume_message(q->consumer, &envelope, &timeout, 0);
    if (reply.reply_type == AMQP_RESPONSE_LIBRARY_EXCEPTION && reply.library_error == AMQP_STATUS_TIMEOUT)
        return lean_io_result_mk_ok(lean_box(0));
    if (reply.reply_type != AMQP_RESPONSE_NORMAL) {
        disconnect(q); return error("RabbitMQ receive failed");
    }
    q->delivery = envelope.delivery_tag;
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_mk_string_from_bytes(envelope.message.body.bytes, envelope.message.body.len));
    lean_ctor_set(pair, 1, lean_box_uint64(envelope.delivery_tag));
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, pair);
    amqp_destroy_envelope(&envelope);
    return lean_io_result_mk_ok(some);
}

LEAN_EXPORT lean_obj_res lc_queue_ack(b_lean_obj_arg handle, b_lean_obj_arg owner,
                                      uint64_t receipt, lean_obj_arg world) {
    (void)world;
    cloud_queue *q = lean_get_external_data(handle);
    if (q != lean_get_external_data(owner)) return lean_io_result_mk_ok(lean_box(0));
    if (!q->consumer) return error("RabbitMQ consumer is closed");
    if (!receipt || q->delivery != receipt) return lean_io_result_mk_ok(lean_box(0));
    if (amqp_basic_ack(q->consumer, 1, receipt, 0) != AMQP_STATUS_OK) {
        disconnect(q); return error("RabbitMQ acknowledgement lost; outcome unknown");
    }
    /* An RPC on the same channel is a barrier after the asynchronous ack.
       Failure still has an uncertain outcome and must not be retried as success. */
    amqp_basic_qos(q->consumer, 1, 0, 1, 0);
    if (amqp_get_rpc_reply(q->consumer).reply_type != AMQP_RESPONSE_NORMAL) {
        disconnect(q); return error("RabbitMQ acknowledgement barrier failed; outcome unknown");
    }
    q->delivery = 0;
    return lean_io_result_mk_ok(lean_box(1));
}
