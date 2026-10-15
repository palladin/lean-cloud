# Render an ordinary Compose file. Node IDs and volumes remain stable across runs.
. as $c |
def node($role): {
  image: $c.image, restart: "unless-stopped", stop_grace_period: "60s",
  hostname: ($role + "-mailbox"),
  networks: {default: {aliases: [($role + "-mailbox")]}},
  command: [(if $role == "scheduler" then "serve-scheduler" else "serve-worker" end), "/etc/lean-cloud/config.json"],
  environment: ({CLOUD_INBOX_DATABASE:"/data/inbox.sqlite"} +
    (if ($c.nodeName // "") == "" then {} else {CLOUD_NODE_NAME:$c.nodeName} end) +
    (if $role == "scheduler" then {} else {CLOUD_WORKER_ID:$role} end)),
  volumes: [($role + "-data:/data"), {type:"bind",source:($c.directory + "/config.json"),target:"/etc/lean-cloud/config.json",read_only:true}],
  logging: {driver:"json-file",options:{"max-size":"10m","max-file":"2"}}
} + (if $role == "scheduler" then {ports:[("127.0.0.1:" + (if $c.port==0 then "" else ($c.port|tostring) end) + ":8080")]} else {} end);
(["scheduler"] + [range(1; $c.workers + 1) | "worker\(.)"]) as $roles |
{ name: $c.name,
  services: ({blobs: {
    image:"chrislusf/seaweedfs:4.48", restart:"unless-stopped",
    command:["server","-ip=blobs","-ip.bind=0.0.0.0","-dir=/data","-volume.max=20","-master.volumeSizeLimitMB=100","-filer","-s3","-s3.config=/etc/seaweedfs/s3.json"],
    volumes:["blob-data:/data", {type:"bind",source:($c.directory+"/s3.json"),target:"/etc/seaweedfs/s3.json",read_only:true}, {type:"bind",source:($c.directory+"/filer.toml"),target:"/etc/seaweedfs/filer.toml",read_only:true}],
    healthcheck:{test:["CMD-SHELL","wget -S -O /dev/null http://localhost:8333/ 2>&1 | grep -q 'HTTP/1.1 403'"],interval:"2s",timeout:"3s",retries:40}
  }} + (reduce $roles[] as $r ({}; .[$r] = node($r)))),
  volumes: (reduce (["blob-data"] + [range(1; $c.retainedWorkers + 1) | "worker\(.)-data"] + ["scheduler-data"])[] as $v ({}; .[$v] = {external:true,name:($c.name+"_"+$v)})) }
