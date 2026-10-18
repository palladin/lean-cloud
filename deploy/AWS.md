# Run Lean Cloud on AWS

Run the same application and HTTP console as [local Docker](README.md#local-docker)
and [Azure](Azure.md). The optional `deploy/aws.sh` helper prepares EKS, EC2
machines, ECR images, S3 blobs and per-node EBS disks. The shared
`deploy/kubernetes.sh` manages the application. You can inspect or replace these
scripts; an [existing Kubernetes cluster](README.md#existing-kubernetes-cluster)
needs no provisioning helper.

The flow is **check tools → login → create cluster → build → publish → configure → up → connect → run**.

## 1. Check tools and sign in

Run from the repository directory. Install the [local prerequisites](README.md#local-docker),
[AWS CLI v2](https://docs.aws.amazon.com/cli/latest/userguide/getting-started-install.html),
[OpenTofu](https://opentofu.org/docs/intro/install/) (>= 1.10, < 2), and `kubectl`.
The helper checks for CLI 2.32 or newer, as required for
[AWS browser login](https://docs.aws.amazon.com/cli/latest/userguide/cli-configure-sign-in.html).

```sh
./deploy/aws.sh doctor
./deploy/aws.sh login lean-cloud --region eu-north-1
```

Use your own profile and region. In the **AWS (new)** project experience, use the
project's assigned region; it may not permit other regions. The examples use
Stockholm (`eu-north-1`). `init` uses the region configured in your profile unless
you supply `--region`; it never guesses one. If needed, pass the region explicitly
to both `login` and `init`.

For manual browser authorization, add `--remote` to `login`; paste the returned
code into your terminal only. For an already configured IAM Identity Center
profile, use `login PROFILE --sso`. Authentication stays with AWS CLI. All other
helper commands use the existing session and never initiate sign-in.

The account must permit EKS, EC2/VPC, ECR, S3, IAM roles and role passing, EKS Pod
Identity associations, and EBS provisioning. A successful login does not establish
these permissions. AWS (new) project policies can restrict them. The helper does
not change account plans, organization policies or advanced-feature settings.

## 2. Configure and create the cluster

Use a fresh state directory, a unique cluster name (up to 30 characters), and your
administrator machine's public IPv4 address. The helper does not look up your IP.

```sh
./deploy/aws.sh init .aws-infra --name aws-demo \
  --profile lean-cloud --region eu-north-1 --admin-cidr YOUR_PUBLIC_IPV4/32
./deploy/aws.sh show .aws-infra
./deploy/aws.sh plan .aws-infra
# Review the infrastructure plan before creating paid resources.
./deploy/aws.sh create .aws-infra
```

`init` writes `aws.tfvars.json`. It pins the signed-in account, detects the machine
architecture, selects an available zone, and pins a Kubernetes version in standard
support. You can edit the file before `plan`. `create` applies the saved plan;
configuration edits require a new plan. Retain the directory for cleanup.

The first plan binds this directory to the cluster name, account, region,
namespace and worker zone. Use a fresh directory to change these. VM count,
size and administrator access settings remain editable through a new plan.

Defaults: **one ARM64 `m7g.large` VM**, 32 GiB OS disk, and no automatic scaling.
The application will have one scheduler and three workers. `--machines`,
`--machine-size`, `--os-disk-gib`, `--worker-zone`, `--namespace`, and
`--kubernetes-version` override these defaults. `--account` verifies an expected
account ID before generating configuration.

The development pool stays in one availability zone so replacement VMs can attach
existing SQLite disks. EKS uses two subnets for its control plane. This is not a
multi-zone availability design. Worker machines use public subnets for outbound
access, with no public inbound application port and no NAT gateway. Kubernetes
API access is restricted to your administrator CIDR; node access uses the private
API endpoint.

`create` also saves cluster metadata, retrieves kubeconfig and creates an encrypted
gp3 StorageClass with `WaitForFirstConsumer`. If the AWS resources were created
but these final steps failed, retry them without applying the provision plan again.
`credentials` refreshes the metadata from OpenTofu state before retrieving kubeconfig:

```sh
./deploy/aws.sh credentials .aws-infra
./deploy/aws.sh storage .aws-infra
```

## 3. Build and publish

```sh
./deploy/build.sh --platform linux/arm64 . lean-cloud-demo:dev
./deploy/aws.sh publish .aws-infra lean-cloud-demo:dev demo-v1
```

Use `linux/amd64` for an x86 machine. The image contains `log-summary` and
`sum-squares`. For your own registered workflows, replace the build's application
path; see [application setup](README.md#your-application).

`publish` uses your existing AWS login to authenticate Docker to ECR. It passes
the registry password through stdin. Images have immutable tags; choose a new tag
for changed code. An interrupted upload can be retried. If the tag already exists,
`configure` can use that published image without rebuilding or republishing.

## 4. Configure and start

```sh
./deploy/aws.sh configure .aws-infra .aws-deployment demo-v1 3
./deploy/kubernetes.sh show .aws-deployment
# Review deployment.json, storage.json and resources.json.
./deploy/kubernetes.sh up .aws-deployment
./deploy/kubernetes.sh status .aws-deployment
```

`configure` writes files only. It resolves the image tag to an immutable digest,
sets the kubeconfig path and storage settings, and renders the ordinary Kubernetes
resources. Each scheduler/worker has an HTTP inbox and SQLite database on its own
EBS disk. Shared blobs and replay records live in S3.

EKS Pod Identity delivers short-lived credentials through its node-local agent;
there are no static AWS access keys in the application configuration. The
application role can list/read/write/delete objects only in this deployment's
bucket. Existing clusters using IRSA are also supported (see below).

Worker count is independent of VM count. Kubernetes places the containers. Before
the first `up`, adjust `cpuMillis`, `memoryMiB`, `diskGiB`, and optionally
`schedulerResources` in deployment.json. Large application startup downloads can
set `startupSeconds` (for LeanBuild, use 900). Resource requests must fit the VMs.

## 5. Connect and run

Keep this tunnel running in a terminal:

```sh
./deploy/kubernetes.sh connect .aws-deployment 8081
```

In a second terminal, run `lake exe lean_cloud`. At the `cloud>` prompt:

```text
connect aws-demo http://127.0.0.1:8081 --token-file .aws-deployment/client.token
programs
run log-summary --id my-logs
ps
watch my-logs
```

Press `q` to leave watch. When completed, `result my-logs` should print
`files=16, errors=24`. Use a new run ID for each new workflow.

The scheduler is a private ClusterIP service. `127.0.0.1:8081` is the local end of
the Kubernetes tunnel, not a public AWS address. Restart `connect` if the scheduler
pod or tunnel restarts. The CLI uses the same HTTP path as local and Azure.

## 6. Stop, scale, and clean up

```sh
./deploy/kubernetes.sh down .aws-deployment     # stop application; retain disks
./deploy/kubernetes.sh up .aws-deployment       # recover
./deploy/kubernetes.sh scale .aws-deployment 5  # workers, not VMs
```

Scaling uses the same stop barrier as local and Azure. Old pods must stop before
replacements start. Retired workers keep their disks. Changes to VM count belong
in the infrastructure configuration followed by `plan` and `create`.

**Stopping the application does not stop AWS billing.** To remove this example:

```sh
./deploy/kubernetes.sh clean .aws-deployment --yes
./deploy/aws.sh destroy-plan .aws-infra
# Review the deletion plan: it includes the bucket and all its blobs.
./deploy/aws.sh destroy .aws-infra
```

Clean the application first so the EBS driver can delete its disks. `destroy`
refuses while tagged application disks remain. It then applies the saved deletion
plan and checks state, EKS and VPC removal. The infrastructure's S3 bucket contents
and ECR images are also deleted. Keep local state until cleanup succeeds.
If provisioning failed before starting an application, use `destroy-plan` and
`destroy` to clean up the resources already created.

EKS charges separately for the control plane, machines, disks, public IPv4
addresses, registry and storage. See [EKS pricing](https://aws.amazon.com/eks/pricing/).
A small development cluster should be created for a bounded test and destroyed
when finished; stopping pods alone does not remove those charges.

## Existing EKS clusters

Follow the [existing Kubernetes instructions](README.md#existing-kubernetes-cluster).
Provide an existing EBS CSI StorageClass with `WaitForFirstConsumer`, an immutable
image, and a private storage.json:

```json
{"provider":"s3","endpoint":"https://s3.eu-north-1.amazonaws.com","region":"eu-north-1","bucket":"YOUR_BUCKET","provisioned":true,"authentication":{"kind":"podIdentity"}}
```

Your administrator must associate an IAM role with the deployment namespace's
`cloud-node` service account and install the Pod Identity agent. The EBS CSI driver
needs its own permissions. The helper does not take ownership of your cluster or
change its IAM configuration.

For IRSA, use `"authentication":{"kind":"workload"}` and set
`serviceAccountAnnotations` to `{"eks.amazonaws.com/role-arn":"YOUR_ROLE_ARN"}`.
Both methods refresh temporary credentials; there is no AWS SDK or AWS CLI inside
the application container.
