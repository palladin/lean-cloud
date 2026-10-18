terraform {
  required_version = ">= 1.10, < 2.0"
  required_providers {
    aws = { source = "hashicorp/aws", version = "~> 6.0" }
  }
}

variable "name" {
  type = string
  validation {
    condition     = can(regex("^[a-z][a-z0-9-]{0,29}$", var.name))
    error_message = "Use a lowercase cluster name of at most 30 characters."
  }
}
variable "region" { type = string }
variable "account" { type = string }
variable "profile" { type = string }
variable "machines" {
  type = number
  validation {
    condition     = var.machines >= 1 && floor(var.machines) == var.machines
    error_message = "Use at least one machine."
  }
}
variable "os_disk_size_gb" {
  type    = number
  default = 32
  validation {
    condition     = var.os_disk_size_gb >= 32 && floor(var.os_disk_size_gb) == var.os_disk_size_gb
    error_message = "Use an OS disk of at least 32 GiB."
  }
}
variable "worker_zone" { type = string }
variable "machine_size" { type = string }
variable "architecture" {
  type = string
  validation {
    condition     = contains(["arm64", "amd64"], var.architecture)
    error_message = "Architecture must be arm64 or amd64."
  }
}
variable "kubernetes_version" { type = string }
variable "administrator_cidrs" { type = list(string) }
variable "namespace" { type = string }

provider "aws" {
  region              = var.region
  profile             = var.profile
  allowed_account_ids = [var.account]
  default_tags { tags = { "managed-by" = "lean-cloud", "lean-cloud-cluster" = var.name } }
}

data "aws_availability_zones" "available" {
  state = "available"
  filter {
    name   = "zone-type"
    values = ["availability-zone"]
  }
}
locals {
  # EKS needs two zones; the small development node pool stays in one so that a
  # replacement VM can always attach the existing SQLite disks. Not multi-AZ HA.
  zones = concat([var.worker_zone], slice(sort(tolist(setsubtract(
  toset(data.aws_availability_zones.available.names), toset([var.worker_zone])))), 0, 1))
}

resource "aws_vpc" "cloud" {
  cidr_block           = "10.80.0.0/16"
  enable_dns_support   = true
  enable_dns_hostnames = true
}

resource "aws_internet_gateway" "cloud" { vpc_id = aws_vpc.cloud.id }

# Development pools use public subnets with no inbound node ports and no NAT
# gateway charge. Kubernetes' API is private to nodes and CIDR-limited to operators.
resource "aws_subnet" "cloud" {
  count                   = 2
  vpc_id                  = aws_vpc.cloud.id
  cidr_block              = cidrsubnet(aws_vpc.cloud.cidr_block, 8, count.index)
  availability_zone       = local.zones[count.index]
  map_public_ip_on_launch = true
}

resource "aws_route_table" "cloud" {
  vpc_id = aws_vpc.cloud.id
  route {
    cidr_block = "0.0.0.0/0"
    gateway_id = aws_internet_gateway.cloud.id
  }
}

resource "aws_route_table_association" "cloud" {
  count          = 2
  subnet_id      = aws_subnet.cloud[count.index].id
  route_table_id = aws_route_table.cloud.id
}

resource "aws_iam_role" "cluster" {
  name = "lean-cloud-${var.name}-cluster"
  assume_role_policy = jsonencode({ Version = "2012-10-17", Statement = [{
    Effect = "Allow", Principal = { Service = "eks.amazonaws.com" }, Action = "sts:AssumeRole"
  }] })
}

resource "aws_iam_role_policy_attachment" "cluster" {
  role       = aws_iam_role.cluster.name
  policy_arn = "arn:aws:iam::aws:policy/AmazonEKSClusterPolicy"
}

resource "aws_eks_cluster" "cloud" {
  name     = var.name
  role_arn = aws_iam_role.cluster.arn
  version  = var.kubernetes_version
  access_config {
    authentication_mode                         = "API"
    bootstrap_cluster_creator_admin_permissions = true
  }
  vpc_config {
    subnet_ids              = aws_subnet.cloud[*].id
    endpoint_private_access = true
    endpoint_public_access  = true
    public_access_cidrs     = var.administrator_cidrs
  }
  upgrade_policy { support_type = "STANDARD" }
  depends_on = [aws_iam_role_policy_attachment.cluster]
}

resource "aws_iam_role" "machines" {
  name = "lean-cloud-${var.name}-machines"
  assume_role_policy = jsonencode({ Version = "2012-10-17", Statement = [{
    Effect = "Allow", Principal = { Service = "ec2.amazonaws.com" }, Action = "sts:AssumeRole"
  }] })
}

resource "aws_iam_role_policy_attachment" "machines" {
  for_each   = toset(["AmazonEKSWorkerNodePolicy", "AmazonEC2ContainerRegistryPullOnly", "AmazonEKS_CNI_Policy"])
  role       = aws_iam_role.machines.name
  policy_arn = "arn:aws:iam::aws:policy/${each.key}"
}

resource "aws_launch_template" "machines" {
  name_prefix = "lean-cloud-${var.name}-"
  metadata_options {
    http_tokens                 = "required"
    http_put_response_hop_limit = 1
  }
  block_device_mappings {
    device_name = "/dev/xvda"
    ebs {
      volume_size           = var.os_disk_size_gb
      volume_type           = "gp3"
      encrypted             = true
      delete_on_termination = true
    }
  }
}

resource "aws_eks_node_group" "cloud" {
  cluster_name    = aws_eks_cluster.cloud.name
  node_group_name = "nodes"
  node_role_arn   = aws_iam_role.machines.arn
  subnet_ids      = [aws_subnet.cloud[0].id]
  instance_types  = [var.machine_size]
  ami_type        = var.architecture == "arm64" ? "AL2023_ARM_64_STANDARD" : "AL2023_x86_64_STANDARD"
  launch_template {
    id      = aws_launch_template.machines.id
    version = aws_launch_template.machines.latest_version
  }
  capacity_type = "ON_DEMAND"
  scaling_config {
    desired_size = var.machines
    min_size     = var.machines
    max_size     = var.machines
  }
  update_config { max_unavailable = 1 }
  depends_on = [aws_iam_role_policy_attachment.machines, aws_route_table_association.cloud,
  aws_eks_pod_identity_association.node]
}

locals {
  identities = {
    node = { namespace = var.namespace, service_account = "cloud-node" }
    disk = { namespace = "kube-system", service_account = "ebs-csi-controller-sa" }
  }
}

resource "aws_iam_role" "workload" {
  for_each = local.identities
  name     = "lean-cloud-${var.name}-${each.key}"
  assume_role_policy = jsonencode({ Version = "2012-10-17", Statement = [{
    Effect = "Allow", Principal = { Service = "pods.eks.amazonaws.com" },
    Action = ["sts:AssumeRole", "sts:TagSession"],
    Condition = {
      StringEquals = {
        "aws:RequestTag/eks-cluster-arn"            = aws_eks_cluster.cloud.arn
        "aws:RequestTag/kubernetes-namespace"       = each.value.namespace
        "aws:RequestTag/kubernetes-service-account" = each.value.service_account
      }
    }
  }] })
}

resource "aws_eks_pod_identity_association" "node" {
  cluster_name    = aws_eks_cluster.cloud.name
  namespace       = var.namespace
  service_account = "cloud-node"
  role_arn        = aws_iam_role.workload["node"].arn
  depends_on      = [aws_iam_role_policy.storage]
}

resource "aws_eks_addon" "identity" {
  cluster_name = aws_eks_cluster.cloud.name
  addon_name   = "eks-pod-identity-agent"
  depends_on   = [aws_eks_node_group.cloud]
}

resource "aws_iam_role_policy_attachment" "disk" {
  role       = aws_iam_role.workload["disk"].name
  policy_arn = "arn:aws:iam::aws:policy/AmazonEBSCSIDriverPolicyV2"
}

resource "aws_eks_addon" "disk" {
  cluster_name = aws_eks_cluster.cloud.name
  addon_name   = "aws-ebs-csi-driver"
  pod_identity_association {
    role_arn        = aws_iam_role.workload["disk"].arn
    service_account = "ebs-csi-controller-sa"
  }
  depends_on = [aws_eks_addon.identity, aws_iam_role_policy_attachment.disk]
}

resource "aws_ecr_repository" "cloud" {
  name                 = "lean-cloud-${var.name}"
  image_tag_mutability = "IMMUTABLE"
  image_scanning_configuration { scan_on_push = true }
  force_delete = true
}

resource "aws_s3_bucket" "cloud" {
  bucket        = "lean-cloud-${substr(var.name, 0, 20)}-${substr(sha256("${var.account}/${var.region}/${var.name}"), 0, 16)}"
  force_destroy = true
}

resource "aws_s3_bucket_public_access_block" "cloud" {
  bucket                  = aws_s3_bucket.cloud.id
  block_public_acls       = true
  block_public_policy     = true
  ignore_public_acls      = true
  restrict_public_buckets = true
}

resource "aws_s3_bucket_server_side_encryption_configuration" "cloud" {
  bucket = aws_s3_bucket.cloud.id
  rule {
    apply_server_side_encryption_by_default { sse_algorithm = "AES256" }
  }
}

resource "aws_s3_bucket_policy" "cloud" {
  bucket = aws_s3_bucket.cloud.id
  policy = jsonencode({ Version = "2012-10-17", Statement = [{
    Effect    = "Deny", Principal = "*", Action = "s3:*",
    Resource  = [aws_s3_bucket.cloud.arn, "${aws_s3_bucket.cloud.arn}/*"],
    Condition = { Bool = { "aws:SecureTransport" = "false" } }
  }] })
}

resource "aws_iam_role_policy" "storage" {
  role = aws_iam_role.workload["node"].id
  policy = jsonencode({ Version = "2012-10-17", Statement = [
    { Effect = "Allow", Action = ["s3:ListBucket"], Resource = aws_s3_bucket.cloud.arn },
    { Effect = "Allow", Action = ["s3:GetObject", "s3:PutObject", "s3:DeleteObject"], Resource = "${aws_s3_bucket.cloud.arn}/*" }
  ] })
}

output "cloud" {
  value = {
    provider     = "aws"
    name         = var.name
    region       = var.region
    account      = var.account
    vpcId        = aws_vpc.cloud.id
    registry     = split("/", aws_ecr_repository.cloud.repository_url)[0]
    repository   = aws_ecr_repository.cloud.repository_url
    storageClass = "lean-cloud-${var.name}-gp3"
    storage = {
      provider       = "aws"
      bucket         = aws_s3_bucket.cloud.id
      region         = var.region
      authentication = "podIdentity"
    }
  }
}
