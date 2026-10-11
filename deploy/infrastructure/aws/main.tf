terraform {
  required_version = ">= 1.10, < 2.0"
  required_providers {
    aws = { source = "hashicorp/aws", version = "~> 6.0" }
  }
}

variable "name" { type = string }
variable "region" { type = string }
variable "account" { type = string }
variable "profile" { type = string }
variable "machines" { type = number }
variable "machine_size" { type = string }
variable "architecture" { type = string }
variable "kubernetes_version" { type = string }
variable "administrator_cidrs" { type = list(string) }
variable "namespace" { type = string }

provider "aws" {
  region              = var.region
  profile             = var.profile
  allowed_account_ids = [var.account]
  default_tags { tags = { "managed-by" = "lean-cloud", "lean-cloud-cluster" = var.name } }
}

data "aws_availability_zones" "available" { state = "available" }

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
  availability_zone       = data.aws_availability_zones.available.names[count.index]
  map_public_ip_on_launch = true
  tags                    = { "kubernetes.io/role/elb" = "1" }
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

resource "aws_eks_node_group" "cloud" {
  cluster_name    = aws_eks_cluster.cloud.name
  node_group_name = "nodes"
  node_role_arn   = aws_iam_role.machines.arn
  subnet_ids      = aws_subnet.cloud[*].id
  instance_types  = [var.machine_size]
  ami_type        = var.architecture == "arm64" ? "AL2023_ARM_64_STANDARD" : "AL2023_x86_64_STANDARD"
  disk_size       = 20
  capacity_type   = "ON_DEMAND"
  scaling_config {
    desired_size = var.machines
    min_size     = var.machines
    max_size     = var.machines
  }
  update_config { max_unavailable = 1 }
  # Do not start paid machines if workload identity setup is rejected.
  depends_on = [aws_iam_role_policy_attachment.machines, aws_route_table_association.cloud,
  aws_iam_openid_connect_provider.cluster]
}

resource "aws_iam_openid_connect_provider" "cluster" {
  url            = aws_eks_cluster.cloud.identity[0].oidc[0].issuer
  client_id_list = ["sts.amazonaws.com"]
}

locals {
  issuer     = replace(aws_iam_openid_connect_provider.cluster.url, "https://", "")
  identities = { node = "${var.namespace}:cloud-node", disk = "kube-system:ebs-csi-controller-sa" }
}

resource "aws_iam_role" "workload" {
  for_each = local.identities
  name     = "lean-cloud-${var.name}-${each.key}"
  assume_role_policy = jsonencode({ Version = "2012-10-17", Statement = [{
    Effect = "Allow", Principal = { Federated = aws_iam_openid_connect_provider.cluster.arn },
    Action = "sts:AssumeRoleWithWebIdentity",
    Condition = { StringEquals = {
      "${local.issuer}:sub" = "system:serviceaccount:${each.value}",
      "${local.issuer}:aud" = "sts.amazonaws.com"
    } }
  }] })
}

resource "aws_iam_role_policy_attachment" "disk" {
  role       = aws_iam_role.workload["disk"].name
  policy_arn = "arn:aws:iam::aws:policy/service-role/AmazonEBSCSIDriverPolicy"
}

resource "aws_eks_addon" "disk" {
  cluster_name             = aws_eks_cluster.cloud.name
  addon_name               = "aws-ebs-csi-driver"
  service_account_role_arn = aws_iam_role.workload["disk"].arn
  depends_on               = [aws_eks_node_group.cloud, aws_iam_role_policy_attachment.disk]
}

resource "aws_ecr_repository" "cloud" {
  name                 = "lean-cloud-${var.name}"
  image_tag_mutability = "IMMUTABLE"
  image_scanning_configuration { scan_on_push = true }
  force_delete = true
}

resource "aws_s3_bucket" "cloud" {
  bucket        = "lean-cloud-${var.name}-${var.account}-${var.region}"
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
    registry     = split("/", aws_ecr_repository.cloud.repository_url)[0]
    repository   = aws_ecr_repository.cloud.repository_url
    storageClass = "lean-cloud-gp3"
    storage = {
      provider = "aws"
      bucket   = aws_s3_bucket.cloud.id
      region   = var.region
      roleArn  = aws_iam_role.workload["node"].arn
    }
  }
}
