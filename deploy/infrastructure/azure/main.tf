terraform {
  required_version = ">= 1.10, < 2.0"
  required_providers {
    azurerm = { source = "hashicorp/azurerm", version = "~> 4.81" }
  }
}

variable "name" { type = string }
variable "region" { type = string }
variable "subscription" { type = string }
variable "machines" { type = number }
variable "machine_size" { type = string }
variable "kubernetes_version" { type = string }
variable "administrator_cidrs" { type = list(string) }
variable "namespace" { type = string }

provider "azurerm" {
  subscription_id                 = var.subscription
  storage_use_azuread             = true
  resource_provider_registrations = "none"
  features {}
}

data "azurerm_client_config" "current" {}

locals {
  suffix = substr(sha256("${var.subscription}/${var.name}"), 0, 16)
  tags   = { "managed-by" = "lean-cloud", "lean-cloud-cluster" = var.name }
}

resource "azurerm_resource_group" "cloud" {
  name     = "lean-cloud-${var.name}"
  location = var.region
  tags     = local.tags
}

resource "azurerm_container_registry" "cloud" {
  name                = "lc${local.suffix}"
  resource_group_name = azurerm_resource_group.cloud.name
  location            = var.region
  sku                 = "Basic"
  admin_enabled       = false
  tags                = local.tags
}

resource "azurerm_kubernetes_cluster" "cloud" {
  name                              = var.name
  resource_group_name               = azurerm_resource_group.cloud.name
  location                          = var.region
  dns_prefix                        = "lean-cloud-${var.name}"
  kubernetes_version                = var.kubernetes_version
  sku_tier                          = "Free"
  oidc_issuer_enabled               = true
  workload_identity_enabled         = true
  local_account_disabled            = true
  role_based_access_control_enabled = true
  azure_active_directory_role_based_access_control {
    tenant_id          = data.azurerm_client_config.current.tenant_id
    azure_rbac_enabled = true
  }
  api_server_access_profile { authorized_ip_ranges = var.administrator_cidrs }
  default_node_pool {
    name                 = "nodes"
    vm_size              = var.machine_size
    node_count           = var.machines
    os_disk_size_gb      = 32
    auto_scaling_enabled = false
  }
  identity { type = "SystemAssigned" }
  network_profile {
    network_plugin      = "azure"
    network_plugin_mode = "overlay"
    load_balancer_sku   = "standard"
  }
  tags = local.tags
}

resource "azurerm_role_assignment" "administrator" {
  scope                = azurerm_kubernetes_cluster.cloud.id
  role_definition_name = "Azure Kubernetes Service RBAC Cluster Admin"
  principal_id         = data.azurerm_client_config.current.object_id
}

resource "azurerm_role_assignment" "pull" {
  scope                            = azurerm_container_registry.cloud.id
  role_definition_name             = "AcrPull"
  principal_id                     = azurerm_kubernetes_cluster.cloud.kubelet_identity[0].object_id
  skip_service_principal_aad_check = true
}

resource "azurerm_storage_account" "cloud" {
  name                            = "lc${local.suffix}"
  resource_group_name             = azurerm_resource_group.cloud.name
  location                        = var.region
  account_tier                    = "Standard"
  account_replication_type        = "LRS"
  min_tls_version                 = "TLS1_2"
  shared_access_key_enabled       = false
  allow_nested_items_to_be_public = false
  tags                            = local.tags
}

resource "azurerm_storage_container" "cloud" {
  name                  = "cloud"
  storage_account_id    = azurerm_storage_account.cloud.id
  container_access_type = "private"
}

resource "azurerm_user_assigned_identity" "node" {
  name                = "cloud-node"
  resource_group_name = azurerm_resource_group.cloud.name
  location            = var.region
  tags                = local.tags
}

resource "azurerm_federated_identity_credential" "node" {
  name                      = "cloud-node"
  user_assigned_identity_id = azurerm_user_assigned_identity.node.id
  issuer                    = azurerm_kubernetes_cluster.cloud.oidc_issuer_url
  audience                  = ["api://AzureADTokenExchange"]
  subject                   = "system:serviceaccount:${var.namespace}:cloud-node"
}

resource "azurerm_role_assignment" "storage" {
  scope                            = "${azurerm_storage_account.cloud.id}/blobServices/default/containers/${azurerm_storage_container.cloud.name}"
  role_definition_name             = "Storage Blob Data Contributor"
  principal_id                     = azurerm_user_assigned_identity.node.principal_id
  skip_service_principal_aad_check = true
}

output "cloud" {
  value = {
    provider      = "azure"
    name          = var.name
    region        = var.region
    resourceGroup = azurerm_resource_group.cloud.name
    registry      = azurerm_container_registry.cloud.login_server
    registryName  = azurerm_container_registry.cloud.name
    repository    = "${azurerm_container_registry.cloud.login_server}/cloud-app"
    storageClass  = "managed-csi"
    storage = {
      provider  = "azure"
      account   = azurerm_storage_account.cloud.name
      container = azurerm_storage_container.cloud.name
      clientId  = azurerm_user_assigned_identity.node.client_id
      tenantId  = azurerm_user_assigned_identity.node.tenant_id
    }
  }
}
