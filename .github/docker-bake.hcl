variable "LEAN_VERSION" {
  default = "4.34.1"
}

// Also usable locally; CI adds its legacy GitHub cache imports via --set.
group "default" {
  targets = ["demo", "chaos"]
}

target "common" {
  args = { LEAN_VERSION = LEAN_VERSION }
  cache-from = [
    "type=local,src=.lean-cloud/buildkit/demo",
    "type=local,src=.lean-cloud/buildkit/chaos"
  ]
  output = ["type=docker"]
}

target "demo" {
  inherits = ["common"]
  context = "."
  dockerfile = "Dockerfile"
  target = "worker"
  tags = ["lean-cloud-ci:demo"]
  cache-to = ["type=local,dest=.lean-cloud/buildkit-next/demo,mode=max,compression=zstd,compression-level=1,ignore-error=true"]
}

target "chaos" {
  inherits = ["common"]
  context = ".lean-cloud/ci-chaos/application"
  dockerfile = ".lean-cloud/ci-chaos/deployment/Dockerfile"
  contexts = {
    sdk = "."
    node_assets = ".lean-cloud/ci-chaos/application/.lean-cloud/ci-chaos/deployment"
  }
  args = { APP_TARGET = "cloud_app" }
  tags = ["lean-cloud-ci:chaos"]
  cache-to = ["type=local,dest=.lean-cloud/buildkit-next/chaos,mode=max,compression=zstd,compression-level=1,ignore-error=true"]
}
