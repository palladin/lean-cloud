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
  // Runtime suites deploy the already-built images through the shell helpers.
  output = ["type=docker"]
}

target "demo" {
  inherits = ["common"]
  context = "."
  dockerfile = "Dockerfile"
  target = "worker"
  tags = ["lean-cloud-demo:test"]
  cache-to = ["type=local,dest=.lean-cloud/buildkit-next/demo,mode=max,compression=zstd,compression-level=1,ignore-error=true"]
}

target "chaos" {
  inherits = ["common"]
  context = ".lean-cloud/ci-chaos/application"
  dockerfile = "../../../deploy/app/Dockerfile"
  tags = ["lean-cloud-chaos:test"]
  contexts = {
    sdk = "."
    node_assets = "deploy"
  }
  args = { APP_TARGET = "cloud_app" }
  cache-to = ["type=local,dest=.lean-cloud/buildkit-next/chaos,mode=max,compression=zstd,compression-level=1,ignore-error=true"]
}
