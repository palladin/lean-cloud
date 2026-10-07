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
  // CLI deploy loads its own deployment image from this builder's cache.
  // Exporting extra, unused images to the Docker daemon wastes setup time.
  output = ["type=cacheonly"]
}

target "demo" {
  inherits = ["common"]
  context = "."
  dockerfile = "Dockerfile"
  target = "worker"
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
  cache-to = ["type=local,dest=.lean-cloud/buildkit-next/chaos,mode=max,compression=zstd,compression-level=1,ignore-error=true"]
}
