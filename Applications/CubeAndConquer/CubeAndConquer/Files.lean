import LeanCloudRuntime.Files

namespace CubeAndConquer
abbrev FileRef := LeanCloudRuntime.FileRef
abbrev FileRef.validate (ref : FileRef) := LeanCloudRuntime.FileRef.validate ref
namespace Files
export LeanCloudRuntime.Files (chunkSize digest upload download putText readText metadataLimit putJson readJson)
end Files
end CubeAndConquer
