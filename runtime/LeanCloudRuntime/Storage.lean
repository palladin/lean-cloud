import LeanCloudRuntime.S3
import LeanCloudRuntime.AzureBlob

namespace LeanCloudRuntime.Storage
open Lean

inductive Config where
  | s3 (config : S3.Config)
  | azure (config : AzureBlob.Config)

instance : ToJson Config where
  toJson
    | .s3 config => (toJson config).setObjVal! "provider" (toJson "s3")
    | .azure config => (toJson config).setObjVal! "provider" (toJson "azure")

instance : FromJson Config where
  fromJson? json := do
    match ← json.getObjValAs? String "provider" with
    | "s3" => Config.s3 <$> fromJson? json
    | "azure" => Config.azure <$> fromJson? json
    | _ => throw "Unknown blob storage provider"

def Config.validate : Config → Except String Unit
  | .s3 config => config.validate
  | .azure config => config.validate

def Config.objects : Config → ObjectStore
  | .s3 config => S3.objects config
  | .azure config => AzureBlob.objects config

end LeanCloudRuntime.Storage
