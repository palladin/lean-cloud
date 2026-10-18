import Wiki.Model
import LeanCloud.Source

namespace Wiki
open LeanCloud

structure Backend (m : Type → Type) where
  source : FileRef → m Source
  prepare : PrepareRequest → Part → m (Array Shard)
  publish : Dataset → m FileRef
  dataset : FileRef → m Dataset
  count : CountRequest → Shard → m FileRef
  sumCounts : CountRequest → Array FileRef → m Counts
  validateGrep : GrepRequest → m Unit
  grep : GrepRequest → Shard → m Matches
  publishMatches : MatchManifest → m FileRef

def mergeCounts (r : CountRequest) (parts : Array Counts) : Counts := {
  articles := parts.foldl (fun n p => n + p.articles) 0
  counts := r.vocabulary.mapIdx fun i name => {
    word := name
    occurrences := parts.foldl (fun n p => n + p.counts[i]!.occurrences) 0
    articles := parts.foldl (fun n p => n + p.counts[i]!.articles) 0 } }

def prepare [Monad m] [MonadCloudExec m] (b : Backend m) (r : PrepareRequest) : Cloud m Prepared := cloud {
  match r.validate with | .error e => Cloud.fail e | .ok () => pure ()
  let source ← Cloud.exec (fun _ => b.source r.source) "read dump manifest"
  let parts ← Cloud.parallel fun _ => (source.parts.map fun part => cloud {
    Cloud.exec (fun _ => b.prepare r part) "parse dump part"
  })
  let shards := parts.flatten
  let dataset ← Cloud.exec (fun _ => b.publish {
    label := source.label, source := r.source, namespaceId := r.namespaceId
    includeRedirects := r.includeRedirects, shards }) "publish dataset"
  return { dataset, shards := shards.size
           articles := shards.foldl (fun n s => n + s.articles) 0 }
}

def count [Monad m] [MonadCloudExec m] (b : Backend m) (r : CountRequest) : Cloud m Counts := cloud {
  match r.validate with | .error e => Cloud.fail e | .ok () => pure ()
  let dataset ← Cloud.exec (fun _ => b.dataset r.dataset) "read dataset"
  let parts ← Cloud.parallel fun _ => (dataset.shards.map fun shard => cloud {
    Cloud.exec (fun _ => b.count r shard) "count vocabulary"
  })
  Cloud.exec (fun _ => b.sumCounts r parts) "combine counts"
}

def grep [Monad m] [MonadCloudExec m] (b : Backend m) (r : GrepRequest) : Cloud m GrepReport := cloud {
  match r.validate with | .error e => Cloud.fail e | .ok () => pure ()
  Cloud.exec (fun _ => b.validateGrep r) "validate search pattern"
  let dataset ← Cloud.exec (fun _ => b.dataset r.dataset) "read dataset"
  let parts ← Cloud.parallel fun _ => (dataset.shards.map fun shard => cloud {
    Cloud.exec (fun _ => b.grep r shard) "search articles"
  })
  let results ← Cloud.exec (fun _ => b.publishMatches { request := r, parts }) "publish matches"
  return { results, articles := parts.foldl (fun n p => n + p.articles) 0
           matched := parts.foldl (fun n p => n + p.matched) 0 }
}

end Wiki
