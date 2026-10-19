import Wiki.Analysis
import LeanCloudReducers
import LeanCloud.Source

namespace Wiki
open LeanCloud LeanReducers

structure Backend (m : Type → Type) where
  source : FileRef → m Source
  parts : PrepareRequest → Array Part → ReducerCloudM m Shard
  publish : Dataset → m FileRef
  dataset : FileRef → m Dataset
  articles : Dataset → ReducerCloudM m (String × Article)
  saveCounts : CountPartial → m FileRef
  sumCounts : CountRequest → Dataset → Array FileRef → m Counts
  validateGrep : GrepRequest → m Unit
  search : GrepRequest → Dataset → ReducerCloudM m (String × Matches)
  publishMatches : GrepRequest → Dataset → Array (String × Matches) → m FileRef

def prepare [Monad m] [MonadCloudExec m] (b : Backend m) (r : PrepareRequest) : Cloud m Prepared := cloud {
  match r.validate with | .error e => Cloud.fail e | .ok () => pure ()
  let source ← Cloud.exec (fun _ => b.source r.source) "read dump manifest"
  let shards ← (b.parts r source.parts).toArray { label := "prepare articles" }
  let dataset ← Cloud.exec (fun _ => b.publish {
    label := source.label, source := r.source, namespaceId := r.namespaceId
    includeRedirects := r.includeRedirects, shards }) "publish dataset"
  return { dataset, shards := shards.size
           articles := shards.foldl (fun n s => n + s.articles) 0 }
}

def count [Monad m] [MonadCloudExec m] (b : Backend m) (r : CountRequest) : Cloud m Counts := cloud {
  match r.validate with | .error e => Cloud.fail e | .ok () => pure ()
  let dataset ← Cloud.exec (fun _ => b.dataset r.dataset) "read dataset"
  let parts ← (b.articles dataset).foldPartitions (countFold r)
    (fun _ counts => b.saveCounts counts) { label := "count vocabulary" }
  Cloud.exec (fun _ => b.sumCounts r dataset parts) "combine counts"
}

def grep [Monad m] [MonadCloudExec m] (b : Backend m) (r : GrepRequest) : Cloud m GrepReport := cloud {
  match r.validate with | .error e => Cloud.fail e | .ok () => pure ()
  let dataset ← Cloud.exec (fun _ => b.dataset r.dataset) "read dataset"
  Cloud.exec (fun _ => b.validateGrep r) "validate search pattern"
  let parts ← (b.search r dataset).toArray { label := "search articles" }
  let results ← Cloud.exec (fun _ => b.publishMatches r dataset parts) "publish search"
  return { results, articles := parts.foldl (fun n p => n + p.2.articles) 0
           matched := parts.foldl (fun n p => n + p.2.matched) 0 }
}

end Wiki
