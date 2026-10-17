import Lean
namespace Wiki.Native

@[extern "wiki_normalize"]
opaque normalize (input directory : @& String) (compressed first last : Bool)
  (namespaceId : UInt32) (redirects : Bool) (shardBytes : UInt64) : IO (Array Nat)
@[extern "wiki_decompress"]
opaque decompress (input output : @& String) : IO Unit
private opaque MatcherType : NonemptyType
def Matcher := MatcherType.type
instance : Nonempty Matcher := MatcherType.property
@[extern "wiki_matcher"]
opaque matcher (pattern : @& String) (regex ignoreCase : Bool) : IO Matcher
@[extern "wiki_find"]
opaque find (matcher : @& Matcher) (text : @& String) : IO (Option (Nat × Nat))

end Wiki.Native
