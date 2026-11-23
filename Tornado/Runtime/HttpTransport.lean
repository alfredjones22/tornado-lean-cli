import Lean
import Tornado.Runtime.JsonRpc

/-!
This module crosses the bounded HTTPS OS boundary. The two `extern` functions
are implemented in `native/tornado_https.c`: authenticated TLS (or explicit
loopback HTTP for local development), no redirects,
ambient proxies or HTTP auth. POST is bounded to one MiB in both directions;
GET has a caller-chosen bound capped at 32 MiB by C. The Lean caller owns
JSON-RPC method choice, request encoding, response validation, and Saga digest
and event checks.
-/

namespace Tornado.Runtime.HttpTransport

open Lean

/-- The native transport performs full URL and socket validation. This
shared admission guard also lets protected journals retain local development
RPCs without allowing remote plaintext endpoints. -/
def validRpcUrl (url : String) : Bool := Id.run do
  if url.isEmpty || url.utf8ByteSize > 4096 || url.contains '#' ||
      url.contains '\\' || url.toList.any (fun c => c.toNat <= 32 || c.toNat == 127) then
    return false
  let lower := url.toLower
  let secure := lower.startsWith "https://"
  if !secure && !lower.startsWith "http://" then return false
  let rest := String.ofList (url.toList.drop (if secure then 8 else 7))
  let authority := String.ofList (rest.toList.takeWhile (fun c => c != '/' && c != '?'))
  if authority.isEmpty || authority.contains '@' then return false
  if secure then return true
  if url.toList.any (fun c => c.toNat >= 127) then return false
  let authority := authority.toLower
  let candidates := ["127.0.0.1", "localhost", "[::1]"]
  for host in candidates do
    if authority == host then return true
    if authority.startsWith (host ++ ":") then
      let portText := String.ofList (authority.toList.drop (host.length + 1))
      if let some port := portText.toNat? then
        if port > 0 && port <= 65535 && toString port == portText then return true
  return false

@[extern "tornado_https_post"]
opaque postHttps (url : @& String) (body : @& ByteArray) : IO ByteArray

/-- Bounded public asset fetch. HTTP Content-Encoding is decoded by libcurl;
    a gzip file without that transport header stays compressed. The caller
    must still authenticate content and validate format before use. -/
@[extern "tornado_https_get"]
opaque getHttps (url : @& String) (maxBytes : UInt32) (noCache : Bool) : IO ByteArray

def getSagaIndex (url : String) : IO ByteArray :=
  getHttps url (2 * 1024 * 1024) true

def getSagaChunk (url : String) (hotHead : Bool) : IO ByteArray :=
  getHttps url (32 * 1024 * 1024) hotHead

def call (url : String) (id : Nat) (method : JsonRpc.Method)
    (params : Array Json) : IO Json := do
  let request ← match JsonRpc.encodeRequest id method params with
    | .ok value => pure value
    | .error message => throw <| IO.userError message
  let response ← postHttps url request.toUTF8
  let some raw := String.fromUTF8? response
    | throw <| IO.userError "HTTPS response is not UTF-8"
  match JsonRpc.parseResult id raw with
  | .ok value => return value
  | .error message => throw <| IO.userError message

def callReply (url : String) (id : Nat) (method : JsonRpc.Method)
    (params : Array Json) : IO JsonRpc.Reply := do
  if !validRpcUrl url then throw <| IO.userError "Invalid RPC endpoint."
  let request ← match JsonRpc.encodeRequest id method params with
    | .ok value => pure value
    | .error _ => throw <| IO.userError "Invalid RPC request."
  let response ← postHttps url request.toUTF8
  let some raw := String.fromUTF8? response
    | throw <| IO.userError "Invalid RPC response encoding."
  match JsonRpc.parseReply id raw with
  | .ok reply => return reply
  | .error _ => throw <| IO.userError "Invalid RPC response envelope."

end Tornado.Runtime.HttpTransport
