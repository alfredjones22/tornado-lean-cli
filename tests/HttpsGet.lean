import Tornado.Runtime.HttpTransport

open Tornado.Runtime.HttpTransport

private def failed (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ => return true

private def ensure (condition : Bool) (description : String) : IO Unit :=
  unless condition do throw <| IO.userError description

def main (args : List String) : IO Unit := do
  let some mode := args[0]?
    | throw <| IO.userError "Expected unsafe or positive mode"
  let some base := args[1]?
    | throw <| IO.userError "Expected local HTTPS URL"
  if mode == "unsafe" then
    ensure (← failed (getHttps "http://127.0.0.2:1" 100 false))
      "Non-explicit HTTP loopback was accepted"
    ensure (← failed (getHttps "https://user:password@example.com" 100 false))
      "Embedded credentials were accepted"
    ensure (← failed (getHttps "https://example.com/#fragment" 100 false))
      "URL fragment was accepted"
    ensure (← failed (getHttps base 0 false))
      "Zero response bound was accepted"
    ensure (← failed (getHttps base (32 * 1024 * 1024 + 1) false))
      "Oversized response bound was accepted"
    ensure (← failed (getHttps (base ++ "/index") 100 false))
      "Untrusted local TLS certificate was accepted"
    IO.println "HTTPS GET: 6 unsafe endpoint, bound, and TLS checks passed"
  else if mode == "positive" then
    let index ← getSagaIndex (base ++ "/index")
    ensure (index == "{\"version\":2}".toUTF8) "Index bytes changed"
    let chunk ← getSagaChunk (base ++ "/chunk") false
    ensure (chunk == "{\"blockNumber\":\"0x1\"}\n".toUTF8)
      "HTTP Content-Encoding gzip was not decoded"
    let hot ← getSagaChunk (base ++ "/hot") true
    ensure (hot[0]? == some 0x1f && hot[1]? == some 0x8b)
      "Raw gzip asset was unexpectedly decoded"
    ensure (← failed (getHttps (base ++ "/oversize") 4 false))
      "Oversized response was accepted"
    ensure (← failed (getHttps (base ++ "/redirect") 100 false))
      "HTTP redirect was followed or accepted"
    ensure (← failed (getHttps (base ++ "/missing") 100 false))
      "HTTP 404 was accepted"
    let empty ← getHttps (base ++ "/empty") 100 false
    ensure (empty.size == 0) "Empty GET body was rejected"
    IO.println "HTTPS GET: 7 bounded, encoding, cache, redirect, and status checks passed"
  else if mode == "manual" then
    let bytes ← getHttps base (1024 * 1024) false
    ensure (bytes.size > 0) "Manual HTTPS GET returned an empty body"
    IO.println s!"HTTPS GET: trusted endpoint returned {bytes.size} bytes"
  else
    throw <| IO.userError "Expected unsafe, positive, or manual mode"
