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
  let body := "{}".toUTF8
  if args[0]? == some "loopback" then
    let [_, ipv4, localName, ipv6] := args
      | throw <| IO.userError "Expected IPv4, localhost and IPv6 fixture origins"
    for base in [ipv4, localName, ipv6] do
      let response ← postHttps (base ++ "/rpc?mode=loopback") body
      ensure (response == "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":\"0x1\"}".toUTF8)
        "Loopback HTTP POST bytes changed"
      let response ← getHttps (base ++ "/get") 100 true
      ensure (response == "loopback get".toUTF8) "Loopback HTTP GET bytes changed"
      ensure (← failed (postHttps (base ++ "/redirect") body)) "Loopback POST redirect was accepted"
      ensure (← failed (getHttps (base ++ "/redirect") 100 false)) "Loopback GET redirect was accepted"
      ensure (← failed (postHttps (base ++ "/bad-status") body)) "Loopback HTTP 500 was accepted"
      ensure (← failed (postHttps (base ++ "/oversize-response") body)) "Loopback POST response bound was bypassed"
      ensure (← failed (getHttps (base ++ "/oversize") 4 false)) "Loopback GET response bound was bypassed"
      ensure ((← getHttps (base ++ "/empty") 10 false).isEmpty) "Empty loopback GET was rejected"
    ensure (← failed (postHttps (ipv4 ++ "/rpc#fragment") body)) "Loopback fragment was accepted"
    let credentialed := ipv4.replace "http://" "http://user:password@"
    ensure (← failed (postHttps (credentialed ++ "/rpc") body)) "Loopback credentials were accepted"
    for alternate in ["127.1", "2130706433", "0177.0.0.1", "%31%32%37.0.0.1"] do
      let alias := ipv4.replace "127.0.0.1" alternate
      ensure (← failed (postHttps (alias ++ "/rpc") body)) "Alternate numeric loopback spelling was accepted"
    ensure (← failed (postHttps (ipv4 ++ "/rpc")
      (ByteArray.mk (Array.replicate 1048577 0)))) "Loopback request bound was bypassed"
    IO.println "Loopback HTTP: IPv4, localhost, IPv6, bounds, redirect, proxy and unsafe URL checks passed"
    return
  ensure (← failed (postHttps "http://127.0.0.2:1" body)) "Non-explicit HTTP loopback was accepted"
  ensure (← failed (postHttps "https://user:password@example.com" body))
    "Endpoint with credentials was accepted"
  ensure (← failed (postHttps "https://example.com/#fragment" body))
    "Endpoint with a fragment was accepted"
  ensure (← failed (postHttps "https://example.com" (ByteArray.mk (Array.replicate 1048577 0))))
    "Oversized request was accepted"
  if let some selfSignedUrl := args[0]? then
    ensure (← failed (postHttps selfSignedUrl body)) "Self-signed TLS certificate was accepted"
  IO.println "HTTPS transport: 5 unsafe endpoint and TLS rejection checks passed"
