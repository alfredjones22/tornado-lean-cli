import Tornado.Runtime.JsonRpc
import Tornado.Runtime.HttpTransport

open Lean Tornado.Runtime.JsonRpc

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def check : Except String Unit := do
  let request ← encodeRequest 7 .chainId #[]
  let requestJson ← Json.parse request
  require ((← (← requestJson.getObjVal? "method").getStr?) == "eth_chainId")
    "Typed method name changed."
  require ((← (← requestJson.getObjVal? "id").getNat?) == 7)
    "Request ID changed."
  require ((encodeRequest 9007199254740992 .chainId #[]).isOk == false)
    "Unsafe numeric request ID was accepted."
  let success := "{\"jsonrpc\":\"2.0\",\"id\":7,\"result\":\"0x1\"}"
  require ((← parseQuantityResult 7 success) == 1) "Canonical chain ID was rejected."
  require ((parseResult 8 success).isOk == false) "Mismatched response ID was accepted."
  require ((parseResult 7 "{\"jsonrpc\":\"1.0\",\"id\":7,\"result\":1}").isOk == false)
    "Wrong JSON-RPC version was accepted."
  require ((parseResult 7 "{\"jsonrpc\":\"2.0\",\"id\":7,\"result\":1,\"error\":{\"code\":-1,\"message\":\"bad\"}}").isOk == false)
    "Result/error collision was accepted."
  require ((parseResult 7 "{\"jsonrpc\":\"2.0\",\"id\":7,\"error\":{\"code\":-1,\"message\":\"bad\"}}").isOk == false)
    "Remote error was accepted as a result."
  require ((parseResult 7 "{\"jsonrpc\":\"2.0\",\"id\":7}").isOk == false)
    "Missing result was accepted."
  for invalid in ["0x", "0x00", "0x01", "0X1", "0xA", "0xg", "1", "-0x1"] do
    require ((parseHexQuantity invalid).isOk == false)
      s!"Noncanonical RPC quantity {invalid} was accepted."
  require ((← parseHexQuantity "0x0") == 0) "Zero quantity was rejected."
  require ((← parseHexQuantity ("0x" ++ String.ofList (List.replicate 64 'f'))) ==
      2 ^ 256 - 1) "Maximum uint256 quantity was rejected."
  require ((parseHexQuantity ("0x" ++ String.ofList (List.replicate 65 'f'))).isOk == false)
    "Oversized RPC quantity was accepted."

def main : IO UInt32 := do
  for url in ["http://127.0.0.1:8545", "http://localhost:3000/rpc", "http://[::1]:8545",
      "HTTP://LOCALHOST:8545", "https://ethereum.publicnode.com"] do
    unless Tornado.Runtime.HttpTransport.validRpcUrl url do
      throw <| IO.userError "Supported RPC endpoint was rejected."
  for url in ["http://example.com/rpc", "http://127.1:8545", "http://127.0.0.1:0",
      "http://localhost:08545", "http://user@localhost", "http://localhost/#x"] do
    if Tornado.Runtime.HttpTransport.validRpcUrl url then
      throw <| IO.userError "Unsafe RPC endpoint was accepted."
  match check with
  | .error error =>
    IO.eprintln error
    return 1
  | .ok _ =>
    IO.println "PASS: typed JSON-RPC requests, ID-bound responses, and canonical quantities"
    return 0
