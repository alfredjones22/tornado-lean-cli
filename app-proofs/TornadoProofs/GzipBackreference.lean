import Tornado.Compression.Gzip

open Lean Elab Term Meta
elab "gzipPrivate" name:ident : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `Tornado.Compression.Gzip name.getId)
elab "unfoldGzipMatch" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic1 fun goal => goal.deltaTarget (· ==
    mkPrivateNameCore `Tornado.Compression.Gzip `Tornado.Compression.Gzip.appendMatch)

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TornadoProofs.GzipBackreference
abbrev Decoder : Type := gzipPrivate Tornado.Compression.Gzip.Decoder
abbrev output (state : Decoder) : ByteArray := (gzipPrivate Tornado.Compression.Gzip.Decoder.output) state
abbrev outputLimit (state : Decoder) : Nat := (gzipPrivate Tornado.Compression.Gzip.Decoder.outputLimit) state
abbrev withOutput (state : Decoder) (bytes : ByteArray) : Decoder :=
  (gzipPrivate Tornado.Compression.Gzip.Decoder.mk)
    ((gzipPrivate Tornado.Compression.Gzip.Decoder.input) state)
    ((gzipPrivate Tornado.Compression.Gzip.Decoder.bitPos) state)
    ((gzipPrivate Tornado.Compression.Gzip.Decoder.trailer) state) bytes (outputLimit state)

/-- Exact original decoder code before the buffer ownership change. -/
def original (length distance : Nat) : StateT Decoder (Except String) Unit := do
  let state ← get
  if distance == 0 || distance > (output state).size ||
      length > outputLimit state - (output state).size then
    throw "Invalid or oversized DEFLATE backreference."
  let mut bytes := output state
  for _ in [0:length] do
    bytes := bytes.push bytes[bytes.size - distance]!
  set (withOutput state bytes)

theorem withOutput_overwrite (state : Decoder) (first second : ByteArray) :
    withOutput (withOutput state first) second = withOutput state second := by rfl

theorem appendMatch_same_state (length distance : Nat) (state : Decoder) :
    (gzipPrivate Tornado.Compression.Gzip.appendMatch) length distance state =
      original length distance state := by
  unfoldGzipMatch
  unfold original
  simp only [pure_bind, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  simp only [Bind.bind, StateT.bind, get, getThe, set, modifyGet, modify,
    MonadState.get, MonadStateOf.get, MonadStateOf.set, MonadState.modifyGet, MonadStateOf.modifyGet,
    StateT.get, pure,
    Except.pure, Except.bind, withOutput, output, outputLimit]
  split <;> rfl

end TornadoProofs.GzipBackreference
#print axioms TornadoProofs.GzipBackreference.withOutput_overwrite
#print axioms TornadoProofs.GzipBackreference.appendMatch_same_state
