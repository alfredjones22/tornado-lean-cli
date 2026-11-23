import { createHash, randomUUID } from 'node:crypto'
import { spawnSync } from 'node:child_process'
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs'
import { resolve, relative } from 'node:path'
import { fileURLToPath } from 'node:url'
import { tmpdir } from 'node:os'
import { gunzipSync } from 'node:zlib'

// Fresh, local validation of the native Lean subset. A successful verdict is
// deliberately narrower than whole-CLI correctness or money-moving parity.
const root = fileURLToPath(new URL('../', import.meta.url))
const path = value => resolve(root, value)
const read = value => readFileSync(path(value), 'utf8')
const sha256 = value => createHash('sha256').update(value).digest('hex')
const requireCheck = (condition, message) => { if (!condition) throw new Error(message) }
const toolchain = 'leanprover/lean4:v4.29.1'
const commit = 'f72c35b3f637c8c6571d353742168ab66cc22c00'
const runId = randomUUID()
const startedAtUTC = new Date().toISOString()
const reportPath = path('reports/verify.json')
const env = { ...process.env, LEAN_TOOLCHAIN: toolchain, TORNADO_VERIFY_RUN_ID: runId,
  NO_COLOR: '1', CI: '1', TZ: 'UTC' }
delete env.TORNADO_RPC_URL
delete env.TORNADO_BUNDLER_URL
mkdirSync(path('reports'), { recursive: true })
rmSync(reportPath, { force: true })
writeFileSync(reportPath, JSON.stringify({ schemaVersion: 1, runId, startedAtUTC, status: 'RUNNING' }, null, 2) + '\n')

function run(command, args, timeout = 180000) {
  const result = spawnSync(command, args, { cwd: root, env, encoding: 'utf8', timeout,
    maxBuffer: 8 * 1024 * 1024 })
  if (result.error) throw result.error
  requireCheck(result.signal === null, `${command} ${args.join(' ')} terminated by ${result.signal}`)
  requireCheck(result.status === 0, `${command} ${args.join(' ')} failed:\n${(result.stderr + result.stdout).slice(-5000)}`)
  return result.stdout + result.stderr
}

function sourceFiles() {
  const found = []
  function visit(dir) {
    for (const entry of readdirSync(path(dir), { withFileTypes: true })) {
      const name = dir === '.' ? entry.name : `${dir}/${entry.name}`
      if (entry.isSymbolicLink()) throw new Error(`Unexpected source symlink: ${name}`)
      if (entry.isDirectory()) {
        if (!['.lake', 'reports', 'node_modules', '.git'].includes(entry.name)) visit(name)
      } else if (entry.isFile() && name.endsWith('.lean')) found.push(name)
    }
  }
  visit('.')
  return found.sort()
}

function vendoredSecpFiles() {
  const vendor = 'native/vendor/libsecp256k1'
  const found = ['COPYING', 'README.md', 'CHANGELOG.md']
  function visit(dir) {
    for (const entry of readdirSync(path(`${vendor}/${dir}`), { withFileTypes: true })) {
      const name = `${dir}/${entry.name}`
      if (entry.isDirectory()) visit(name)
      else if (entry.isFile()) found.push(name)
      else throw new Error(`Unexpected vendored secp256k1 entry: ${name}`)
    }
  }
  visit('include')
  visit('src')
  visit('contrib')
  return found.sort().map(name => `${vendor}/${name}`)
}

function codeWithoutComments(source) {
  let out = ''
  let depth = 0
  let lineComment = false
  let inString = false
  let escaped = false
  for (let i = 0; i < source.length; i++) {
    const here = source[i]
    const next = source[i + 1]
    if (lineComment) {
      if (here === '\n') { lineComment = false; out += '\n' } else out += ' '
    } else if (depth) {
      if (here === '/' && next === '-') { depth++; out += '  '; i++ }
      else if (here === '-' && next === '/') { depth--; out += '  '; i++ }
      else out += here === '\n' ? '\n' : ' '
    } else if (inString) {
      if (escaped) escaped = false
      else if (here === '\\') escaped = true
      else if (here === '"') inString = false
      out += here
    } else if (here === '-' && next === '-') { lineComment = true; out += '  '; i++ }
    else if (here === '/' && next === '-') { depth = 1; out += '  '; i++ }
    else if (here === '"') { inString = true; out += here }
    else out += here
  }
  requireCheck(depth === 0 && !inString, 'Unclosed comment or string in Lean source')
  return out
}

function codeWithoutStringBodies(source) {
  let out = ''
  let inString = false
  let escaped = false
  for (const here of source) {
    if (inString) {
      if (escaped) escaped = false
      else if (here === '\\') escaped = true
      else if (here === '"') inString = false
      out += here === '\n' ? '\n' : ' '
    } else if (here === '"') { inString = true; out += ' ' }
    else out += here
  }
  requireCheck(!inString, 'Unclosed Lean string literal')
  return out
}

function theoremInventory(file, source) {
  const namespaces = []
  const declarations = []
  const prints = []
  for (const line of source.split('\n')) {
    const namespace = /^\s*namespace\s+([A-Za-z_][\w.]*)\s*$/.exec(line)
    if (namespace) { namespaces.push(namespace[1]); continue }
    const end = /^\s*end(?:\s+[A-Za-z_][\w.]*)?\s*$/.exec(line)
    if (end && namespaces.length) { namespaces.pop(); continue }
    const theorem = /^\s*(?:private\s+)?theorem\s+([A-Za-z_][\w']*)\b/.exec(line)
    if (theorem) declarations.push([...namespaces, theorem[1]].join('.'))
    const printed = /^\s*#print axioms\s+([A-Za-z_][\w.]*)\s*$/.exec(line)
    if (printed) prints.push(printed[1])
  }
  requireCheck(new Set(declarations).size === declarations.length,
    `Duplicate theorem name in ${file}`)
  requireCheck((source.match(/\btheorem\b/g) ?? []).length === declarations.length &&
    !/\blemma\b/.test(source) &&
    (file.startsWith('tests/') || !/\bexample\b/.test(source)),
    `Unsupported or uninspected theorem form in ${file}`)
  requireCheck(new Set(prints).size === prints.length,
    `Duplicate #print axioms in ${file}`)
  requireCheck(JSON.stringify(declarations.slice().sort()) === JSON.stringify(prints.slice().sort()),
    `Every theorem in ${file} must have one matching #print axioms`)
  return declarations
}

function parseAxiomOutput(output, names, file) {
  const pattern = /'([^']+)' (does not depend on any axioms|depends on axioms: \[([\s\S]*?)\])/g
  const matches = [...output.matchAll(pattern)]
  requireCheck(matches.length === names.length && output.replace(pattern, '').trim() === '',
    `Unexpected Lean proof output in ${file}: ${output.slice(-1500)}`)
  const allowed = new Set(['propext', 'Classical.choice', 'Quot.sound'])
  const rows = new Map()
  for (const match of matches) {
    const printedName = match[1]
    const privateMatches = names.filter(name => printedName.startsWith('_private.') &&
      printedName.endsWith(`.${name}`))
    const name = names.includes(printedName) ? printedName :
      (privateMatches.length === 1 ? privateMatches[0] : undefined)
    requireCheck(name && names.includes(name) && !rows.has(name),
      `Unexpected or duplicate axiom report in ${file}: ${match[0]}`)
    if (match[2] === 'does not depend on any axioms') {
      rows.set(name, { theorem: name, axioms: [] }); continue
    }
    const axioms = match[3].split(',').map(value => value.trim()).filter(Boolean)
    requireCheck(axioms.length > 0 && axioms.every(value => allowed.has(value)),
      `Unapproved axiom dependency in ${name}: ${axioms.join(', ')}`)
    rows.set(name, { theorem: name, axioms })
  }
  requireCheck(rows.size === names.length, `Missing axiom report in ${file}`)
  return names.map(name => rows.get(name))
}

const requiredCryptoTests = {
  'Tornado/Crypto/BIP32Tests.lean': 'BIP32 Tornado signing path: 10 compatibility and rejection checks passed',
  'Tornado/Crypto/BIP39Tests.lean': 'BIP39 English: 12 compatibility and rejection checks passed',
  'Tornado/Crypto/KeccakTests.lean': 'Keccak-256: 11 compatibility vectors passed',
  'Tornado/Crypto/SHA256Tests.lean': 'SHA-256/HMAC-SHA256: 14 compatibility vectors passed',
  'Tornado/Crypto/SHA512Tests.lean': 'SHA-512/HMAC-SHA512: 14 compatibility vectors passed',
  'Tornado/Crypto/Secp256k1Tests.lean': 'secp256k1 deterministic signatures: 11 compatibility and rejection checks passed',
  'Tornado/Crypto/TornadoSignatureTests.lean': 'Tornado EIP-712 seeded notes: 13 pinned SDK/viem compatibility checks passed',
  'Tornado/Crypto/Blake256Tests.lean': 'BLAKE-256: 16 compatibility vectors passed',
  'Tornado/Crypto/MiMCTests.lean': 'MiMC sponge: 21 compatibility checks passed',
  'Tornado/Crypto/MiMCTreeTests.lean': 'MiMC Merkle: 14 root, path, and rejection checks passed',
  'Tornado/Crypto/PedersenTests.lean': 'Pedersen/BabyJubJub: 16 compatibility vectors passed',
}
const requiredOtherModuleTests = {
  'Tornado/Protocol/SagaHistoryTests.lean': 'Saga history: 34 offline fixture assertions passed',
  'Tornado/Protocol/RpcHistoryTests.lean': 'RPC history: 14 offline fixture assertions passed',
}
const requiredFocusedTests = {
  'tests/BN254G1.lean': 'PASS: 14 pinned BN254 G1 scalar and addition vectors; field and point rejections',
  'tests/BN254G2.lean': 'PASS: 14 pinned BN254 G2 scalar and addition vectors; twist and field rejections',
  'tests/BN254PairingField.lean': 'PASS: three noble Fp6/Fp12 field vectors, tower relations, and inverse guards',
  'tests/BN254TatePairing.lean': 'embedded G1 on curve: true\nembedded G2 on curve: true\nPASS: three noble reduced Tate vectors, prime-order output, doubling bilinearity, malformed and non-subgroup rejection',
  'tests/ClassicVerifyingKey.lean': 'PASS: complete compiled Classic key matches pinned source fixture; malformed public signals rejected',
  'tests/HistoryReducer.lean': 'PASS: pinned SDK roots, selected-pool replay, reorg pruning, and rejection gates',
  'tests/HistorySync.lean': 'PASS: bounded live-history orchestration, Saga/RPC fallback, split, same-block claims, and fault gates',
  'tests/History.lean': 'PASS: native history and redacted compliance report, exact-block receipt evidence, privacy filter, and fault gates',
  'tests/WithdrawOne.lean': 'PASS: protected-note withdrawal review, EIP-55 recipient, opaque HMAC status path, and read-only preflight gates',
  'tests/WithdrawBatch.lean': 'PASS: protected batch review, Safe/raw ordered call hash parity, scope guards, and fail-closed account checks',
  'tests/SmartAccountRecover.lean': 'PASS: native smart-account recovery dry-run plan and fail-closed RPC guards',
  'tests/SmartAccountStatus.lean': 'PASS: recovery journal, zero-value typed transaction, receipt, inclusion, and RPC-chain checks',
  'tests/NullifierSpent.lean': 'PASS: exact-block nullifier-spent selection, ABI, and RPC checks',
  'tests/ProofBlinding.lean': 'PASS: unbiased bounded Groth16 blinding admission and injected entropy',
  'tests/ProverWorkerWire.lean': 'PASS: strict public prover worker wire and request/result binding',
  'tests/Bundler.lean': 'PASS: bounded bundler codec and estimates, durable exposure order, and ambiguous-send stop',
  'tests/DepositMultiSend.lean': 'PASS: native multi-deposit sequence, durable-before-send, exact transaction/event binding, and ambiguity stop',
  'tests/DepositBatch7702.lean': 'PASS: native Simple7702 batches, viem parity, durable delegation exposure, exact events, and ambiguity stop',
  'tests/RecoverySend.lean': 'PASS: recovery candidate binding, review revalidation, journal-before-send fault traces, and status CAS',
  'tests/ImportedAbi.lean': 'PASS: 28 pinned Safe ABI encoding/hash cases, 20 import rejections, and bounded Solidity types',
  'tests/RelayerSend.lean': 'PASS: native relayer discovery, viem registry ABI, HTTPS status, stake, fee caps, oracle deviation and quote rechecks',
  'tests/PaymasterPrepare.lean': 'PASS: dummy-only paymaster estimates, bounded refinement and fallback, fee quotes, and final proof boundary',
  'tests/WithdrawalNetwork.lean': 'PASS: structured estimation errors, bounded native fees, one-attempt simulation/send, and outage admission policy',
  'tests/SponsoredPreparation.lean': 'PASS: slow proving precedes fresh history, gas and account checks and a new review clock; failures stop before review',
  'tests/EntryPointSimulation.lean': 'PASS: viem handleOps encoding, exact signed simulation events, and malformed-result rejection',
  'tests/SmartAccountAddress.lean': 'PASS: six native CREATE2 vectors, pinned factory reconstruction, and forged RPC destination rejection',
  'tests/DepositStatus.lean': 'PASS: pinned sequential journal, exact receipt classification, and read-only rendering',
  'tests/DepositStatusCommand.lean': 'PASS: sequential and 7702 deposit status reconciliation',
  'tests/WithdrawalStatusCommand.lean': 'PASS: one-note withdrawal status confirmation, failure, pending, fallback, and wrong-evidence checks',
  'tests/RelayerWithdrawalStatus.lean': 'PASS: exact Classic relayer chain event, receipt, ambiguity, and no-job safety',
  'tests/BatchWithdrawalStatus.lean': 'PASS: batch-4337 exact receipt, all selected events, candidate and path binding, ambiguous scan',
  'tests/Gzip.lean': 'PASS: 6 native gzip/DEFLATE vectors and malformed-stream guards',
  'tests/FrFFT.lean': 'PASS: 7 pinned NQR-7 FFT cases, 32768-point roundtrip, 3 sparse H polynomials, roots, and rejections',
  'tests/Groth16MSM.lean': 'PASS: 4 MSM, 3 windowed MSM, 1 Groth16/Solidity vector, and 13 rejection checks',
  'tests/Entropy.lean': 'PASS: native Lean Unix kernel CSPRNG exact-length reads and fail-closed bounds',
  'tests/JsonRpc.lean': 'PASS: typed JSON-RPC requests, ID-bound responses, and canonical quantities',
  'tests/NoteCreation.lean': 'PASS: 3 independent SDK note vectors, 11 seeded notes, backup format, and input rejection',
  'tests/PrivateKeyInput.lean': 'PASS: byte-only private-key parsing, trim parity, and malformed-input rejection',
  'tests/Recovery.lean': 'PASS: 3 pinned smart-account recovery plans and 7 input/code guards',
  'tests/RpcReceipt.lean': 'PASS: 16 viem-formatted RPC receipt checks and 21 rejection checks',
  'tests/SetCodeValidity.lean': 'PASS: 34 EIP-7702 stateless envelope and intent checks',
  'tests/SmartAccountShow.lean': 'PASS: offline smart-account show request, response, and output checks',
  'tests/ProvingKey.lean': 'PASS: authenticated full key decoded all polynomial and query-point sections\nPASS: 12 native G1, 5 G2, and 8 sparse polynomial vectors match the pinned key',
  'tests/SpecRefinement.lean': 'PASS: concrete one-note and batch traces reach reservations and reject second sends',
  'tests/TypedTransaction.lean': 'PASS: 43 viem EIP-1559/EIP-7702 typed transaction checks and 22 rejections',
  'tests/WitnessVM.lean': 'PASS: native Circom templates produced all 28,300 R1CS slots, 36,528 signals, 28275 constraints, and four full-witness R1CS cases',
  'tests/EffectRefinement.lean': 'PASS: one-note and two-note durable-reservation/authenticated-receipt effect traces',
}
const trustedExterns = {
  'Tornado/Runtime/ProtectedIO.lean': ['tornado_private_create', 'tornado_private_read',
    'tornado_private_replace', 'tornado_private_remove_exact',
    'tornado_private_dir_check'],
  'Tornado/Runtime/HttpTransport.lean': ['tornado_https_post', 'tornado_https_get'],
  'Tornado/Runtime/NativeSigner.lean': ['tornado_secure_pubkey_from_key_file',
    'tornado_secure_sign_digest_from_key_file', 'tornado_worker_disable_core_dumps',
    'tornado_verify_public_digest'],
}
const requiredTheorems = [
  'Tornado.Crypto.empty_entropy_cannot_make_mnemonic',
  'Tornado.Crypto.empty_bip32_seed_rejected',
  'Tornado.Crypto.empty_ecdsa_key_rejected',
  'Tornado.Crypto.every_non_32_byte_ecdsa_key_rejected',
  'Tornado.Crypto.zero_chain_id_rejected',
  'Tornado.Crypto.zero_chain_id_rejected_for_every_nonce',
  'Tornado.Crypto.nonce_over_uint64_rejected',
  'Tornado.Crypto.every_nonce_over_uint64_rejected',
  'Tornado.Crypto.pool_address_over_uint160_rejected',
  'Tornado.Crypto.every_pool_address_over_uint160_rejected',
  'Tornado.Protocol.Abi.validated_call_count',
  'Tornado.Protocol.Abi.decoded_sponsor_reencodes',
  'Tornado.Protocol.Abi.byteArray_eq_of_beq',
  'Tornado.Protocol.UserOperation08.hash_ignores_signature',
  'Tornado.Protocol.UserOperation08.no_paymaster_has_empty_data',
  'Tornado.Protocol.UserOperation08.uint128_overflow_rejected',
  'Tornado.Protocol.UserOperation08.hash_ignores_paymaster_signature_bytes',
  'Tornado.Protocol.Rlp.zero_chain_id_rejected',
  'Tornado.Protocol.Rlp.authorization_address_bound',
  'Tornado.Protocol.Rlp.rlp_zero',
  'Tornado.Protocol.Groth16R1CS.evaluated_row_has_valid_indices',
  'Tornado.Protocol.Groth16R1CS.checked_constraint_satisfies',
  'Tornado.Protocol.Groth16Key.decoded_header_has_valid_layout',
  'Tornado.Protocol.TornadoWitness.inputPrefix_size',
  'Tornado.Protocol.TornadoWitness.inputPrefix_public_root',
  'Tornado.Protocol.TornadoWitness.inputPrefix_nullifier_hash',
  'Tornado.Protocol.TornadoWitness.inputPrefix_private_nullifier',
  'Tornado.Protocol.Events.matchesWithdrawal_sound',
  'Tornado.Protocol.Events.direct_confirmation_requires_exact_events',
  'Tornado.Protocol.Events.batch_confirmation_requires_all_events',
  'Tornado.Protocol.Events.batch_deposit_confirmation_requires_all_events',
  'Tornado.Domain.catalog_has_29_pools', 'Tornado.Domain.catalog_all_amounts_positive',
  'Tornado.Domain.catalog_mainnet_count', 'Tornado.Domain.catalog_sepolia_count',
  'Tornado.Domain.catalog_address_unique', 'Tornado.Domain.validatePlan_sound',
  'Tornado.Domain.validatePlan_value',
  'Tornado.Domain.validatePlan_note_count',
  'Tornado.Domain.validatePlan_batch_count',
  'Tornado.Domain.validatePlan_nonempty_positive',
  'Tornado.Domain.validatePlan_entries_allowed',
  'Tornado.Domain.signedCandidateBlocksReplacement',
  'Tornado.Domain.aggregateConfirmedFirst',
  'Tornado.Policy.simulation_hash_matches',
  'Tornado.Policy.simulation_within_upper_age_bound',
  'Tornado.Policy.failed_simulation_blocks',
  'Tornado.Policy.relayer_fee_fields', 'Tornado.Policy.relayer_fee_limits',
  'Tornado.Policy.relayer_fee_conserves_amount',
  'Tornado.Policy.unknown_blocks_retry',
  'Tornado.Policy.submitted_cannot_send_again',
  'Tornado.Policy.send_requires_exposed',
  'Tornado.Policy.send_requires_matching_reservation',
  'Tornado.Policy.sign_requires_review_match',
  'Tornado.Policy.reservation_binds_reviewed_signature',
  'Tornado.Policy.exposure_requires_matching_reservation',
  'Tornado.Policy.confirmation_requires_exact_evidence',
  'Tornado.Policy.Batch.prepare_requires_valid_selection',
  'Tornado.Policy.Batch.sign_binds_reviewed_hash',
  'Tornado.Policy.Batch.reserve_requires_selected_new_note',
  'Tornado.Policy.Batch.exposure_requires_all_reserved',
  'Tornado.Policy.Batch.send_requires_all_reserved',
  'Tornado.Policy.Batch.send_requires_first_exposure',
  'Tornado.Policy.Batch.exposed_cannot_resign',
  'Tornado.Policy.Batch.unknown_blocks_retry',
  'Tornado.Policy.Batch.confirmation_requires_chain_success',
  'Tornado.Policy.Batch.confirmation_requires_exact_note_events',
  'Tornado.Policy.EvidenceBridge.confirmDirect_sound',
  'Tornado.Policy.EvidenceBridge.confirmBatch_sound',
  'Tornado.SmartAccount.encoded_calls_match_sound',
  'Tornado.Protocol.WitnessVM.generateCheckedWitness_passes',
  'Tornado.Protocol.SetCodeValidity.accepted_envelope_covers_intrinsic_gas',
  'Tornado.Protocol.SetCodeValidity.accepted_intent_auth_nonce_is_processable',
  'Tornado.Protocol.RpcReceipt.direct_confirmation_binds_transaction',
  'Tornado.Protocol.RpcReceipt.batch_confirmation_binds_transaction',
  'Tornado.Spec.direct_exposure_refines_spec',
  'Tornado.Spec.batch_exposure_refines_spec',
  'Tornado.Spec.Effects.run_exposure_has_prior_reservation',
  'Tornado.Spec.Effects.Batch.run_exposure_has_all_prior_reservations',
  'Tornado.Spec.Effects.Batch.confirmation_requires_authenticated_evidence',
  'Tornado.Protocol.BN254G1.fp_ofNat_bounded',
  'Tornado.Protocol.BN254G1.fp_add_bounded',
  'Tornado.Protocol.BN254G1.fp_mul_bounded',
  'Tornado.Protocol.BN254G1.fp_inverse_sound',
  'Tornado.Protocol.BN254PairingField.fp6_inverse_sound',
  'Tornado.Protocol.BN254PairingField.fp12_inverse_sound',
  'Tornado.Protocol.BN254TatePairing.finalExponent_divisible',
  'Tornado.Protocol.BN254TatePairing.pair_success_nonzero',
  'Tornado.Protocol.BN254TatePairing.pair_success_order',
  'Tornado.Protocol.BN254Groth16Verify.publicInputPoint_success_signals_bounded',
  'Tornado.Protocol.BN254Groth16Verify.verify_true_signals_bounded',
  'Tornado.Protocol.ClassicVerifyingKey.verifyClassic_true_uses_checked_key',
  'Tornado.Protocol.ClassicVerifyingKey.verifyClassic_true_signals_bounded',
  'Tornado.Protocol.ClassicProofPipeline.checked_artifact_has_full_witness',
  'Tornado.Protocol.ClassicProofPipeline.checked_artifact_serializes_points',
  'Tornado.Protocol.ClassicProofPipeline.checked_artifact_verifies_expected_signals',
  'Tornado.Protocol.ClassicProofPipeline.checked_artifact_signals_bounded',
  'Tornado.Protocol.ClassicProofPipeline.public_proof_binds_review',
  'Tornado.Protocol.ClassicProofPipeline.public_proof_checked_and_encoded',
  'Tornado.Protocol.ClassicProofPipeline.public_proof_verified',
  'Tornado.Protocol.ClassicProofPipeline.public_proof_signals_bounded',
  'Tornado.Runtime.AttemptJournal.advance_prepare_binds_selection',
  'Tornado.Runtime.AttemptJournal.advance_reserve_selected',
  'Tornado.Runtime.AttemptJournal.advance_direct_send_refines_policy',
  'Tornado.Runtime.AttemptJournal.advance_direct_send_requires_exposed',
  'Tornado.Runtime.AttemptJournal.advance_direct_send_consumes_slot',
  'Tornado.Runtime.AttemptJournal.advance_direct_send_no_repeat',
  'Tornado.Runtime.AttemptJournal.advance_batch_send_refines_policy',
  'Tornado.Runtime.AttemptJournal.advance_batch_send_requires_reserved',
  'Tornado.Runtime.AttemptJournal.advance_batch_send_consumes_slot',
  'Tornado.Runtime.AttemptJournal.advance_batch_send_no_repeat',
  'Tornado.Runtime.NoteClaims.fileName_injective_of_same_prefix',
  'Tornado.Runtime.NoteClaims.fileName_ne_of_ne_same_prefix',
  'Tornado.Protocol.SagaHistory.replay_never_before_registration',
  'Tornado.Protocol.SagaHistory.cursor_before_registration_replay',
  'Tornado.Protocol.HistoryReducer.appendDeposit_success_next_index',
  'Tornado.Protocol.HistoryReducer.applyBatch_success_bound',
  'Tornado.Protocol.HistoryReducer.applyBatch_success_identity',
  'Tornado.Runtime.HistorySync.acceptComplete_success_fresh',
  'Tornado.Runtime.HistorySync.withinAggregateBytes_sound',
  'Tornado.Cli.SmartAccountStatus.confirmed_requires_matching_transaction',
  'Tornado.Cli.SmartAccountStatus.confirmed_requires_matching_inclusion',
  'Tornado.Cli.NullifierSpent.accepted_selection_binds_pool',
  'Tornado.Cli.NullifierSpent.accepted_spent_is_canonical',
  'Tornado.Runtime.ProofBlinding.admitted_scalar_shape',
  'Tornado.Spec.JournalIORefinement.replay_success_metadata',
  'Tornado.Spec.JournalIORefinement.replay_direct_send_requires_reservation',
  'Tornado.Spec.JournalIORefinement.replay_batch_send_requires_all_reservations',
  'Tornado.Spec.JournalIORefinement.replay_send_no_repeat',
  'Tornado.Protocol.SagaHistory.validate_coverage_sound',
  'Tornado.Protocol.SagaHistory.validate_coverage_end',
  'Tornado.Protocol.SagaHistory.accepted_range_is_within_coverage',
  'Tornado.Protocol.SagaHistory.accepted_freshness_covers_head',
  'Tornado.Protocol.RpcHistory.request_params_sound',
  'Tornado.Protocol.ProvingKey.fpRInverse_correct',
  'Tornado.Protocol.ProvingKey.frRInverse_correct',
  'Tornado.Protocol.ProvingKey.authenticated_key_has_pinned_digest',
  'Tornado.Protocol.ProvingKey.authenticated_key_has_valid_header',
  'Tornado.Protocol.FrFFT.inverse_sound',
  'Tornado.Protocol.FrFFT.rootOfUnity_sound',
  'Tornado.Protocol.Groth16MSM.msmG1_rejects_mismatched_counts',
  'Tornado.Protocol.Groth16MSM.msmG2_rejects_mismatched_counts',
  'Tornado.Protocol.Groth16MSM.derived_points_use_checked_witness',
  'Tornado.Compression.Gzip.verifyTrailer_sound',
  'Tornado.Compression.Gzip.decompress_success_integrity',
]
const unsupportedCommands = []

let stage = 'initialization'
try {
  stage = 'toolchain'
  requireCheck(read('lean-toolchain').trim() === toolchain, 'Lean toolchain pin changed')
  const version = run('elan', ['run', toolchain, 'lean', '--version'], 10000).trim()
  requireCheck(version.startsWith('Lean (version 4.29.1,') && version.includes(`commit ${commit},`),
    `Unexpected Lean binary: ${version}`)
  const manifest = JSON.parse(read('lake-manifest.json'))
  requireCheck(manifest.name === 'tornadoLeanCli' && Array.isArray(manifest.packages) &&
    manifest.packages.length === 0, 'Lean project unexpectedly imports external Lake packages')

  stage = 'source inventory'
  const files = sourceFiles()
  requireCheck(files.includes('Main.lean') && files.includes('Tornado.lean') &&
    files.length >= 10, 'Native Lean source inventory incomplete')
  requireCheck(JSON.stringify(files.filter(file => file.startsWith('Tornado/') &&
    file.endsWith('Tests.lean'))) ===
    JSON.stringify([...Object.keys(requiredCryptoTests), ...Object.keys(requiredOtherModuleTests)].sort()),
    'A native module test was added or removed without updating the verifier')
  requireCheck(JSON.stringify(files.filter(file => /^tests\/.*\.lean$/.test(file))) ===
    JSON.stringify(['tests/Abi.lean', 'tests/BN254G1.lean', 'tests/BN254G2.lean',
      'tests/BN254PairingField.lean', 'tests/BN254TatePairing.lean',
      'tests/BN254Groth16Verify.lean',
      'tests/ClassicVerifyingKey.lean', 'tests/HistoryReducer.lean',
      'tests/HistorySync.lean', 'tests/History.lean',
      'tests/WithdrawOne.lean', 'tests/WithdrawBatch.lean',
      'tests/WithdrawProof.lean', 'tests/BatchWithdrawalStatus.lean',
      'tests/SmartAccountRecover.lean',
      'tests/ClassicProofPipelineFull.lean',
      'tests/SmartAccountStatus.lean',
      'tests/NullifierSpent.lean',
      'tests/ProofBlinding.lean', 'tests/ProverWorkerWire.lean',
      'tests/ProverWorkerClient.lean', 'tests/ProverWorker.lean',
      'tests/Bundler.lean', 'tests/DepositMultiSend.lean', 'tests/DepositBatch7702.lean',
      'tests/RecoverySend.lean', 'tests/ImportedAbi.lean', 'tests/RelayerSend.lean',
      'tests/PaymasterPrepare.lean', 'tests/HistorySnapshot.lean',
      'tests/WithdrawalNetwork.lean', 'tests/SponsoredPreparation.lean',
      'tests/WithdrawalJournal.lean', 'tests/RelayerSubmit.lean',
      'tests/EntryPointSimulation.lean', 'tests/ProverWorkerMetadata.lean',
      'tests/SmartAccountAddress.lean',
      'tests/JournalIORefinement.lean',
      'tests/DepositStatus.lean', 'tests/DepositStatusCommand.lean',
      'tests/DepositSend.lean', 'tests/DepositMulti.lean', 'tests/NativeSigner.lean',
      'tests/WithdrawalStatusCommand.lean', 'tests/RelayerWithdrawalStatus.lean',
      'tests/Gzip.lean',
      'tests/FrFFT.lean',
      'tests/Groth16MSM.lean',
      'tests/Groth16MSMFull.lean',
      'tests/HttpsGet.lean',
      'tests/BatchPolicy.lean', 'tests/Events.lean',
      'tests/EffectRefinement.lean', 'tests/Entropy.lean', 'tests/EvidenceBridge.lean',
      'tests/Groth16Key.lean', 'tests/Groth16R1CS.lean',
      'tests/Invoices.lean', 'tests/JsonRpc.lean', 'tests/NoteCreation.lean',
      'tests/PrivateKeyInput.lean',
      'tests/NoteClaims.lean',
      'tests/NotesParsing.lean', 'tests/OneNotePolicy.lean',
      'tests/PlanChoices.lean', 'tests/PlanGrid.lean', 'tests/Rlp.lean', 'tests/StatusParity.lean',
      'tests/StatusRules.lean', 'tests/TornadoWitness.lean', 'tests/UserOperation08.lean',
      'tests/Recovery.lean', 'tests/RpcReceipt.lean', 'tests/SetCodeValidity.lean',
      'tests/ProvingKey.lean',
      'tests/ProtectedIO.lean', 'tests/ProtectedReplace.lean',
      'tests/SelectedPoolBootstrap.lean',
      'tests/HttpsTransport.lean', 'tests/AttemptJournal.lean',
      'tests/SmartAccountShow.lean', 'tests/SpecRefinement.lean',
      'tests/TypedTransaction.lean', 'tests/WitnessVM.lean'].sort()),
    'A domain test was added or removed without updating the verifier')
  requireCheck(JSON.stringify(files.filter(file => /^Tests\/.*\.lean$/.test(file))) ===
    JSON.stringify([]), 'Unexpected capitalized test directory')
  requireCheck(['tests/ProtectedIO.lean', 'tests/HttpsTransport.lean',
    'tests/AttemptJournal.lean'].every(file => files.includes(file)),
    'A native executable test is missing')
  const inputHashes = {}
  const secpFiles = vendoredSecpFiles()
  const vendorRoot = 'native/vendor/libsecp256k1/'
  const secpTreeDigest = sha256(secpFiles.map(file =>
    `${file.slice(vendorRoot.length)} ${sha256(readFileSync(path(file)))}\n`).join(''))
  requireCheck(secpFiles.length === 133 &&
    secpTreeDigest === 'd13f475d1ccb943f214b5756d50773d283d5f9ab012860ab7ab4a3cf555ba135',
    'Vendored libsecp256k1 v0.8.0 source differs from the pinned archive')
  for (const file of secpFiles) inputHashes[file] = sha256(readFileSync(path(file)))
  const theoremFiles = []
  const theoremNames = []
  for (const file of files) {
    const content = read(file)
    inputHashes[file] = sha256(content)
    const uncommented = codeWithoutComments(content)
    const code = codeWithoutStringBodies(uncommented)
    const approved = trustedExterns[file] ?? []
    const declaredExterns = [...uncommented.matchAll(/@\[\s*extern\s+"([^"]+)"\s*\]\s*opaque\s+[A-Za-z_][\w']*/g)]
      .map(match => match[1])
    requireCheck(JSON.stringify(declaredExterns) === JSON.stringify(approved) &&
      (code.match(/\bextern\b/g) ?? []).length === approved.length &&
      (code.match(/\bopaque\b/g) ?? []).length === approved.length,
      `Unexpected native extern or opaque declaration in ${file}`)
    requireCheck(!/\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b/.test(code) &&
      !/^\s*#eval\b/m.test(code) &&
      !/\{[^\n{}]*\b(?:sorry|admit|axiom|opaque|unsafe|native_decide|extern|implemented_by)\b[^\n{}]*\}/.test(uncommented),
    `Untrusted proof escape or placeholder in ${file}`)
    const names = theoremInventory(file, code)
    if (names.length) { theoremFiles.push({ file, names }); theoremNames.push(...names) }
  }
  requireCheck(new Set(theoremNames).size === theoremNames.length,
    'Duplicate theorem across native Lean files')
  requireCheck(requiredTheorems.every(name => theoremNames.includes(name)),
    'A required native theorem is missing')
  for (const file of ['fixtures/parity-read-only.json', 'fixtures/parity-oracle-digests.json',
    'fixtures/plan-grid.csv', 'fixtures/plan-choices.csv', 'fixtures/seeded-note-vectors.json',
    'fixtures/status-parity.json', 'fixtures/abi-vectors.json',
    'fixtures/userop08-vectors.json', 'fixtures/rlp-vectors.json',
    'fixtures/groth16-tornado-r1cs.json', 'fixtures/groth16-key-header.json',
    'fixtures/events-vectors.json', 'fixtures/note-creation-vectors.json',
    'fixtures/recovery-vectors.json', 'fixtures/rpc-receipt-vectors.json',
    'fixtures/typed-transactions.json', 'fixtures/witness-vm-selected-components.json',
    'fixtures/proving-key-vectors.json',
    'fixtures/fr-fft-vectors.json',
    'fixtures/deposit-status-journal.json',
    'fixtures/groth16-msm-vectors.json',
    'fixtures/groth16-full-public-proof.json',
    'fixtures/groth16-relayer-public-proof.json', 'fixtures/prover-signer-public.json',
    'fixtures/gzip-vectors.json',
    'fixtures/bn254-g1-vectors.json', 'fixtures/bn254-g2-vectors.json',
    'fixtures/bn254-tower-vectors.json', 'fixtures/bn254-tate-vectors.json',
    'fixtures/tornado-classic-verifying-key.json',
    'fixtures/tornado-classic-proof-equation.json',
    'fixtures/tornado-classic-Verifier.sol',
    'fixtures/history-reducer-vectors.json',
    'fixtures/imported-abi-vectors.json', 'fixtures/classic-relayer.json',
    'fixtures/deposit7702-vectors.json', 'fixtures/simple7702-code.json',
    'fixtures/entrypoint-simulation.json',
    'fixtures/smart-account-address-vectors.json',
    'fixtures/history-snapshot/history/1/0x199112eb461ea7eec1d75b33343542e1d069b41c-306b948d71dbe716.json.gz',
    '.gitignore', 'scripts/parity.mjs', 'scripts/notes-file-parity.mjs',
    'scripts/notes-create-smoke.mjs',
    'scripts/test-protected-io.mjs', 'scripts/test-https-transport.mjs',
    'scripts/test-https-get.mjs', 'scripts/test-https-get-boundary.mjs',
    'scripts/test-loopback-http.mjs',
    'scripts/test-attempt-journal.mjs',
    'scripts/test-journal-io-refinement.mjs',
    'scripts/test-note-claims.mjs',
    'scripts/generate-bn254-g1-vectors.mjs', 'scripts/generate-bn254-g2-vectors.mjs',
    'scripts/generate-bn254-tower-vectors.mjs',
    'scripts/generate-bn254-tate-vectors.mjs',
    'scripts/check-classic-vk-provenance.mjs',
    'scripts/check-tornado-proof-equation.mjs',
    'scripts/generate-history-reducer-vectors.mjs',
    'scripts/generate-imported-abi-vectors.mjs', 'scripts/check_history_snapshots.py',
    'scripts/generate-entrypoint-simulation-vectors.mjs',
    'scripts/witness-vm-extract.mjs', 'scripts/verify.mjs',
    'scripts/proving-key-extract.mjs',
    'scripts/generate-fr-fft-vectors.mjs',
    'scripts/deposit-status-source-check.mjs',
    'scripts/generate-groth16-msm-vectors.mjs',
    'scripts/generate-full-public-proof.mjs',
    'scripts/generate-gzip-vectors.mjs',
    'native/tornado_private_io.c', 'native/tornado_private_io.h',
    'native/tornado_https.c', 'native/tornado_secret_sign.c',
    'native/vendor/libsecp256k1/UPSTREAM.md',
    'native/https_get_boundary_test.c',
    'lakefile.lean', 'lean-toolchain',
    'lake-manifest.json']) {
    requireCheck(existsSync(path(file)), `Missing verification input ${file}`)
    inputHashes[file] = sha256(readFileSync(path(file)))
  }
  const sagaFixtureEntries = readdirSync(path('fixtures/saga-history'),
    { withFileTypes: true })
  requireCheck(sagaFixtureEntries.length === 35 && sagaFixtureEntries.every(entry =>
    entry.isFile() && /^[a-z0-9.-]+\.(?:json|jsonl|jsonl\.gz)$/.test(entry.name)),
    'Native Saga fixture inventory changed')
  for (const entry of sagaFixtureEntries) {
    const file = `fixtures/saga-history/${entry.name}`
    inputHashes[file] = sha256(readFileSync(path(file)))
  }
  const provingAssets = [
    { file: 'assets/proving/tornado-3ddd61dbff09caee.json.gz',
      compressedSHA256: '22b240a07985e1f7f5e4520029b65cce0276eafd35d67080c70a3990aa892ed6',
      rawSize: 19474889,
      rawSHA256: '3ddd61dbff09caeec82d8edde95c674a3c34f9e66b1fe9f2c8783e72fe536f98' },
    { file: 'assets/proving/tornadoProvingKey-8e2d2f22beafb5a9.bin.gz',
      compressedSHA256: '806676308b1fc825a97aad47eaec0499f665a1da3f3d0a0e35f7bbf6796bcd32',
      rawSize: 14522256,
      rawSHA256: '8e2d2f22beafb5a9666daebca57b13f8029c3656c65fcfbcc86e2418fa16a3af' },
  ]
  let pinnedCircuitRaw
  let pinnedKeyRaw
  for (const asset of provingAssets) {
    requireCheck(existsSync(path(asset.file)), `Missing pinned proving asset ${asset.file}`)
    const compressed = readFileSync(path(asset.file))
    const compressedDigest = sha256(compressed)
    requireCheck(compressedDigest === asset.compressedSHA256,
      `Compressed proving asset hash changed: ${asset.file}`)
    const raw = gunzipSync(compressed)
    requireCheck(raw.length === asset.rawSize && sha256(raw) === asset.rawSHA256,
      `Decompressed proving asset differs from pinned source: ${asset.file}`)
    if (asset.file.endsWith('.json.gz')) pinnedCircuitRaw = raw
    else pinnedKeyRaw = raw
    inputHashes[asset.file] = compressedDigest
  }
  const r1csFixtureFile = 'fixtures/groth16-tornado-r1cs.json'
  const r1csFixtureSHA256 =
    '10364ef4ca2a0436435ee40d2cd1376b2dd1c5d79278e8addabcbae38b56920c'
  requireCheck(inputHashes[r1csFixtureFile] === r1csFixtureSHA256,
    'Pinned R1CS fixture digest changed')
  const pinnedCircuit = JSON.parse(pinnedCircuitRaw.toString('utf8'))
  const r1csFixture = JSON.parse(read(r1csFixtureFile))
  requireCheck(r1csFixture.sourceCircuitSha256 === provingAssets[0].rawSHA256 &&
    r1csFixture.sourceProvingKeySha256 === provingAssets[1].rawSHA256 &&
    r1csFixture.nVars === pinnedCircuit.nVars &&
    r1csFixture.nPubInputs === pinnedCircuit.nPubInputs &&
    r1csFixture.nOutputs === pinnedCircuit.nOutputs &&
    JSON.stringify(r1csFixture.constraints) === JSON.stringify(pinnedCircuit.constraints),
  'R1CS fixture does not match the decompressed pinned circuit constraints and metadata')

  stage = 'build'
  console.log('Building native Lean library and executable...')
  const moduleTargets = files.filter(file => file.startsWith('Tornado/') &&
    !file.endsWith('Tests.lean')).map(file => file.slice(0, -'.lean'.length).replaceAll('/', '.'))
  run('lake', ['build', 'Tornado', 'tornado', 'protected_io_test',
    'https_transport_test', 'https_get_test', 'attempt_journal_test',
    'journal_refinement_test', 'note_claims_test', 'protected_replace_test',
    'selected_pool_bootstrap_test', 'deposit_send_test', 'deposit_multi_test',
    'native_signer_test',
    'withdraw_proof_test', 'tornado_prover_worker', 'prover_worker_test', 'history_snapshot_test',
    'prover_worker_metadata_test', 'relayer_submit_test',
    'gzip_test', 'groth16_full_public_test',
    'classic_proof_pipeline_full_test', ...moduleTargets], 600000)
  requireCheck(existsSync(path('.lake/build/bin/tornado')), 'Native Lean executable missing after build')
  requireCheck(existsSync(path('.lake/build/bin/protected_io_test')) &&
    existsSync(path('.lake/build/bin/https_transport_test')) &&
    existsSync(path('.lake/build/bin/https_get_test')) &&
    existsSync(path('.lake/build/bin/attempt_journal_test')) &&
    existsSync(path('.lake/build/bin/journal_refinement_test')) &&
    existsSync(path('.lake/build/bin/note_claims_test')) &&
    existsSync(path('.lake/build/bin/protected_replace_test')) &&
    existsSync(path('.lake/build/bin/selected_pool_bootstrap_test')) &&
    existsSync(path('.lake/build/bin/deposit_send_test')) &&
    existsSync(path('.lake/build/bin/deposit_multi_test')) &&
    existsSync(path('.lake/build/bin/native_signer_test')) &&
    existsSync(path('.lake/build/bin/withdraw_proof_test')) &&
    existsSync(path('.lake/build/bin/tornado_prover_worker')) &&
    existsSync(path('.lake/build/bin/prover_worker_test')) &&
    existsSync(path('.lake/build/bin/history_snapshot_test')) &&
    existsSync(path('.lake/build/bin/prover_worker_metadata_test')) &&
    existsSync(path('.lake/build/bin/relayer_submit_test')) &&
    existsSync(path('.lake/build/bin/gzip_test')) &&
    existsSync(path('.lake/build/bin/groth16_full_public_test')) &&
    existsSync(path('.lake/build/bin/classic_proof_pipeline_full_test')),
    'Native OS binding test executables missing after build')

  stage = 'native OS boundary'
  requireCheck(run(process.execPath, ['scripts/test-loopback-http.mjs'], 180000).trim() ===
    'Loopback HTTP: IPv4, localhost, IPv6, bounds, redirect, proxy and unsafe URL checks passed',
    'Explicit loopback HTTP or remote-plaintext rejection changed')
  requireCheck(run('python3', ['scripts/check_history_snapshots.py']).trim() ===
    'PASS: all 29 compiled history snapshot descriptors match the pinned CLI manifest',
    'Compiled history snapshot descriptors differ from the pinned TypeScript manifest')
  const snapshotDir = mkdtempSync(path('tests/.history-snapshot-'))
  try {
    requireCheck(run(path('.lake/build/bin/history_snapshot_test'), [snapshotDir], 300000).trim() ===
      'PASS: pinned snapshot hashes, protected chunk cache, checkpoint revalidation, reorg rebuild, and stale CAS rejection',
      'Pinned history or protected snapshot cache checks changed')
  } finally { rmSync(snapshotDir, { recursive: true, force: true }) }
  const metadataDir = mkdtempSync(path('tests/.prover-metadata-'))
  try {
    requireCheck(run(path('.lake/build/bin/prover_worker_metadata_test'),
      [path('.lake/build/bin/tornado_prover_worker'), metadataDir], 180000).trim() ===
      'PASS: isolated public metadata and viem-parity ephemeral signatures, strict wire, recovery verification, and sanitized failures',
      'Isolated public note metadata or protected worker boundary changed')
  } finally { rmSync(metadataDir, { recursive: true, force: true }) }
  const relayerDir = mkdtempSync(path('tests/.relayer-submit-'))
  try {
    requireCheck(run(path('.lake/build/bin/relayer_submit_test'), [relayerDir], 180000).trim() ===
      'PASS: relayer proof binding, reserve-before-POST, single-send ambiguity, exact receipts and protected claims',
      'Relayer proof, protected claim or single-POST fault checks changed')
  } finally { rmSync(relayerDir, { recursive: true, force: true }) }
  const protectedOutput = run(process.execPath, ['scripts/test-protected-io.mjs']).trim().split('\n')
  const protectedExpected = ['Protected IO: 10 roundtrip and unsafe-path checks passed']
  if (process.platform === 'darwin')
    protectedExpected.push('Protected IO: inherited and direct ACL checks passed')
  requireCheck(JSON.stringify(protectedOutput) === JSON.stringify(protectedExpected),
    'Protected-file OS boundary test changed')
  const replacementDir = mkdtempSync(path('tests/.protected-replace-'))
  try {
    requireCheck(run(path('.lake/build/bin/protected_replace_test'), [replacementDir]).trim() ===
      'PASS: protected atomic replace, stale CAS, bounds, and lock rejection',
      'Protected journal CAS or atomic replacement changed')
  } finally { rmSync(replacementDir, { recursive: true, force: true }) }
  requireCheck(run(path('.lake/build/bin/selected_pool_bootstrap_test'), []).trim() ===
    'PASS: all 29 selected-pool bootstrap identities, deployment cursors, and mismatch rejections',
    'Selected-pool bootstrap behavior changed')
  requireCheck(run('python3', ['scripts/check_selected_pool_bootstrap.py']).trim() ===
    'PASS: clean CLI source hashes and all 29 Lean pool bootstrap rows match catalog, bootstrap, and manifest',
    'Selected-pool bootstrap differs from pinned TypeScript source')
  requireCheck(run(path('.lake/build/bin/deposit_send_test'), []).trim() ===
    'PASS: invoice planning, durable-before-send fault ordering, ambiguity stop, and exact deposit confirmation',
    'Native deposit invoice preparation or fault ordering changed')
  requireCheck(run(path('.lake/build/bin/deposit_multi_test'), []).trim() ===
    'PASS: multi-note sequential/7702 planning, approval and chunk limits, and private-backup reduction',
    'Native multi-note deposit dry-run planning changed')
  const signerDir = mkdtempSync(path('tests/.native-signer-'))
  try {
    requireCheck(run(path('.lake/build/bin/native_signer_test'), [signerDir]).trim() ===
      'PASS: protected native signer matches Lean and viem public vectors',
      'Protected native signer boundary or public-vector parity changed')
  } finally { rmSync(signerDir, { recursive: true, force: true }) }
  const secpTestDir = mkdtempSync(path('tests/.secp-upstream-'))
  try {
    const vendor = 'native/vendor/libsecp256k1'
    const upstreamTest = `${secpTestDir}/tests`
    run('/usr/bin/cc', [
      '-O2', '-std=c11', '-DENABLE_MODULE_RECOVERY=1',
      '-DCOMB_BLOCKS=43', '-DCOMB_TEETH=6', '-DECMULT_WINDOW_SIZE=15',
      '-I', path(`${vendor}/include`), '-I', path(`${vendor}/src`),
      path(`${vendor}/src/tests.c`), path(`${vendor}/src/precomputed_ecmult.c`),
      path(`${vendor}/src/precomputed_ecmult_gen.c`), '-o', upstreamTest], 180000)
    const upstreamOutput = run(upstreamTest, ['1'], 300000)
    requireCheck(upstreamOutput.includes('iterations = 1') &&
      upstreamOutput.includes('Total execution time:'),
      'Vendored libsecp256k1 upstream one-iteration test changed')
  } finally { rmSync(secpTestDir, { recursive: true, force: true }) }
  requireCheck(run(process.execPath, ['scripts/test-https-transport.mjs']).trim() ===
    'HTTPS transport: 5 unsafe endpoint and TLS rejection checks passed',
    'HTTPS OS boundary test changed')
  requireCheck(run(process.execPath, ['scripts/test-https-get-boundary.mjs']).trim() ===
    'HTTPS GET C boundary: callback, header, and URL guards passed',
    'HTTPS GET C callback boundary changed')
  const getOutput = run(process.execPath, ['scripts/test-https-get.mjs']).trim().split('\n')
  const getExpected = process.platform === 'darwin' ? [
    'HTTPS GET: 6 unsafe endpoint, bound, and TLS checks passed',
    'HTTPS GET: trusted local fetch skipped on macOS system trust'] : [
    'HTTPS GET: 6 unsafe endpoint, bound, and TLS checks passed',
    'HTTPS GET: 7 bounded, encoding, cache, redirect, and status checks passed']
  requireCheck(JSON.stringify(getOutput) === JSON.stringify(getExpected),
    'HTTPS GET OS boundary test changed')
  requireCheck(run(process.execPath, ['scripts/test-attempt-journal.mjs']).trim() ===
    'Attempt journal: durable replay, crash/retry, batch, gap and malformed-record checks passed',
    'Append-only attempt journal replay changed')
  const journalRefinementOutput = run(process.execPath,
    ['scripts/test-journal-io-refinement.mjs']).trim()
  const journalRefinementExpected = process.getuid?.() === 0
    ? 'Journal IO refinement: concurrent arm and crash replay gates passed (write failure skipped as root)'
    : 'Journal IO refinement: failed write, concurrent arm, and crash replay gates passed'
  requireCheck(journalRefinementOutput === journalRefinementExpected,
    'Concrete journal replay or exclusive-arm refinement changed')
  requireCheck(run(process.execPath, ['scripts/test-note-claims.mjs']).trim() ===
    'Note claims: private directory, replay, conflicts, orphan safety, and concurrent exclusivity passed',
    'Global note-claim replay or exclusivity changed')
  requireCheck(run(process.execPath, ['scripts/witness-vm-extract.mjs', '--check'], 600000).includes('PASS'),
    'Pinned Circom graph extraction changed')
  requireCheck(run(process.execPath, ['scripts/generate-bn254-g1-vectors.mjs', '--check']).trim() ===
    'PASS: BN254 G1 vectors match pinned noble implementation',
    'Pinned BN254 G1 vector oracle changed')
  requireCheck(run(process.execPath, ['scripts/generate-bn254-g2-vectors.mjs', '--check']).trim() ===
    'PASS: BN254 G2 vectors match pinned noble implementation',
    'Pinned BN254 G2 vector oracle changed')
  requireCheck(run(process.execPath, ['scripts/generate-bn254-tower-vectors.mjs', '--check']).trim() ===
    'PASS: three BN254 tower vectors match pinned noble',
    'Pinned BN254 extension-field oracle changed')
  requireCheck(run(process.execPath, ['scripts/generate-bn254-tate-vectors.mjs', '--check']).trim() ===
    'PASS: three reduced Tate vectors and non-subgroup point match pinned noble',
    'Pinned reduced Tate oracle changed')
  requireCheck(run(process.execPath, ['scripts/check-classic-vk-provenance.mjs']).trim() ===
    'PASS: complete Classic VK matches immutable Solidity source; proving-key alpha1, beta2, delta2 match',
    'Immutable Classic verifier key provenance changed')
  requireCheck(run(process.execPath, ['scripts/check-tornado-proof-equation.mjs', '--check']).trim() ===
    'PASS: noble accepts pinned Classic proof and rejects all six changed public signals',
    'Independent Classic Groth16 equation oracle changed')
  requireCheck(run(process.execPath, ['scripts/generate-history-reducer-vectors.mjs', '--check']).trim() ===
    'PASS: six pinned SDK MiMC pool-root vectors',
    'Pinned pool-history MiMC root oracle changed')
  requireCheck(run(process.execPath, ['scripts/proving-key-extract.mjs', '--check']).trim() ===
    'PASS: 12 G1, 5 G2, and 8 polynomial vectors match the pinned key',
    'Pinned proving-key vector oracle changed')
  requireCheck(run(process.execPath, ['scripts/generate-fr-fft-vectors.mjs', '--check']).trim() ===
    'PASS: 7 FFT and 3 H vectors match pinned noble BN254 Fr',
    'Pinned Fr FFT vector oracle changed')
  requireCheck(run(process.execPath, ['scripts/deposit-status-source-check.mjs', '--check']).trim() ===
    'PASS: pinned TypeScript sequential deposit journal fixture',
    'Pinned sequential deposit journal fixture changed')
  requireCheck(run(process.execPath, ['scripts/generate-groth16-msm-vectors.mjs', '--check']).trim() ===
    'PASS: 4 noble MSM, 3 windowed MSM, and 1 Solidity proof vector',
    'Pinned Groth16 MSM vector oracle changed')
  requireCheck(run(process.execPath, ['scripts/generate-full-public-proof.mjs', '--check'], 300000).trim() ===
    'PASS: full public Groth16 proof bytes match pinned micro-zk-proofs',
    'Pinned full public Groth16 proof oracle changed')
  requireCheck(run(process.execPath, ['scripts/generate-full-public-proof.mjs', '--relayer-check'], 300000).trim() ===
    'PASS: public Classic relayer proof bytes match pinned micro-zk-proofs and all R1CS constraints',
    'Pinned public relayer proof or complete R1CS witness changed')
  requireCheck(run(process.execPath, ['scripts/generate-gzip-vectors.mjs', '--check']).trim() ===
    'PASS: 6 gzip/DEFLATE vectors match Node zlib',
    'Pinned native gzip vector oracle changed')
  const nativeGzipOutput = run(path('.lake/build/bin/gzip_test'), [
    path('assets/proving/tornado-3ddd61dbff09caee.json.gz'),
    path('assets/proving/tornadoProvingKey-8e2d2f22beafb5a9.bin.gz')], 900000).trim()
  requireCheck(nativeGzipOutput ===
    'PASS: native Lean decompressed and authenticated both pinned proving assets\n' +
    'PASS: 6 native gzip/DEFLATE vectors and malformed-stream guards',
    'Native Lean did not authenticate both pinned gzip assets')

  stage = 'proof certificates'
  const proofs = []
  for (const { file, names } of theoremFiles) {
    const output = run('lake', ['env', 'lean', '-t', '0', file])
    proofs.push(...parseAxiomOutput(output, names, file))
  }
  requireCheck(proofs.length === theoremNames.length, 'Some native theorems were not checked')
  console.log(`Checked ${proofs.length} native Lean theorem axiom reports.`)

  stage = 'crypto vectors'
  const crypto = []
  for (const [file, expected] of Object.entries(requiredCryptoTests)) {
    requireCheck(existsSync(path(file)), `Missing crypto vector test ${file}`)
    const output = run('lake', ['env', 'lean', '--run', file])
    requireCheck(output.trim() === expected, `Unexpected crypto vector output from ${file}: ${output}`)
    crypto.push({ file, result: 'PASS', detail: expected })
  }
  const otherModuleTests = []
  for (const [file, expected] of Object.entries(requiredOtherModuleTests)) {
    const output = run('lake', ['env', 'lean', '--run', file], 600000)
    requireCheck(output.trim() === expected, `Unexpected native module test output from ${file}: ${output}`)
    otherModuleTests.push({ file, result: 'PASS', detail: expected })
  }
  const focusedTests = []
  const keyTempDir = mkdtempSync(resolve(tmpdir(), 'tornado-lean-pinned-key-'))
  try {
    const keyTempPath = resolve(keyTempDir, 'key.bin')
    writeFileSync(keyTempPath, pinnedKeyRaw, { mode: 0o600, flag: 'wx' })
    for (const [file, expected] of Object.entries(requiredFocusedTests)) {
      const args = ['env', 'lean', '--run', file]
      if (file === 'tests/ProvingKey.lean') args.push(keyTempPath)
      const output = run('lake', args, 600000)
      requireCheck(output.trim() === expected, `Unexpected focused native test output from ${file}: ${output}`)
      focusedTests.push({ file, result: 'PASS', detail: expected })
    }
    const fullProofOutput = run(path('.lake/build/bin/groth16_full_public_test'),
      [keyTempPath], 300000).trim()
    requireCheck(/^PASS: native full public Groth16 proof bytes match pinned SDK oracle \(\d+ ms\)$/.test(fullProofOutput),
      `Native full-key proof bytes differ from pinned SDK oracle: ${fullProofOutput}`)
    focusedTests.push({ file: 'tests/Groth16MSMFull.lean', result: 'PASS',
      detail: 'Exact 256-byte public proof parity with pinned micro-zk-proofs' })
    const pipelineOutput = run(path('.lake/build/bin/classic_proof_pipeline_full_test'),
      [], 600000).trim()
    requireCheck(/^PASS: authenticated compressed assets, complete public witness, 256-byte SDK proof parity, and compiled-key pairing verification \(\d+ ms\)$/.test(pipelineOutput),
      `Native Classic proof pipeline changed: ${pipelineOutput}`)
    focusedTests.push({ file: 'tests/ClassicProofPipelineFull.lean', result: 'PASS',
      detail: 'Authenticated native assets, full public witness, 256-byte proof parity, compiled-key pairing' })
    const withdrawalProofOutput = run(path('.lake/build/bin/withdraw_proof_test'),
      [], 600000).trim()
    requireCheck(/^PASS: selected public note, checked history, exact SDK proof, and direct Classic calldata \(\d+ ms\)$/.test(withdrawalProofOutput),
      `Native one-note proof-to-call builder changed: ${withdrawalProofOutput}`)
    focusedTests.push({ file: 'tests/WithdrawProof.lean', result: 'PASS',
      detail: 'Public selected-note proof, history binding, and direct Classic calldata' })
    const clientOutput = run('lake', ['env', 'lean', '--run',
      'tests/ProverWorkerClient.lean'], 300000).trim()
    requireCheck(/^PASS: prover worker public response binding, strict proof decoding, and compiled-key verification \(\d+ ms\)$/.test(clientOutput),
      `Prover worker parent acceptance changed: ${clientOutput}`)
    focusedTests.push({ file: 'tests/ProverWorkerClient.lean', result: 'PASS',
      detail: 'Pinned public proof acceptance, signal/request binding, malformed proof rejection' })
    const workerDir = mkdtempSync(path('tests/.prover-worker-'))
    try {
      const workerOutput = run(path('.lake/build/bin/prover_worker_test'),
        [path('.lake/build/bin/tornado_prover_worker'), root, workerDir], 600000).trim()
      requireCheck(/^PASS: isolated public-fixture proof, parent verification, malformed request and sanitized failure \(\d+ ms\)$/.test(workerOutput),
        `Native isolated public prover worker changed: ${workerOutput}`)
      focusedTests.push({ file: 'tests/ProverWorker.lean', result: 'PASS',
        detail: 'Separate process nonzero-fee sponsor proof, second SDK direct proof, ordered calls and simulated execution fault traces' })
    } finally {
      rmSync(workerDir, { recursive: true, force: true })
    }
    const equationOutput = run('lake', ['env', 'lean', '--run',
      'tests/BN254Groth16Verify.lean'], 300000).trim()
    requireCheck(/^PASS: pinned Classic proof accepted, all six changed signals and malformed inputs rejected, noble oracle matched \(\d+ ms\)$/.test(equationOutput),
      `Native Classic Groth16 verification equation changed: ${equationOutput}`)
    focusedTests.push({ file: 'tests/BN254Groth16Verify.lean', result: 'PASS',
      detail: 'Public proof accepted; six signal changes and malformed points rejected' })
  } finally {
    rmSync(keyTempDir, { recursive: true, force: true })
  }

  stage = 'domain vectors'
  const notesOutput = run('lake', ['env', 'lean', '--run', 'tests/NotesParsing.lean'])
  requireCheck(notesOutput.trim() ===
    'PASS: parsed and derived Pedersen identifiers for 11 pinned raw-note vectors; malformed-note cases rejected',
    `Unexpected note parser result: ${notesOutput}`)
  const invoicesOutput = run('lake', ['env', 'lean', '--run', 'tests/Invoices.lean'])
  requireCheck(invoicesOutput.trim() === 'PASS: 11 native invoice and deposit ABI vectors',
    `Unexpected invoice result: ${invoicesOutput}`)
  const gridOutput = run('lake', ['env', 'lean', '--run', 'tests/PlanGrid.lean'])
  requireCheck(gridOutput.trim() ===
    'PASS: checked 1860 pinned denomination-plan cases (31 catalogs × 60 amounts; 1272 exact plans, 588 rejections)',
    `Unexpected planner grid result: ${gridOutput}`)
  const choicesOutput = run('lake', ['env', 'lean', '--run', 'tests/PlanChoices.lean'])
  requireCheck(choicesOutput.trim() ===
    'PASS: checked 900 pinned plan-choice cases across seven chain/asset catalogs',
    `Unexpected plan-choice result: ${choicesOutput}`)
  const statusOutput = run('lake', ['env', 'lean', '--run', 'tests/StatusRules.lean'])
  requireCheck(statusOutput.trim() ===
    'PASS: decoded status records, rejected malformed candidates, and blocked signed replacement',
    `Unexpected status rule result: ${statusOutput}`)
  const oneNoteOutput = run('lake', ['env', 'lean', '--run', 'tests/OneNotePolicy.lean'])
  requireCheck(oneNoteOutput.trim() ===
    'PASS: one-note reservation, exposure, unknown outcome, and exact confirmation gates',
    `Unexpected one-note policy result: ${oneNoteOutput}`)
  const statusParityOutput = run('lake', ['env', 'lean', '--run', 'tests/StatusParity.lean'])
  requireCheck(statusParityOutput.trim() === 'Matched 38/38 TS status JSON oracle cases',
    `Unexpected status JSON parity result: ${statusParityOutput}`)
  const abiOutput = run('lake', ['env', 'lean', '--run', 'tests/Abi.lean'])
  requireCheck(abiOutput.trim() === 'PASS: 15 viem ABI vectors, 2 sponsor roundtrips, 15 rejection checks',
    `Unexpected ABI vector result: ${abiOutput}`)
  const batchOutput = run('lake', ['env', 'lean', '--run', 'tests/BatchPolicy.lean'])
  requireCheck(batchOutput.trim() === 'PASS: batch reservation, exposure, single send, and exact confirmation gates',
    `Unexpected batch policy result: ${batchOutput}`)
  const bridgeOutput = run('lake', ['env', 'lean', '--run', 'tests/EvidenceBridge.lean'])
  requireCheck(bridgeOutput.trim() ===
    'PASS: exact one-note and batch event-to-policy bridge, 15 checks',
    `Unexpected event-to-policy bridge result: ${bridgeOutput}`)
  const userOpOutput = run('lake', ['env', 'lean', '--run', 'tests/UserOperation08.lean'])
  requireCheck(userOpOutput.trim() ===
    'PASS: 9 viem v0.8 packed UserOperation/hash vectors, 1 signature, 8 rejection checks',
    `Unexpected UserOperation v0.8 result: ${userOpOutput}`)
  const rlpOutput = run('lake', ['env', 'lean', '--run', 'tests/Rlp.lean'])
  requireCheck(rlpOutput.trim() ===
    'PASS: 20 pinned viem RLP/EIP-1559/EIP-7702 vectors and 10 rejections',
    `Unexpected RLP result: ${rlpOutput}`)
  const r1csOutput = run('lake', ['env', 'lean', '--run', 'tests/Groth16R1CS.lean'])
  requireCheck(r1csOutput.trim() ===
    'PASS: 28275 pinned Tornado R1CS constraints, public witness, and tamper checks',
    `Unexpected Tornado R1CS result: ${r1csOutput}`)
  const keyOutput = run('lake', ['env', 'lean', '--run', 'tests/Groth16Key.lean'])
  requireCheck(keyOutput.trim() ===
    'PASS: pinned Groth16 key header layout and 4 corruption checks',
    `Unexpected Groth16 key header result: ${keyOutput}`)
  const witnessOutput = run('lake', ['env', 'lean', '--run', 'tests/TornadoWitness.lean'])
  requireCheck(witnessOutput.trim() ===
    'PASS: native Lean generated all 49 pinned Tornado witness input slots; eight tamper cases rejected',
    `Unexpected Tornado witness result: ${witnessOutput}`)
  const eventsOutput = run('lake', ['env', 'lean', '--run', 'tests/Events.lean'])
  requireCheck(eventsOutput.trim() ===
    'PASS: 7 viem event vectors, 33 exact-evidence checks, 39 malformed/spoofed/rejection checks',
    `Unexpected event/receipt result: ${eventsOutput}`)

  stage = 'read-only CLI parity'
  const leanBin = path('.lake/build/bin/tornado')
  for (const args of unsupportedCommands) {
    const result = spawnSync(leanBin, args, { cwd: root, env, encoding: 'utf8',
      timeout: 5000, maxBuffer: 1024 * 1024 })
    if (result.error) throw result.error
    requireCheck(result.status === 1 && result.signal === null && result.stdout === '' &&
      result.stderr === 'Error: This command is not implemented in the Lean CLI and cannot move funds.\n',
      `Unsupported command did not fail closed: ${args.join(' ')}`)
  }
  for (const [args, expected] of [
    [['deposit', 'send', '--notes-file', '/missing-notes', '--key-file', '/missing-key'],
      'Choose exactly one deposit mode: --dry-run or --experimental-send.'],
    [['deposit', 'pay-invoice', '--invoice-file', '/missing-invoice', '--key-file', '/missing-key'],
      'Choose exactly one invoice mode: --dry-run or --experimental-send.'],
    [['deposit', 'pay-invoice', '--invoice-file', '/missing-invoice', '--key-file', '/missing-key',
      '--experimental-send'],
      'Experimental invoice send requires a new --journal <path>.'],
    [['withdraw', 'one', '--note-file', '/missing-note', '--recipient',
      '0x1111111111111111111111111111111111111111'],
      'Choose --dry-run, --preflight or --experimental-send.'],
    [['withdraw', 'batch', '--notes-file', '/missing-notes', '--owner-key-file', '/missing-key'],
      'Choose --dry-run or --experimental-send.'],
    [['smart-account', 'recover', '--owner', '0x1111111111111111111111111111111111111111'],
      'Choose --dry-run or --experimental-send for recovery.'],
    [['withdraw', 'one', '--experimental-send', '--yes'],
      'Experimental withdrawals require typed WITHDRAW approval; --yes is unavailable.'],
    [['withdraw', 'batch', '--experimental-send', '--yes'],
      'Experimental withdrawals require typed WITHDRAW approval; --yes is unavailable.'],
    [['withdraw', 'one', '--experimental-send', '--dry-run'],
      'Choose --experimental-send separately from --dry-run and --preflight.'],
    [['withdraw', 'one', '--experimental-send', '--route', 'relayer', '--contract-calls', '/missing-calls'],
      'Owner keys, contract calls and execution simulation options require the batch 4337 route.'],
    [['withdraw', 'batch', '--experimental-send', '--note-index', '1'],
      'Batch withdrawals require the complete selected backup and the 4337 route.'],
    [['smart-account', 'recover', '--experimental-send', '--owner-key-file', '/missing-key'],
      'Experimental recovery requires a new --journal path.'],
  ]) {
    const result = spawnSync(leanBin, args, { cwd: root, env, encoding: 'utf8',
      timeout: 5000, maxBuffer: 1024 * 1024 })
    if (result.error) throw result.error
    requireCheck(result.status === 1 && result.signal === null && result.stdout === '' &&
      result.stderr === `Error: ${expected}\n`,
      `Native funded mode did not fail before file/network access: ${args.join(' ')}`)
  }
  requireCheck(run(leanBin, ['smart-account', 'show', '--help']).startsWith(
    'Usage: tornado smart-account show [options]'),
    'Smart-account show is not reachable through the native executable')
  requireCheck(run(leanBin, ['smart-account', 'status', '--help']).startsWith(
    'Usage: tornado smart-account status --journal <path>'),
    'Read-only smart-account status is not reachable through the native executable')
  requireCheck(run(leanBin, ['deposit', 'inspect-status', '--help']).startsWith(
    'Usage: tornado deposit inspect-status --journal <path>'),
    'Read-only deposit inspector is not reachable through the native executable')
  for (const [args, expected] of [
    [['deposit', 'pay-invoice', '--help'], 'Usage: tornado deposit pay-invoice --invoice-file'],
    [['deposit', 'send', '--help'], 'Usage: tornado deposit send --notes-file'],
    [['deposit', 'status', '--help'], 'Usage: tornado deposit status --journal'],
    [['withdraw', 'one', '--help'], 'Usage: tornado withdraw one --note-file'],
    [['withdraw', 'batch', '--help'], 'Usage: tornado withdraw batch --notes-file'],
    [['withdraw', 'status', '--help'], 'Usage: tornado withdraw status --status-file'],
    [['smart-account', 'recover', '--help'], 'Usage: tornado smart-account recover --owner'],
    [['history', '--help'], 'Usage: tornado history --note-file'],
    [['compliance', 'report', '--help'], 'Usage: tornado compliance report --note-file'],
  ]) requireCheck(run(leanBin, args).startsWith(expected),
    `Native command is not reachable: ${args.join(' ')}`)
  rmSync(path('reports/parity.json'), { force: true })
  console.log('Comparing read-only CLI commands with the pinned TypeScript oracle...')
  run(process.execPath, ['scripts/parity.mjs'], 300000)
  requireCheck(run(process.execPath, ['scripts/notes-file-parity.mjs'], 300000).trim() ===
    'Native note inspect/invoice: 6 pinned read-only parity and rejection checks passed',
    'Native note inspect/invoice parity changed')
  stage = 'native backup creation'
  requireCheck(run(process.execPath, ['scripts/notes-create-smoke.mjs'], 600000).trim() ===
    'Native note creation: independent, seeded recovery, both plan modes, relative path, and exclusive backup checks passed',
    'Native note creation or seed-session recovery changed')
  const parity = JSON.parse(read('reports/parity.json'))
  requireCheck(parity.schemaVersion === 1 && parity.runId === runId &&
    parity.status === 'PASS' && parity.total === 156 && parity.matched === 156 &&
    parity.sourceCommit === 'daaa0c18de91ecc2effbdaea8d0bea7c856ff7f7' &&
    parity.sourceBuildSHA256 === 'cb039416616458ab261036e08e3c4d83991a1b6d7ab4259328894292c035f809',
  'Read-only CLI parity report is absent or incomplete')

  stage = 'source stability'
  requireCheck(JSON.stringify(sourceFiles()) === JSON.stringify(files),
    'Native Lean file inventory changed during verification; rerun from a stable checkout')
  for (const [file, digest] of Object.entries(inputHashes)) {
    requireCheck(sha256(readFileSync(path(file))) === digest,
      `Verification input changed during this run: ${file}`)
  }

  stage = 'result'
  const result = {
    schemaVersion: 1, runId, startedAtUTC, finishedAtUTC: new Date().toISOString(),
    status: 'PASS_WITH_LIMITATIONS', leanToolchain: toolchain, leanVersion: version,
    lakePackages: 0,
    nativeLeanSourceFiles: files.length, inputHashes,
    pinnedProvingAssets: provingAssets.map(({ file, compressedSHA256, rawSize, rawSHA256 }) =>
      ({ file, compressedSHA256, rawSize, rawSHA256, result: 'PASS' })),
    nativeGzipAssetAuthentication: 'PASS',
    classicVerifierProvenance: {
      sourceCommit: '1ef6a263ac6a0e476d063fcb269a9df65a1bd56a',
      vendoredSourceSHA256: 'a2fd9a12dc008ae95e1f9da2968e7d017617e804f22aa0491d2e8a91d965a824',
      completeFixtureKeyMatchesSource: true,
      pinnedProvingKeyAlphaBetaDeltaMatch: true,
      deployedPoolVerifierCodeChecked: false },
    r1csFixtureProvenance: { fixtureSHA256: r1csFixtureSHA256,
      constraintsEqualPinnedCircuit: true, metadataEqualPinnedCircuit: true,
      constraintCount: r1csFixture.constraints.length },
    proofs: { theoremCount: proofs.length,
      axiomFreeCount: proofs.filter(row => row.axioms.length === 0).length,
      allowedStandardAxioms: ['propext', 'Classical.choice', 'Quot.sound'],
      theorems: proofs, noCustomAxiomsOrProofEscapes: true },
    cryptoVectors: crypto,
    otherModuleTests,
    focusedTests,
    domainVectors: { noteParsingAndPedersenIdentity: 11, invoiceAndDepositABI: 11,
      plannerGrid: 1860, plannerChoices: 900, statusRules: 'PASS',
      oneNotePolicy: 'PASS', statusJsonParity: 38,
      abiViemVectors: 15, abiSponsorRoundtrips: 2, abiRejectionChecks: 15,
      batchPolicy: 'PASS', evidenceBridgeChecks: 15, userOperation08ViemVectors: 9,
      userOperation08SignatureVectors: 1, userOperation08RejectionChecks: 8,
      rlpViemVectors: 20, rlpRejectionChecks: 10,
      tornadoR1CSConstraints: 28275, groth16KeyHeader: 'PASS',
      groth16KeyFullDecodeAndTamper: 'PASS',
      tornadoWitnessInputSlots: 49, tornadoWitnessTamperCases: 8,
      tornadoFullWitnessSignals: 36528, tornadoFullWitnessR1CSSlots: 28300,
      tornadoFullWitnessCases: 4,
      bn254G1NobleVectors: 14,
      bn254G2NobleVectors: 14,
      bn254TowerNobleVectors: 3,
      bn254ReducedTateNobleVectors: 3,
      classicPublicGroth16Equation: 'PINNED_PUBLIC_PROOF_ONLY',
      frFftNobleVectors: 7, frSparseHChecks: 3, frLargeRoundtrip: 32768,
      groth16MsmNobleVectors: 4, groth16SyntheticAssemblyVectors: 1,
      groth16FullPublicProofBytes: 256,
      classicComposablePublicProofPipeline: 'PUBLIC_FIXTURE_PASSED_SECRET_UNSAFE',
      isolatedProverWorker: 'PUBLIC_FIXTURE_TESTED_EXPERIMENTAL_LIVE_CONNECTED_VARIABLE_TIME_NONZEROIZING',
      isolatedNoteMetadata: 'PROTECTED_CHILD_PROCESS_TESTED',
      paymasterPreparation: 'DUMMY_ONLY_ESTIMATION_COMMAND_CONNECTED_OFFLINE_FAULT_TESTED',
      signedEntryPointSimulation: 'VIEM_CODEC_AND_EXACT_EVENT_TESTED',
      localSmartAccountAddress: 'SIX_CREATE2_VECTORS_PINNED_BYTECODE_AND_FORGED_RPC_REJECTION',
      recoveryExecution: 'EXPERIMENTAL_NATIVE_COMMAND_OFFLINE_FAULT_TESTED',
      batchStatusPersistence: 'MIRROR_CAS_RESTART_AND_PARTIAL_WRITE_TESTED',
      importedSafeAbi: '28_ENCODING_AND_20_REJECTION_CASES',
      classicRelayerQuote: 'REGISTRY_STAKE_FEE_RECHECK_OFFLINE_TESTED',
      classicRelayerSubmit: 'EXPERIMENTAL_NATIVE_ONE_POST_PROOF_AND_CLAIM_FAULT_TESTED',
      nativeBlindingSampling: 'BOUNDED_UNBIASED_INTERNAL_WITHDRAWAL_BUILDER',
      historyReducerSdkRootVectors: 6,
      eventViemVectors: 7, eventExactEvidenceChecks: 33, eventRejectionChecks: 39 },
    readOnlyParity: { status: parity.status, matched: parity.matched, total: parity.total,
      sourceCommit: parity.sourceCommit, sourceBuildSHA256: parity.sourceBuildSHA256,
      evidence: 'reports/parity.json', noteFileParityAndRejections: 6 },
    backupCreation: { commands: 2, independent: true, seededSession: true,
      plannedIndependent: true, plannedSeeded: true,
      sourceSeedRecoveryMatched: true, exclusiveMode0600: true },
    trustedOsBindings: { privateFiles: 'native/tornado_private_io.c',
      https: 'native/tornado_https.c', get: 'BOUND_TESTED', tested: true,
      explicitLoopbackHttp: 'URL_AND_SOCKET_DESTINATION_TESTED',
      protectedCompareAndReplace: 'NATIVE_FAULT_TESTED',
      model: 'Reviewed C/POSIX and libcurl wrappers; OS, TLS, filesystem, and network remain assumptions' },
    trustedCryptoBoundary: {
      source: 'native/vendor/libsecp256k1', version: 'v0.8.0',
      upstreamCommit: '6e2c8bc4ecdc6e71dbe7a368f360d8d453ce435d',
      sourceTreeSHA256: secpTreeDigest,
      bridge: 'native/tornado_secret_sign.c',
      status: 'PUBLIC_VECTOR_TESTED_NATIVE_SECRET_PATH',
      upstreamTests: 'ONE_ITERATION_PASSED; HIGH_COUNT_CASES_SKIPPED',
      limitation: 'C, compiler, OS memory behavior, and libsecp256k1 remain trusted; no funded test or complete erasure proof' },
    attemptJournal: { status: 'BOUNDED_TESTED_NOT_CONNECTED',
      maxRecords: 20, crossAttemptNoteClaims: 'LOCAL_INSTANCE_TESTED_NOT_CONNECTED',
      replayRecordRefinement: 'FOUR_GUARD_THEOREMS_AND_FAULT_TESTS',
      authenticatedReceipts: false },
    poolHistory: { sagaAndRpcValidators: 'COMMAND_CONNECTED_OFFLINE_FAULT_TESTED',
      selectedPoolReducer: 'COMMAND_CONNECTED_OFFLINE_FAULT_TESTED',
      sdkRootVectors: 6, liveFetchLoop: true,
      liveFetchStatus: 'HISTORY_REPORT_PREFLIGHT_WITH_PINNED_ASSETS_AND_PROTECTED_CACHE',
      endpointCompletenessOrConsensusProved: false },
    nullifierSpentCheck: { status: 'PURE_MODULE_OFFLINE_TESTED_PARALLEL_HISTORY_QUERY_CONNECTED',
      selectedCatalogPoolAndExactBlock: true, rpcQueryDisclosesNullifierHash: true,
      commandConnected: true, consensusOrFinalityProved: false },
    commandCoverage: { typeScriptLeafCommands: 17, nativeReadOnlyParityCommands: 4,
      nativeCommandNamesRecognized: 17,
      partialModeCoverage: true,
      experimentalLiveInvoiceSend: true,
      experimentalLiveSequentialMultiDeposit: true,
      experimentalLiveSimple7702Deposit: true,
      experimentalLiveDirectWithdrawal: true,
      experimentalLiveRelayerWithdrawal: true,
      experimentalLiveBatchWithdrawal: true,
      experimentalLiveRecovery: true,
      nativeExtraReadOnlyCommands: 1,
      nativeBackupCreationCommands: 2,
      rootVersionParityCases: 2,
      unsupportedLeafCommands: unsupportedCommands.length, unsupportedFailClosedTests: unsupportedCommands.length,
      moneyMovingParity: false },
    fullCliParity: false, fullCliCorrectnessProof: false,
    limitations: [
      'Exact CLI differential cases cover pools, deposit plan, notes inspect/invoice, and root version flags. New command modes have focused offline checks, not complete TypeScript differential parity. Backup creation uses random generation with finite compatibility and recovery checks.',
      'The planner grid and crypto vectors are finite tests, not all-input or cryptographic-security proofs.',
      'A native full-size public fixture authenticates compressed assets, produces exact Groth16 proof bytes, and passes the compiled-key reduced Tate pairing equation. This is finite evidence, not secret-safe proving, a theorem of Groth16 soundness, or deployed-verifier acceptance.',
      'Experimental direct, relayer and batch withdrawal commands are connected and tested with public fixtures and injected effects only. The isolated native Lean prover and note-derived signer remain variable time and nonzeroizing; worker binary pinning, funded testing and an end-to-end correctness proof remain open.',
      'A generic pairing helper accepts a caller-supplied key; the compiled Classic wrapper instead fixes every key point to reviewed source. No selected pool or deployed verifier code is authenticated or connected to a command.',
      'A bounded selected-pool Saga/RPC fetch loop, pinned offline assets and protected snapshot cache serve history, compliance report, and withdrawal preflight. The cache rechecks checkpoints and handles reorgs, but provider completeness and consensus are not proved. An endpoint can omit or fabricate chain data.',
      'The exact-block isSpent check used by history and withdrawal preflight discloses the nullifier hash to the configured RPC; its response is not an authenticated state proof.',
      'Experimental pay-invoice can sign and broadcast with a local invoice claim, sender lock, conservative maximum-gas cap, and twelve-confirmation gate. Its key-file signer uses a protected native libsecp256k1 boundary, but the C/compiler/OS behavior, complete erasure, live HTTP effects, deployed contracts, and fund safety are not end-to-end proved or funded-testnet validated.',
      'Sequential and Simple7702 multi-note deposits have experimental live adapters with offline fault tests and pinned viem vectors. Signed delegation is journaled before estimation; no funded end-to-end test or correctness proof was completed.',
      'Experimental recovery and withdrawal live adapters require explicit mode selection and typed approval. Development sent no funded transactions. Offline fault tests and exact event reconciliation do not establish complete command parity or production fund safety. Shared sender locks coordinate only one protected key directory; copies elsewhere are not globally coordinated.',
      'Lean proofs cover selected native definitions; they do not prove the C OS bindings, Ethereum consensus, deployed contracts or filesystem durability.',
    ],
  }
  writeFileSync(reportPath, JSON.stringify(result, null, 2) + '\n')
  console.log(`PASS_WITH_LIMITATIONS: ${proofs.length} Lean theorems, ${crypto.length} crypto vector suites, ` +
    '11 note identities, 11 invoices, 1860 grid cases, 900 choice cases, 38 status JSON cases, 15 ABI vectors, 9 UserOperation v0.8 vectors, 20 RLP vectors, 28275 R1CS constraints, 28300 full witness slots, 7 event vectors, complete pinned key parse, batch policy tests, 156/156 initial read-only CLI cases plus 6 note-file cases. Experimental deposit sending is not production certified; full money-moving parity: NOT CLAIMED.')
} catch (error) {
  const message = error instanceof Error ? error.message : String(error)
  writeFileSync(reportPath, JSON.stringify({ schemaVersion: 1, runId, startedAtUTC,
    finishedAtUTC: new Date().toISOString(), status: 'FAIL', stage, error: message }, null, 2) + '\n')
  console.error(`Native Lean verification failed at ${stage}: ${message}`)
  process.exitCode = 1
}
