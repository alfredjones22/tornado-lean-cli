# Sepolia live test results

Date: 26 November 2026. Network: Sepolia, chain `11155111`.
These are observed execution results and focused regression checks, not a proof of bug-free software.

## Observed totals

- 12 completed deposit/withdrawal scenarios, with dry-run review before broadcasting.
- 18 notes funded through 15 distinct deposit transactions; total principal: **0.54 Sepolia ETH**.
- 13 distinct successful withdrawal transactions; all 18 selected nullifiers were subsequently reported spent.
- Four successful owner-paid recovery transactions.
- Final read-only check at block `12217210`: both tested smart accounts held zero ETH.
- C2 held `0.001` Sepolia WETH; C1 retained `266684056671940` wei of EntryPoint gas credit.
- All 18 protected withdrawal status records agreed on their reserved candidates and confirmed outcomes.

C1: `0x90095377e7e53293a4924b2e8cb5c9aaea246699`.
C2: `0xaa2c4259f262a0a89edb679222dcb9146b5a7dab`.
Every deposit was funded by C1. Funds were deliberately recycled between these test accounts; these tests do not demonstrate anonymity.

## Completed scenarios

1. **Single 0.01 ETH, default routing.** Ordinary EIP-1559 deposit, then direct sponsored withdrawal to C1.
   [Deposit](https://sepolia.etherscan.io/tx/0xe924786f79ec2b592d69bc81a062d5d140c6d6b79ad623e86200737fb3fff65c) · [Withdrawal](https://sepolia.etherscan.io/tx/0xe4e6fd059f2d3cc5c7d54e564261558aabc7ea92e4dee253ccae3de30ac3c41b).

2. **Single 0.03 ETH to another recipient.** Ordinary deposit, then direct sponsored withdrawal to C2.
   [Deposit](https://sepolia.etherscan.io/tx/0x125ffaa21dbb53a021e1701e85ffb55458c143db0571bd13dd8e5097365ac961) · [Withdrawal](https://sepolia.etherscan.io/tx/0x37d264cae453a176ca682d391833681f310cd69acd851b0d79a4d938cd96e546).

3. **Single 0.1 ETH with explicit delegation.** `--delegated` selected a Simple7702 UserOperation; direct sponsored withdrawal returned funds to C1.
   [Deposit](https://sepolia.etherscan.io/tx/0xbe6f81f18e8ec2def79e5382b4eba0c279d7075679d69a1b734638ca67c3feff) · [Withdrawal](https://sepolia.etherscan.io/tx/0xec77bec4a569ade33ea975881742943dc03ba87375a199f9863d06573eedbcb2).

4. **Two 0.03 ETH notes, sequential deposit and smart-account withdrawal.** Proceeds reached C1's smart account and were recovered to C1.
   [Deposit 1](https://sepolia.etherscan.io/tx/0xaede0c6516b1ba31963fa14eb00752711cda800d85022ad4c75e5acea09de0be) · [Deposit 2](https://sepolia.etherscan.io/tx/0x4ade4ad2f487746c5ff8ed3a9779178d858fa107aa42682d91a224994e2bed8c).
   [Withdrawal](https://sepolia.etherscan.io/tx/0x2803c0aacc3880aae61cad9ca4b0844fb25f1662ebbc86e620d35255f61077c2) · [Recovery](https://sepolia.etherscan.io/tx/0x2f1474ab19ff036acc9ebf7dfb18e9bc193c8abf713985859196755e90324378).
   After fixing a local signed-simulation encoder limit, the exact saved signed candidate was continued byte-for-byte and reconciled. This specific continuation is not a general withdrawal-resume feature.

5. **Two 0.03 ETH notes, automatic delegated deposit.** Batch withdrawal forwarded the net proceeds to C2, exercising the `--note-file` and `--recipient` aliases.
   [Deposit](https://sepolia.etherscan.io/tx/0x64f0555d9b9ba68de5d8b20a5c21033d180a97ea8ccd51b0f8ebe3ec87e68288) · [Withdrawal](https://sepolia.etherscan.io/tx/0x07cc0a85e7342b5884e7f7cc57f28db7486f4ca712d9eab6b0e884b09178593b).

6. **Mixed 0.03 + 0.01 ETH, sequential deposit.** The generated 0.04 ETH plan was deposited as two transactions and withdrawn together to C1.
   [Deposit 1](https://sepolia.etherscan.io/tx/0x529c43dbebda88e544e21bf4906b1d24662738746a63fcdd934b2b44cd600832) · [Deposit 2](https://sepolia.etherscan.io/tx/0x3fb556c316d5220ebb717d3b065ab7bfb392b0aacca1e34d191ed85437bc3e7a).
   [Withdrawal](https://sepolia.etherscan.io/tx/0xe20831f29eecf1cb85956e34a9a7037460957538772e95c3bdd19f1bea37d293).

7. **Mixed 0.1 + 0.01 ETH, delegated deposit and a different owner.** C2 owned the withdrawing smart account; the batch forwarded proceeds to C1.
   [Deposit](https://sepolia.etherscan.io/tx/0xf6cff5473b3944a42a37bac9930368a1a81152e357fd4e714e535700396369c1) · [Withdrawal](https://sepolia.etherscan.io/tx/0x868f869ed13d26e6df41c79e4af867f5db53e0524d20a9cfdc0772a79e3fcd5d).

8. **Two 0.03 ETH notes withdrawn separately.** One delegated deposit funded both notes; `--note-index 1` and `2` selected direct withdrawals to C1 and C2 respectively.
   [Deposit](https://sepolia.etherscan.io/tx/0x0c77eac73a401c439714b4d37de8a88dd098809a8a9eea9982fabd6c9aa8dcd3).
   [Withdrawal 1](https://sepolia.etherscan.io/tx/0xf0d38265c67e60a89f22cc66c2c10d9dd32527abe1f7633772819c669b8119da) · [Withdrawal 2](https://sepolia.etherscan.io/tx/0x58cb8649525fd8caca4e6519447c8c83f3f7c74e6f498bf1c003d8af88af4ddb).

9. **One 0.03 ETH note with post-withdrawal calls.** Explicit delegated deposit; smart-account withdrawal wrapped 0.001 ETH and transferred that WETH to C2. The remaining ETH was recovered to C1.
   [Deposit](https://sepolia.etherscan.io/tx/0xe9c5768d64588713b06df88d91d84220ad765a2a5afa5ee2e80c1d4bf57130e0) · [Withdrawal and calls](https://sepolia.etherscan.io/tx/0x1bdd7172cea33425d95bec762d83558f4ca72b9f4b4d1f0172bfdf5dffbb8281).
   [Recovery](https://sepolia.etherscan.io/tx/0x9212053aeed802b23a30e418eeeddc2a56956a0926c0f07c79c4285d0c615505).

10. **Public invoice for 0.01 ETH.** `notes invoice` and `deposit pay-invoice` funded the note without supplying its secret to the payer command; direct withdrawal returned funds to C1.
    [Deposit](https://sepolia.etherscan.io/tx/0xac56e48280e838c2285a0ec1ac607f81cb1e0781b1cd0a412bf51eb7e175e088) · [Withdrawal](https://sepolia.etherscan.io/tx/0x3b36dc5e428f38919ec53dfc5f0ca8c7dcccaf3eeaab4c277c4728adc36ad2a6).

11. **Interrupted sequential plan and real resume.** Two 0.01 ETH notes; the first deposit was confirmed, then the next step was cancelled. `deposit send --resume` used the original journal, skipped the confirmed first transaction and funded only the second note. Both were then withdrawn together to C1.
    [Original deposit](https://sepolia.etherscan.io/tx/0x7d8cc4b059dcb5635c6093611c587ccb589f18bad273fc4c5855463c9aa0d70f) · [Resumed deposit](https://sepolia.etherscan.io/tx/0x4f72b48eac61d913c7f0da4a578c12472450e987f1aec28810d008e48120afbe).
    [Withdrawal](https://sepolia.etherscan.io/tx/0x580303eb1548112d1d51e50d77bdf3564e2574b174feab9b0a6c64e508cb8138). Each commitment had one matching deposit event; the first transaction was not replaced or duplicated.

12. **Delegated 0.01 ETH deposit and controlled stale-head history.** Deposit inclusion was at block `12217155`. A read-only loopback proxy returned `12217154` for its first head response, then passed through real heads. A cold history-cache run caught up through `12217163`, found the recent deposit and completed direct withdrawal to C1.
    [Deposit](https://sepolia.etherscan.io/tx/0x326ff378952835d0a4ce3a391d3684693e2534f857f3b18f7c046a0519c8c70c) · [Withdrawal](https://sepolia.etherscan.io/tx/0xe3ebf4b3abf40ba3d6583c61e1e75cbaae5de3393378dc497e498112833775ec).
    The final EntryPoint credit readout matched the receipt-block and subsequent RPC readings: `266684056671940` wei.

Final recovery sweeps emptied the remaining ETH from both tested smart accounts:
[C1 account recovery](https://sepolia.etherscan.io/tx/0x4d81d0b0c758c3946c3bf019492d0a5087a35337542133307355e35de4b090e9) · [C2 account recovery](https://sepolia.etherscan.io/tx/0x6795670654d40270e6c17d2a437cc06817a8879e3a78d95eaa85ccd0119e210f).

## Fixes exercised

- Explicit `--non-interactive` authorization preserves printed reviews, protected journals, reservations and revalidation.
- New smart-account deployment gas is bounded separately; omitted optional gas measurements retain their floors without repeated inflation.
- Eligible withdrawals can lower bids before final review while preserving proofs, note fees, payouts and gas limits. Custom contract calls retain the original bid; unused-fee refunds remain conditional.
- Authenticated pinned history assets and protected caches retain their integrity checks; one bounded head catch-up handles deposits included during synchronization.
- Batch option aliases, protected-file diagnostics and preparation-stage errors identify actionable failures without echoing provider bodies.
- EntryPoint credit can cover delegated gas costs, never deposit principal or ordinary sequential transaction gas. Funding and credit are rechecked before signing.
- Confirmed deposits report remaining EntryPoint gas credit without turning an optional readout failure into an apparent deposit failure.

## Validation and limits

CLI/worker builds and focused regression tests passed. The kernel-only verification gate also passed, checking 2,291 Lean theorem axiom reports with no custom axioms or proof escapes. The full regression gate was not rerun for this campaign; the kernel-only gate does not run the regression tests or establish full CLI correctness.
Successful receipts, matching deposit/withdrawal/EntryPoint events, all selected spent flags, mirror consistency and final balances were checked against public RPC evidence.
The scope was Sepolia ETH plans of one or two notes, sequential and Simple7702 deposits, sponsored ERC-4337 withdrawals, one WETH call sequence, and ETH recovery.
Mainnet execution, Classic relayer submission, ERC-20 Tornado pools and maximum-size batches were not tested here.
RPC evidence remains a provider claim; these checks do not authenticate Ethereum consensus, establish finality, prove privacy or certify general software correctness.
