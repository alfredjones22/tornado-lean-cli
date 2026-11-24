// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {SimpleAccountFactory} from "@account-abstraction/contracts/accounts/SimpleAccountFactory.sol";
import {TornadoPaymaster} from "privacy/contracts/tornadocash/TornadoPaymaster.sol";
import {IPaymaster} from "@account-abstraction/contracts/interfaces/IPaymaster.sol";
import {PackedUserOperation} from "@account-abstraction/contracts/interfaces/PackedUserOperation.sol";

// Synthetic EntryPoint boundary: no handleOps, gas accounting, signatures,
// deposits, or ERC-7562 validation. The imported account and paymaster are real.
contract ProbeEntryPoint {
    address public immutable senderCreator;
    bytes public context;
    constructor() { senderCreator = msg.sender; }
    function supportsInterface(bytes4) external pure returns (bool) { return true; }
    function validateNative(address paymaster, address sender, bytes calldata sponsorData,
        uint256 callGasLimit, uint256 maxCost) external {
        PackedUserOperation memory op;
        op.sender = sender;
        op.accountGasLimits = bytes32(callGasLimit);
        op.paymasterAndData = abi.encodePacked(paymaster, uint128(500_000), uint128(50_000), sponsorData);
        uint256 validation;
        (context, validation) = IPaymaster(paymaster).validatePaymasterUserOp(op, bytes32(0), maxCost);
        require(validation == 0, "validation failed");
    }
    function postNative(address paymaster, uint256 actualCost) external {
        IPaymaster(paymaster).postOp(IPaymaster.PostOpMode.opSucceeded, context, actualCost, 0);
    }
}

contract ProbeToken {
    mapping(address => uint256) public balanceOf;
    event Transfer(address indexed from, address indexed to, uint256 amount);
    function mint(address recipient, uint256 amount) external { balanceOf[recipient] += amount; }
    function transfer(address recipient, uint256 amount) external returns (bool) {
        require(balanceOf[msg.sender] >= amount, "insufficient tokens");
        balanceOf[msg.sender] -= amount;
        balanceOf[recipient] += amount;
        emit Transfer(msg.sender, recipient, amount);
        return true;
    }
}

// Synthetic pool: intentionally no Merkle tree and no proof verification.
// The real, unchanged Classic verifier is tested separately with public proofs.
contract ProbePool {
    ProbeToken public immutable token;
    mapping(bytes32 => bool) public spent;
    bytes public lastProof;
    bytes32 public lastRoot;
    address public lastRecipient;
    address public lastRelayer;
    uint256 public lastFee;
    event Withdrawal(bytes32 nullifierHash, address recipient, address relayer, uint256 fee);
    constructor(ProbeToken token_) { token = token_; }
    function withdraw(bytes calldata proof, bytes32 root, bytes32 nullifierHash,
        address payable recipient, address payable relayer, uint256 fee, uint256 refund) external {
        require(!spent[nullifierHash], "spent");
        require(refund == 0 && fee < 1000, "invalid payout");
        spent[nullifierHash] = true;
        lastProof = proof;
        lastRoot = root;
        lastRecipient = recipient;
        lastRelayer = relayer;
        lastFee = fee;
        require(token.transfer(recipient, 1000 - fee));
        if (fee != 0) require(token.transfer(relayer, fee));
        emit Withdrawal(nullifierHash, recipient, relayer, fee);
    }
}

contract ProbeRecorder {
    uint256[] public seen;
    function note(uint256 value) external { seen.push(value); }
    function count() external view returns (uint256) { return seen.length; }
}

contract ProbeFailure {
    function fail() external pure { revert("intentional test failure"); }
}

interface IClassicVerifierProbe {
    function verifyProof(bytes memory proof, uint256[6] memory inputs) external view returns (bool);
}

// Synthetic single-root ETH ledger, using the actual unchanged Classic
// verifier. It deliberately does not implement the real Classic Merkle tree.
contract ProbeEthPool {
    IClassicVerifierProbe public immutable verifier;
    bytes32 public immutable expectedRoot;
    uint256 public constant denomination = 0.01 ether;
    mapping(bytes32 => bool) public spent;
    constructor(IClassicVerifierProbe verifier_, bytes32 root_) {
        verifier = verifier_; expectedRoot = root_;
    }
    function withdraw(bytes calldata proof, bytes32 root, bytes32 nullifierHash,
        address payable recipient, address payable relayer, uint256 fee, uint256 refund) external {
        require(root == expectedRoot && !spent[nullifierHash], "unknown root or spent");
        require(fee < denomination && refund == 0, "invalid payout");
        require(verifier.verifyProof(proof, [uint256(root), uint256(nullifierHash), uint256(uint160(address(recipient))),
            uint256(uint160(address(relayer))), fee, refund]), "proof rejected");
        spent[nullifierHash] = true;
        (bool ok,) = recipient.call{value: denomination - fee}("");
        require(ok, "recipient transfer failed");
        (ok,) = relayer.call{value: fee}("");
        require(ok, "relayer transfer failed");
    }
}
