// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Synthetic USDT-like allowance rule makes the reset-before-approve order
// observable. This is a test token, not any deployed token implementation.
contract ProbeDepositToken {
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    event Approval(address indexed owner, address indexed spender, uint256 amount);
    event Transfer(address indexed from, address indexed to, uint256 amount);
    function mint(address to, uint256 amount) external { balanceOf[to] += amount; }
    function seedAllowance(address owner, address spender, uint256 amount) external { allowance[owner][spender] = amount; }
    function approve(address spender, uint256 amount) external returns (bool) {
        require(amount == 0 || allowance[msg.sender][spender] == 0, "reset first");
        allowance[msg.sender][spender] = amount;
        emit Approval(msg.sender, spender, amount);
        return true;
    }
    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        require(allowance[from][msg.sender] >= amount && balanceOf[from] >= amount, "balance or allowance");
        allowance[from][msg.sender] -= amount;
        balanceOf[from] -= amount;
        balanceOf[to] += amount;
        emit Transfer(from, to, amount);
        return true;
    }
}

// Synthetic deposit-only ledger, independently decoding the native bytes32
// commitment and enforcing exact ETH value or ERC-20 transferFrom amount.
// No real Classic tree, verifier, or withdrawal path is implemented here.
contract ProbeDepositPool {
    ProbeDepositToken public immutable token;
    uint256 public immutable denomination;
    bytes32[] public commitments;
    mapping(bytes32 => bool) public seen;
    event Deposit(bytes32 indexed commitment, uint32 leafIndex, uint256 timestamp);
    constructor(ProbeDepositToken token_, uint256 amount_) { token = token_; denomination = amount_; }
    function count() external view returns (uint256) { return commitments.length; }
    function deposit(bytes32 commitment) external payable {
        require(!seen[commitment], "duplicate commitment");
        if (address(token) == address(0)) require(msg.value == denomination, "wrong ETH value");
        else {
            require(msg.value == 0, "token deposit carries ETH");
            require(token.transferFrom(msg.sender, address(this), denomination));
        }
        seen[commitment] = true;
        commitments.push(commitment);
        emit Deposit(commitment, uint32(commitments.length - 1), block.timestamp);
    }
}
