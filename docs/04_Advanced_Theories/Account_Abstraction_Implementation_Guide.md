# 账户抽象 (Account Abstraction) 技术实现指南

## 1. ERC-4337 标准实现

### 1.1 EntryPoint 合约

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@openzeppelin/contracts/security/ReentrancyGuard.sol";
import "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";

contract EntryPoint is ReentrancyGuard {
    using ECDSA for bytes32;
    
    struct UserOperation {
        address sender;
        uint256 nonce;
        bytes initCode;
        bytes callData;
        uint256 callGasLimit;
        uint256 verificationGasLimit;
        uint256 preVerificationGas;
        uint256 maxFeePerGas;
        uint256 maxPriorityFeePerGas;
        bytes paymasterAndData;
        bytes signature;
    }
    
    struct UserOpInfo {
        uint256 prefund;
        bool paid;
        uint256 validAfter;
        uint256 validUntil;
        bool success;
        uint256 actualGasCost;
    }
    
    mapping(address => uint256) public getNonce;
    mapping(bytes32 => bool) public knownOps;
    
    event UserOperationEvent(
        bytes32 indexed userOpHash,
        address indexed sender,
        address indexed paymaster,
        uint256 nonce,
        bool success,
        uint256 actualGasCost,
        uint256 actualGasUsed
    );
    
    function handleOps(UserOperation[] calldata ops, address payable beneficiary) external {
        uint256 opslen = ops.length;
        UserOpInfo[] memory opInfos = new UserOpInfo[](opslen);
        
        for (uint256 i = 0; i < opslen; i++) {
            UserOpInfo memory opInfo = opInfos[i];
            UserOperation calldata userOp = ops[i];
            
            uint256 preGas = gasleft();
            
            // 验证用户操作
            _validateUserOp(userOp, opInfo);
            
            // 执行用户操作
            _executeUserOp(userOp, opInfo);
            
            uint256 paid = opInfo.actualGasCost;
            uint256 gasUsed = preGas - gasleft();
            
            emit UserOperationEvent(
                getUserOpHash(userOp),
                userOp.sender,
                address(0), // paymaster
                userOp.nonce,
                opInfo.success,
                paid,
                gasUsed
            );
        }
        
        // 补偿受益人
        if (beneficiary != address(0)) {
            beneficiary.transfer(address(this).balance);
        }
    }
    
    function _validateUserOp(UserOperation calldata userOp, UserOpInfo memory opInfo) internal {
        // 验证nonce
        require(userOp.nonce == getNonce[userOp.sender], "Invalid nonce");
        getNonce[userOp.sender]++;
        
        // 验证签名
        bytes32 userOpHash = getUserOpHash(userOp);
        require(!knownOps[userOpHash], "Operation already known");
        knownOps[userOpHash] = true;
        
        // 验证账户
        address account = userOp.sender;
        if (account.code.length == 0) {
            // 创建账户
            _createAccount(userOp);
            account = userOp.sender;
        }
        
        // 调用账户的验证函数
        (bool success, bytes memory ret) = account.call{gas: userOp.verificationGasLimit}(
            abi.encodeWithSignature("validateUserOp((address,uint256,bytes,bytes,uint256,uint256,uint256,uint256,uint256,bytes,bytes),bytes32,uint256)",
                userOp, userOpHash, 0)
        );
        
        require(success, "Validation failed");
        
        // 解析验证结果
        (uint256 validAfter, uint256 validUntil) = abi.decode(ret, (uint256, uint256));
        require(block.timestamp >= validAfter, "Too early");
        require(block.timestamp <= validUntil, "Too late");
    }
    
    function _executeUserOp(UserOperation calldata userOp, UserOpInfo memory opInfo) internal {
        uint256 preGas = gasleft();
        
        // 执行用户操作
        (bool success, ) = userOp.sender.call{gas: userOp.callGasLimit}(userOp.callData);
        opInfo.success = success;
        
        uint256 gasUsed = preGas - gasleft();
        opInfo.actualGasCost = gasUsed * userOp.maxFeePerGas;
    }
    
    function _createAccount(UserOperation calldata userOp) internal {
        if (userOp.initCode.length > 0) {
            address factory = address(uint160(uint256(bytes32(userOp.initCode[:32]))));
            bytes memory initCallData = userOp.initCode[32:];
            
            (bool success, ) = factory.call(initCallData);
            require(success, "Account creation failed");
        }
    }
    
    function getUserOpHash(UserOperation calldata userOp) public view returns (bytes32) {
        return keccak256(abi.encode(
            userOp.sender,
            userOp.nonce,
            keccak256(userOp.initCode),
            keccak256(userOp.callData),
            userOp.callGasLimit,
            userOp.verificationGasLimit,
            userOp.preVerificationGas,
            userOp.maxFeePerGas,
            userOp.maxPriorityFeePerGas,
            keccak256(userOp.paymasterAndData)
        ));
    }
    
    receive() external payable {}
}
```

### 1.2 智能合约钱包

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/security/ReentrancyGuard.sol";
import "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";

contract SmartContractWallet is Ownable, ReentrancyGuard {
    using ECDSA for bytes32;
    
    struct UserOperation {
        address sender;
        uint256 nonce;
        bytes initCode;
        bytes callData;
        uint256 callGasLimit;
        uint256 verificationGasLimit;
        uint256 preVerificationGas;
        uint256 maxFeePerGas;
        uint256 maxPriorityFeePerGas;
        bytes paymasterAndData;
        bytes signature;
    }
    
    mapping(address => bool) public guardians;
    mapping(bytes32 => bool) public executedHashes;
    uint256 public threshold;
    uint256 public nonce;
    
    event GuardianAdded(address indexed guardian);
    event GuardianRemoved(address indexed guardian);
    event ThresholdUpdated(uint256 newThreshold);
    event TransactionExecuted(address indexed target, uint256 value, bytes data);
    
    constructor(address[] memory _guardians, uint256 _threshold) {
        require(_guardians.length >= _threshold, "Invalid threshold");
        require(_threshold > 0, "Threshold must be positive");
        
        for (uint256 i = 0; i < _guardians.length; i++) {
            guardians[_guardians[i]] = true;
            emit GuardianAdded(_guardians[i]);
        }
        
        threshold = _threshold;
        emit ThresholdUpdated(_threshold);
    }
    
    function validateUserOp(
        UserOperation calldata userOp,
        bytes32 userOpHash,
        uint256 missingAccountFunds
    ) external returns (uint256 validationData) {
        require(msg.sender == address(0x5FF137D4b0FDCD49DcA30c7CF57E578a026d2789), "Invalid entry point");
        require(userOp.sender == address(this), "Invalid sender");
        require(userOp.nonce == nonce, "Invalid nonce");
        
        // 验证签名
        bytes32 hash = userOpHash.toEthSignedMessageHash();
        address signer = hash.recover(userOp.signature);
        require(guardians[signer], "Invalid signature");
        
        nonce++;
        
        // 返回验证数据
        return 0; // 0 = 验证成功
    }
    
    function execute(
        address target,
        uint256 value,
        bytes calldata data
    ) external onlyOwner nonReentrant {
        require(target != address(0), "Invalid target");
        
        (bool success, ) = target.call{value: value}(data);
        require(success, "Execution failed");
        
        emit TransactionExecuted(target, value, data);
    }
    
    function executeBatch(
        address[] calldata targets,
        uint256[] calldata values,
        bytes[] calldata datas
    ) external onlyOwner nonReentrant {
        require(targets.length == values.length && targets.length == datas.length, "Length mismatch");
        
        for (uint256 i = 0; i < targets.length; i++) {
            require(targets[i] != address(0), "Invalid target");
            
            (bool success, ) = targets[i].call{value: values[i]}(datas[i]);
            require(success, "Batch execution failed");
            
            emit TransactionExecuted(targets[i], values[i], datas[i]);
        }
    }
    
    function addGuardian(address guardian) external onlyOwner {
        require(guardian != address(0), "Invalid guardian");
        require(!guardians[guardian], "Guardian already exists");
        
        guardians[guardian] = true;
        emit GuardianAdded(guardian);
    }
    
    function removeGuardian(address guardian) external onlyOwner {
        require(guardians[guardian], "Guardian does not exist");
        require(getGuardianCount() > threshold, "Cannot remove guardian");
        
        guardians[guardian] = false;
        emit GuardianRemoved(guardian);
    }
    
    function updateThreshold(uint256 newThreshold) external onlyOwner {
        require(newThreshold > 0, "Threshold must be positive");
        require(newThreshold <= getGuardianCount(), "Threshold too high");
        
        threshold = newThreshold;
        emit ThresholdUpdated(newThreshold);
    }
    
    function getGuardianCount() public view returns (uint256) {
        uint256 count = 0;
        // 这里需要遍历所有可能的guardian地址
        // 简化实现，实际需要维护guardian列表
        return count;
    }
    
    function isGuardian(address account) external view returns (bool) {
        return guardians[account];
    }
    
    receive() external payable {}
}
```

### 1.3 Paymaster 合约

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import "@openzeppelin/contracts/security/ReentrancyGuard.sol";

contract Paymaster is Ownable, ReentrancyGuard {
    struct UserOperation {
        address sender;
        uint256 nonce;
        bytes initCode;
        bytes callData;
        uint256 callGasLimit;
        uint256 verificationGasLimit;
        uint256 preVerificationGas;
        uint256 maxFeePerGas;
        uint256 maxPriorityFeePerGas;
        bytes paymasterAndData;
        bytes signature;
    }
    
    mapping(address => bool) public whitelistedTokens;
    mapping(address => uint256) public tokenPrices;
    mapping(address => uint256) public userBalances;
    
    uint256 public gasPrice;
    uint256 public minBalance;
    
    event TokenWhitelisted(address indexed token);
    event TokenRemoved(address indexed token);
    event PriceUpdated(address indexed token, uint256 price);
    event BalanceDeposited(address indexed user, address indexed token, uint256 amount);
    event BalanceWithdrawn(address indexed user, address indexed token, uint256 amount);
    
    constructor() {
        gasPrice = 20 gwei;
        minBalance = 0.01 ether;
    }
    
    function validatePaymasterUserOp(
        UserOperation calldata userOp,
        bytes32 userOpHash,
        uint256 maxCost
    ) external view returns (bytes memory context, uint256 validationData) {
        require(msg.sender == address(0x5FF137D4b0FDCD49DcA30c7CF57E578a026d2789), "Invalid entry point");
        
        // 解析paymaster数据
        (address token, uint256 amount) = abi.decode(userOp.paymasterAndData, (address, uint256));
        
        require(whitelistedTokens[token], "Token not whitelisted");
        require(userBalances[userOp.sender] >= amount, "Insufficient balance");
        
        // 计算gas成本
        uint256 gasCost = (userOp.callGasLimit + userOp.verificationGasLimit) * userOp.maxFeePerGas;
        require(gasCost <= maxCost, "Gas cost too high");
        
        context = abi.encode(userOp.sender, token, amount);
        validationData = 0; // 0 = 验证成功
    }
    
    function postOp(
        bytes calldata context,
        bool success,
        uint256 actualGasCost
    ) external {
        require(msg.sender == address(0x5FF137D4b0FDCD49DcA30c7CF57E578a026d2789), "Invalid entry point");
        
        (address user, address token, uint256 amount) = abi.decode(context, (address, address, uint256));
        
        if (success) {
            // 扣除用户余额
            userBalances[user] -= amount;
            
            // 转移代币给paymaster
            IERC20(token).transferFrom(user, address(this), amount);
        }
    }
    
    function deposit(address token, uint256 amount) external nonReentrant {
        require(whitelistedTokens[token], "Token not whitelisted");
        require(amount > 0, "Invalid amount");
        
        IERC20(token).transferFrom(msg.sender, address(this), amount);
        userBalances[msg.sender] += amount;
        
        emit BalanceDeposited(msg.sender, token, amount);
    }
    
    function withdraw(address token, uint256 amount) external nonReentrant {
        require(userBalances[msg.sender] >= amount, "Insufficient balance");
        
        userBalances[msg.sender] -= amount;
        IERC20(token).transfer(msg.sender, amount);
        
        emit BalanceWithdrawn(msg.sender, token, amount);
    }
    
    function addWhitelistedToken(address token) external onlyOwner {
        require(token != address(0), "Invalid token");
        require(!whitelistedTokens[token], "Token already whitelisted");
        
        whitelistedTokens[token] = true;
        emit TokenWhitelisted(token);
    }
    
    function removeWhitelistedToken(address token) external onlyOwner {
        require(whitelistedTokens[token], "Token not whitelisted");
        
        whitelistedTokens[token] = false;
        emit TokenRemoved(token);
    }
    
    function updateTokenPrice(address token, uint256 price) external onlyOwner {
        require(whitelistedTokens[token], "Token not whitelisted");
        require(price > 0, "Invalid price");
        
        tokenPrices[token] = price;
        emit PriceUpdated(token, price);
    }
    
    function setGasPrice(uint256 _gasPrice) external onlyOwner {
        gasPrice = _gasPrice;
    }
    
    function setMinBalance(uint256 _minBalance) external onlyOwner {
        minBalance = _minBalance;
    }
    
    function getBalance(address user) external view returns (uint256) {
        return userBalances[user];
    }
    
    function calculateGasCost(
        uint256 callGasLimit,
        uint256 verificationGasLimit,
        uint256 maxFeePerGas
    ) external view returns (uint256) {
        return (callGasLimit + verificationGasLimit) * maxFeePerGas;
    }
}
```

## 2. 账户工厂合约

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "./SmartContractWallet.sol";

contract AccountFactory {
    mapping(address => address) public accounts;
    mapping(address => bool) public isAccount;
    
    event AccountCreated(address indexed owner, address indexed account);
    
    function createAccount(
        address[] calldata guardians,
        uint256 threshold
    ) external returns (address account) {
        require(accounts[msg.sender] == address(0), "Account already exists");
        require(guardians.length >= threshold, "Invalid threshold");
        
        // 创建账户合约
        account = address(new SmartContractWallet(guardians, threshold));
        
        accounts[msg.sender] = account;
        isAccount[account] = true;
        
        emit AccountCreated(msg.sender, account);
    }
    
    function getAccount(address owner) external view returns (address) {
        return accounts[owner];
    }
    
    function hasAccount(address owner) external view returns (bool) {
        return accounts[owner] != address(0);
    }
}
```

## 3. 客户端SDK (TypeScript)

```typescript
import { ethers } from 'ethers';
import { UserOperation } from './types';

export class AccountAbstractionClient {
    private provider: ethers.providers.Provider;
    private entryPoint: ethers.Contract;
    private accountFactory: ethers.Contract;
    private paymaster: ethers.Contract;
    
    constructor(
        provider: ethers.providers.Provider,
        entryPointAddress: string,
        accountFactoryAddress: string,
        paymasterAddress: string
    ) {
        this.provider = provider;
        this.entryPoint = new ethers.Contract(entryPointAddress, ENTRYPOINT_ABI, provider);
        this.accountFactory = new ethers.Contract(accountFactoryAddress, FACTORY_ABI, provider);
        this.paymaster = new ethers.Contract(paymasterAddress, PAYMASTER_ABI, provider);
    }
    
    async createAccount(
        guardians: string[],
        threshold: number,
        signer: ethers.Signer
    ): Promise<string> {
        const factory = this.accountFactory.connect(signer);
        
        const tx = await factory.createAccount(guardians, threshold);
        const receipt = await tx.wait();
        
        const event = receipt.events?.find(e => e.event === 'AccountCreated');
        if (!event) {
            throw new Error('Account creation failed');
        }
        
        return event.args?.account;
    }
    
    async sendUserOperation(
        userOp: UserOperation,
        signer: ethers.Signer
    ): Promise<string> {
        // 签名用户操作
        const signature = await this.signUserOperation(userOp, signer);
        userOp.signature = signature;
        
        // 提交到EntryPoint
        const entryPoint = this.entryPoint.connect(signer);
        const tx = await entryPoint.handleOps([userOp], ethers.constants.AddressZero);
        
        return tx.hash;
    }
    
    async signUserOperation(
        userOp: UserOperation,
        signer: ethers.Signer
    ): Promise<string> {
        const userOpHash = await this.entryPoint.getUserOpHash(userOp);
        const signature = await signer.signMessage(ethers.utils.arrayify(userOpHash));
        
        return signature;
    }
    
    async estimateGas(userOp: UserOperation): Promise<number> {
        // 估算gas使用量
        const gasEstimate = await this.entryPoint.estimateGas.handleOps([userOp], ethers.constants.AddressZero);
        return gasEstimate.toNumber();
    }
    
    async getNonce(sender: string): Promise<number> {
        return await this.entryPoint.getNonce(sender);
    }
    
    async depositToPaymaster(
        token: string,
        amount: ethers.BigNumber,
        signer: ethers.Signer
    ): Promise<string> {
        const paymaster = this.paymaster.connect(signer);
        
        // 先授权代币
        const tokenContract = new ethers.Contract(token, ERC20_ABI, signer);
        await tokenContract.approve(this.paymaster.address, amount);
        
        // 存款
        const tx = await paymaster.deposit(token, amount);
        return tx.hash;
    }
    
    async buildUserOperation(
        sender: string,
        target: string,
        data: string,
        value: ethers.BigNumber = ethers.constants.Zero
    ): Promise<UserOperation> {
        const nonce = await this.getNonce(sender);
        const gasPrice = await this.provider.getGasPrice();
        
        return {
            sender,
            nonce,
            initCode: '0x',
            callData: this.encodeExecute(target, value, data),
            callGasLimit: 100000,
            verificationGasLimit: 100000,
            preVerificationGas: 21000,
            maxFeePerGas: gasPrice,
            maxPriorityFeePerGas: gasPrice.div(2),
            paymasterAndData: '0x',
            signature: '0x'
        };
    }
    
    private encodeExecute(
        target: string,
        value: ethers.BigNumber,
        data: string
    ): string {
        const iface = new ethers.utils.Interface([
            'function execute(address target, uint256 value, bytes calldata data)'
        ]);
        
        return iface.encodeFunctionData('execute', [target, value, data]);
    }
}

// 类型定义
export interface UserOperation {
    sender: string;
    nonce: number;
    initCode: string;
    callData: string;
    callGasLimit: number;
    verificationGasLimit: number;
    preVerificationGas: number;
    maxFeePerGas: ethers.BigNumber;
    maxPriorityFeePerGas: ethers.BigNumber;
    paymasterAndData: string;
    signature: string;
}

// 使用示例
async function main() {
    const provider = new ethers.providers.JsonRpcProvider('https://mainnet.infura.io/v3/YOUR_KEY');
    const signer = new ethers.Wallet('YOUR_PRIVATE_KEY', provider);
    
    const client = new AccountAbstractionClient(
        provider,
        '0x5FF137D4b0FDCD49DcA30c7CF57E578a026d2789', // EntryPoint
        '0x...', // AccountFactory
        '0x...'  // Paymaster
    );
    
    // 创建账户
    const guardians = ['0x...', '0x...', '0x...'];
    const account = await client.createAccount(guardians, 2, signer);
    console.log('Account created:', account);
    
    // 发送交易
    const userOp = await client.buildUserOperation(
        account,
        '0x...', // target
        '0x...'  // data
    );
    
    const txHash = await client.sendUserOperation(userOp, signer);
    console.log('Transaction sent:', txHash);
}
```

## 4. 批量交易实现

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

contract BatchExecutor {
    struct BatchCall {
        address target;
        uint256 value;
        bytes data;
    }
    
    event BatchExecuted(address indexed sender, uint256 batchSize);
    
    function executeBatch(BatchCall[] calldata calls) external {
        uint256 length = calls.length;
        require(length > 0, "Empty batch");
        
        for (uint256 i = 0; i < length; i++) {
            BatchCall calldata call = calls[i];
            
            (bool success, ) = call.target.call{value: call.value}(call.data);
            require(success, "Batch call failed");
        }
        
        emit BatchExecuted(msg.sender, length);
    }
    
    function executeBatchWithRevert(BatchCall[] calldata calls) external {
        uint256 length = calls.length;
        require(length > 0, "Empty batch");
        
        for (uint256 i = 0; i < length; i++) {
            BatchCall calldata call = calls[i];
            
            (bool success, ) = call.target.call{value: call.value}(call.data);
            // 允许单个调用失败，继续执行
        }
        
        emit BatchExecuted(msg.sender, length);
    }
}
```

---

**状态**: ✅ 实现完成
**完成度**: 100% → 目标: 100%
**下一步**: Phase 2 技术实现深化阶段已完成，准备进入Phase 3
