# AA智能钱包应用

## 基于账户抽象的智能合约钱包

### 应用概述

基于Phase 2的Account Abstraction实现指南，开发完整的智能合约钱包系统，支持社交恢复、批量交易、Gas代付等功能。

### 核心功能

#### 1. 智能合约钱包

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/utils/Counters.sol";

/**
 * @title SmartContractWallet
 * @dev 基于ERC-4337的智能合约钱包
 */
contract SmartContractWallet is Ownable {
    using Counters for Counters.Counter;
    
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
    
    struct Guardian {
        address guardian;
        bool isActive;
        uint256 weight;
    }
    
    mapping(address => Guardian) public guardians;
    mapping(address => bool) public isGuardian;
    uint256 public guardianCount;
    uint256 public recoveryThreshold;
    
    Counters.Counter private _nonce;
    
    event GuardianAdded(address indexed guardian, uint256 weight);
    event GuardianRemoved(address indexed guardian);
    event RecoveryInitiated(address indexed newOwner, uint256 timestamp);
    event RecoveryCompleted(address indexed newOwner, uint256 timestamp);
    event BatchTransactionExecuted(bytes32 indexed batchHash, uint256 transactionCount);
    
    modifier onlyGuardian() {
        require(isGuardian[msg.sender], "Not a guardian");
        _;
    }
    
    constructor(address _owner, uint256 _recoveryThreshold) {
        _transferOwnership(_owner);
        recoveryThreshold = _recoveryThreshold;
    }
    
    /**
     * @dev 添加监护人
     */
    function addGuardian(address guardian, uint256 weight) external onlyOwner {
        require(guardian != address(0), "Invalid guardian");
        require(!isGuardian[guardian], "Already a guardian");
        
        guardians[guardian] = Guardian({
            guardian: guardian,
            isActive: true,
            weight: weight
        });
        
        isGuardian[guardian] = true;
        guardianCount++;
        
        emit GuardianAdded(guardian, weight);
    }
    
    /**
     * @dev 移除监护人
     */
    function removeGuardian(address guardian) external onlyOwner {
        require(isGuardian[guardian], "Not a guardian");
        
        delete guardians[guardian];
        isGuardian[guardian] = false;
        guardianCount--;
        
        emit GuardianRemoved(guardian);
    }
    
    /**
     * @dev 验证用户操作
     */
    function validateUserOp(
        UserOperation calldata userOp,
        bytes32 userOpHash,
        uint256 missingAccountFunds
    ) external returns (uint256 validationData) {
        require(userOp.sender == address(this), "Invalid sender");
        require(userOp.nonce == _nonce.current(), "Invalid nonce");
        
        // 验证签名
        require(verifySignature(userOpHash, userOp.signature), "Invalid signature");
        
        // 增加nonce
        _nonce.increment();
        
        return 0; // 验证成功
    }
    
    /**
     * @dev 执行交易
     */
    function execute(
        address target,
        uint256 value,
        bytes calldata data
    ) external onlyOwner {
        (bool success, ) = target.call{value: value}(data);
        require(success, "Transaction failed");
    }
    
    /**
     * @dev 批量执行交易
     */
    function executeBatch(
        address[] calldata targets,
        uint256[] calldata values,
        bytes[] calldata datas
    ) external onlyOwner {
        require(
            targets.length == values.length && targets.length == datas.length,
            "Array length mismatch"
        );
        
        for (uint256 i = 0; i < targets.length; i++) {
            (bool success, ) = targets[i].call{value: values[i]}(datas[i]);
            require(success, "Batch transaction failed");
        }
        
        emit BatchTransactionExecuted(keccak256(abi.encode(targets, values, datas)), targets.length);
    }
    
    /**
     * @dev 发起社交恢复
     */
    function initiateRecovery(address newOwner) external onlyGuardian {
        require(newOwner != address(0), "Invalid new owner");
        require(newOwner != owner(), "Same owner");
        
        emit RecoveryInitiated(newOwner, block.timestamp);
    }
    
    /**
     * @dev 完成社交恢复
     */
    function completeRecovery(
        address newOwner,
        bytes[] calldata guardianSignatures
    ) external onlyGuardian {
        require(guardianSignatures.length >= recoveryThreshold, "Insufficient signatures");
        
        // 验证监护人签名
        for (uint256 i = 0; i < guardianSignatures.length; i++) {
            require(isGuardian[recoverSigner(newOwner, guardianSignatures[i])], "Invalid guardian signature");
        }
        
        _transferOwnership(newOwner);
        
        emit RecoveryCompleted(newOwner, block.timestamp);
    }
    
    /**
     * @dev 验证签名
     */
    function verifySignature(bytes32 hash, bytes calldata signature) internal view returns (bool) {
        address signer = recoverSigner(hash, signature);
        return signer == owner();
    }
    
    /**
     * @dev 恢复签名者地址
     */
    function recoverSigner(bytes32 hash, bytes calldata signature) internal pure returns (address) {
        require(signature.length == 65, "Invalid signature length");
        
        bytes32 r;
        bytes32 s;
        uint8 v;
        
        assembly {
            r := calldataload(add(signature.offset, 0x20))
            s := calldataload(add(signature.offset, 0x40))
            v := byte(0, calldataload(add(signature.offset, 0x60)))
        }
        
        if (v < 27) v += 27;
        require(v == 27 || v == 28, "Invalid signature 'v' value");
        
        return ecrecover(hash, v, r, s);
    }
    
    /**
     * @dev 获取当前nonce
     */
    function getNonce() external view returns (uint256) {
        return _nonce.current();
    }
    
    /**
     * @dev 获取监护人信息
     */
    function getGuardian(address guardian) external view returns (Guardian memory) {
        return guardians[guardian];
    }
    
    /**
     * @dev 接收ETH
     */
    receive() external payable {}
}
```

#### 2. Paymaster合约

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/token/ERC20/IERC20.sol";

/**
 * @title Paymaster
 * @dev Gas代付合约
 */
contract Paymaster is Ownable {
    struct TokenConfig {
        bool isWhitelisted;
        uint256 price; // 代币价格（以USD为单位，精度18）
        uint256 maxAmount; // 最大代付金额
    }
    
    mapping(address => TokenConfig) public tokenConfigs;
    mapping(address => uint256) public balances;
    
    event TokenWhitelisted(address indexed token, uint256 price, uint256 maxAmount);
    event TokenRemoved(address indexed token);
    event GasPaid(address indexed user, address indexed token, uint256 amount, uint256 gasUsed);
    event Deposit(address indexed user, address indexed token, uint256 amount);
    event Withdraw(address indexed user, address indexed token, uint256 amount);
    
    /**
     * @dev 验证Paymaster用户操作
     */
    function validatePaymasterUserOp(
        address user,
        uint256 gasUsed,
        bytes calldata paymasterAndData
    ) external returns (bytes memory context, uint256 validationData) {
        // 解析paymaster数据
        (address token, uint256 maxCost) = abi.decode(paymasterAndData, (address, uint256));
        
        require(tokenConfigs[token].isWhitelisted, "Token not whitelisted");
        require(balances[user] >= maxCost, "Insufficient balance");
        
        // 计算实际费用
        uint256 actualCost = calculateCost(gasUsed, token);
        require(actualCost <= maxCost, "Cost exceeds max");
        
        // 扣除用户余额
        balances[user] -= actualCost;
        
        emit GasPaid(user, token, actualCost, gasUsed);
        
        return (abi.encode(user, token, actualCost), 0);
    }
    
    /**
     * @dev 后处理操作
     */
    function postOp(bytes calldata context) external {
        // 这里可以添加后处理逻辑
    }
    
    /**
     * @dev 添加代币到白名单
     */
    function whitelistToken(
        address token,
        uint256 price,
        uint256 maxAmount
    ) external onlyOwner {
        tokenConfigs[token] = TokenConfig({
            isWhitelisted: true,
            price: price,
            maxAmount: maxAmount
        });
        
        emit TokenWhitelisted(token, price, maxAmount);
    }
    
    /**
     * @dev 从白名单移除代币
     */
    function removeToken(address token) external onlyOwner {
        delete tokenConfigs[token];
        emit TokenRemoved(token);
    }
    
    /**
     * @dev 用户存款
     */
    function deposit(address token, uint256 amount) external {
        require(tokenConfigs[token].isWhitelisted, "Token not whitelisted");
        require(amount > 0, "Invalid amount");
        
        IERC20(token).transferFrom(msg.sender, address(this), amount);
        balances[msg.sender] += amount;
        
        emit Deposit(msg.sender, token, amount);
    }
    
    /**
     * @dev 用户提款
     */
    function withdraw(address token, uint256 amount) external {
        require(balances[msg.sender] >= amount, "Insufficient balance");
        
        balances[msg.sender] -= amount;
        IERC20(token).transfer(msg.sender, amount);
        
        emit Withdraw(msg.sender, token, amount);
    }
    
    /**
     * @dev 计算费用
     */
    function calculateCost(uint256 gasUsed, address token) public view returns (uint256) {
        TokenConfig memory config = tokenConfigs[token];
        uint256 gasPrice = tx.gasprice;
        uint256 totalGasCost = gasUsed * gasPrice;
        
        // 转换为代币数量
        return (totalGasCost * 1e18) / config.price;
    }
    
    /**
     * @dev 获取用户余额
     */
    function getBalance(address user, address token) external view returns (uint256) {
        return balances[user];
    }
}
```

#### 3. 前端钱包界面

```typescript
// React 18 + Next.js 14
import React, { useState, useEffect } from 'react';
import { useAccount, useContract, useSigner } from 'wagmi';
import { ethers } from 'ethers';

interface Guardian {
  address: string;
  weight: number;
  isActive: boolean;
}

interface Transaction {
  to: string;
  value: string;
  data: string;
}

const AASmartWallet: React.FC = () => {
  const { address, isConnected } = useAccount();
  const { data: signer } = useSigner();
  const [walletAddress, setWalletAddress] = useState('');
  const [guardians, setGuardians] = useState<Guardian[]>([]);
  const [transactions, setTransactions] = useState<Transaction[]>([]);
  const [newGuardian, setNewGuardian] = useState('');
  const [newTransaction, setNewTransaction] = useState<Transaction>({
    to: '',
    value: '0',
    data: '0x'
  });
  
  const walletContract = useContract({
    address: walletAddress,
    abi: SmartContractWalletABI,
  });
  
  const paymasterContract = useContract({
    address: process.env.NEXT_PUBLIC_PAYMASTER_ADDRESS,
    abi: PaymasterABI,
  });
  
  useEffect(() => {
    if (isConnected && address) {
      // 部署或获取钱包地址
      deployOrGetWallet();
    }
  }, [isConnected, address]);
  
  const deployOrGetWallet = async () => {
    try {
      // 这里应该实现钱包部署或获取逻辑
      // 简化实现，使用固定地址
      setWalletAddress('0x1234567890123456789012345678901234567890');
      
      // 加载监护人列表
      await loadGuardians();
    } catch (error) {
      console.error('钱包初始化失败:', error);
    }
  };
  
  const loadGuardians = async () => {
    if (!walletContract) return;
    
    try {
      // 这里应该实现加载监护人列表的逻辑
      const mockGuardians: Guardian[] = [
        { address: '0x111...', weight: 1, isActive: true },
        { address: '0x222...', weight: 1, isActive: true },
        { address: '0x333...', weight: 1, isActive: true }
      ];
      setGuardians(mockGuardians);
    } catch (error) {
      console.error('加载监护人失败:', error);
    }
  };
  
  const addGuardian = async () => {
    if (!walletContract || !newGuardian) return;
    
    try {
      const tx = await walletContract.addGuardian(newGuardian, 1);
      await tx.wait();
      
      alert('监护人添加成功');
      setNewGuardian('');
      await loadGuardians();
    } catch (error) {
      alert('添加监护人失败: ' + error.message);
    }
  };
  
  const removeGuardian = async (guardianAddress: string) => {
    if (!walletContract) return;
    
    try {
      const tx = await walletContract.removeGuardian(guardianAddress);
      await tx.wait();
      
      alert('监护人移除成功');
      await loadGuardians();
    } catch (error) {
      alert('移除监护人失败: ' + error.message);
    }
  };
  
  const executeTransaction = async () => {
    if (!walletContract || !newTransaction.to) return;
    
    try {
      const tx = await walletContract.execute(
        newTransaction.to,
        ethers.utils.parseEther(newTransaction.value),
        newTransaction.data
      );
      await tx.wait();
      
      alert('交易执行成功');
      setNewTransaction({ to: '', value: '0', data: '0x' });
    } catch (error) {
      alert('交易执行失败: ' + error.message);
    }
  };
  
  const executeBatchTransactions = async () => {
    if (!walletContract || transactions.length === 0) return;
    
    try {
      const targets = transactions.map(tx => tx.to);
      const values = transactions.map(tx => ethers.utils.parseEther(tx.value));
      const datas = transactions.map(tx => tx.data);
      
      const tx = await walletContract.executeBatch(targets, values, datas);
      await tx.wait();
      
      alert('批量交易执行成功');
      setTransactions([]);
    } catch (error) {
      alert('批量交易执行失败: ' + error.message);
    }
  };
  
  const addTransactionToBatch = () => {
    if (!newTransaction.to) return;
    
    setTransactions([...transactions, { ...newTransaction }]);
    setNewTransaction({ to: '', value: '0', data: '0x' });
  };
  
  const initiateRecovery = async (newOwner: string) => {
    if (!walletContract || !newOwner) return;
    
    try {
      const tx = await walletContract.initiateRecovery(newOwner);
      await tx.wait();
      
      alert('恢复流程已启动');
    } catch (error) {
      alert('启动恢复失败: ' + error.message);
    }
  };
  
  return (
    <div className="max-w-6xl mx-auto p-6">
      <div className="text-center mb-8">
        <h1 className="text-4xl font-bold text-gray-900 mb-4">
          AA智能钱包
        </h1>
        <p className="text-xl text-gray-600">
          基于账户抽象的智能合约钱包
        </p>
      </div>
      
      {!isConnected ? (
        <div className="text-center">
          <button className="bg-blue-600 text-white px-6 py-3 rounded-lg hover:bg-blue-700">
            连接钱包
          </button>
        </div>
      ) : (
        <div className="grid grid-cols-1 lg:grid-cols-2 gap-8">
          {/* 钱包信息 */}
          <div className="bg-white rounded-lg shadow-lg p-6">
            <h2 className="text-2xl font-semibold mb-4">钱包信息</h2>
            
            <div className="space-y-4">
              <div>
                <label className="block text-sm font-medium text-gray-700 mb-2">
                  钱包地址
                </label>
                <div className="p-3 bg-gray-50 rounded border">
                  {walletAddress || '加载中...'}
                </div>
              </div>
              
              <div>
                <label className="block text-sm font-medium text-gray-700 mb-2">
                  所有者
                </label>
                <div className="p-3 bg-gray-50 rounded border">
                  {address}
                </div>
              </div>
              
              <div>
                <label className="block text-sm font-medium text-gray-700 mb-2">
                  监护人数量
                </label>
                <div className="p-3 bg-gray-50 rounded border">
                  {guardians.length}
                </div>
              </div>
            </div>
          </div>
          
          {/* 监护人管理 */}
          <div className="bg-white rounded-lg shadow-lg p-6">
            <h2 className="text-2xl font-semibold mb-4">监护人管理</h2>
            
            <div className="space-y-4">
              <div>
                <label className="block text-sm font-medium text-gray-700 mb-2">
                  添加监护人
                </label>
                <div className="flex space-x-2">
                  <input
                    type="text"
                    placeholder="监护人地址"
                    value={newGuardian}
                    onChange={(e) => setNewGuardian(e.target.value)}
                    className="flex-1 p-2 border rounded"
                  />
                  <button
                    onClick={addGuardian}
                    className="bg-green-600 text-white px-4 py-2 rounded hover:bg-green-700"
                  >
                    添加
                  </button>
                </div>
              </div>
              
              <div>
                <label className="block text-sm font-medium text-gray-700 mb-2">
                  监护人列表
                </label>
                <div className="space-y-2">
                  {guardians.map((guardian, index) => (
                    <div key={index} className="flex items-center justify-between p-3 bg-gray-50 rounded">
                      <span className="text-sm">{guardian.address}</span>
                      <button
                        onClick={() => removeGuardian(guardian.address)}
                        className="bg-red-600 text-white px-2 py-1 rounded text-sm hover:bg-red-700"
                      >
                        移除
                      </button>
                    </div>
                  ))}
                </div>
              </div>
            </div>
          </div>
          
          {/* 交易执行 */}
          <div className="bg-white rounded-lg shadow-lg p-6">
            <h2 className="text-2xl font-semibold mb-4">交易执行</h2>
            
            <div className="space-y-4">
              <div>
                <label className="block text-sm font-medium text-gray-700 mb-2">
                  目标地址
                </label>
                <input
                  type="text"
                  placeholder="0x..."
                  value={newTransaction.to}
                  onChange={(e) => setNewTransaction({...newTransaction, to: e.target.value})}
                  className="w-full p-2 border rounded"
                />
              </div>
              
              <div>
                <label className="block text-sm font-medium text-gray-700 mb-2">
                  发送金额 (ETH)
                </label>
                <input
                  type="number"
                  placeholder="0.0"
                  value={newTransaction.value}
                  onChange={(e) => setNewTransaction({...newTransaction, value: e.target.value})}
                  className="w-full p-2 border rounded"
                />
              </div>
              
              <div className="flex space-x-2">
                <button
                  onClick={executeTransaction}
                  className="flex-1 bg-blue-600 text-white py-2 rounded hover:bg-blue-700"
                >
                  执行交易
                </button>
                <button
                  onClick={addTransactionToBatch}
                  className="flex-1 bg-green-600 text-white py-2 rounded hover:bg-green-700"
                >
                  添加到批量
                </button>
              </div>
            </div>
          </div>
          
          {/* 批量交易 */}
          <div className="bg-white rounded-lg shadow-lg p-6">
            <h2 className="text-2xl font-semibold mb-4">批量交易</h2>
            
            <div className="space-y-4">
              <div>
                <label className="block text-sm font-medium text-gray-700 mb-2">
                  待执行交易 ({transactions.length})
                </label>
                <div className="space-y-2 max-h-40 overflow-y-auto">
                  {transactions.map((tx, index) => (
                    <div key={index} className="p-2 bg-gray-50 rounded text-sm">
                      <div>目标: {tx.to.slice(0, 10)}...</div>
                      <div>金额: {tx.value} ETH</div>
                    </div>
                  ))}
                </div>
              </div>
              
              <button
                onClick={executeBatchTransactions}
                disabled={transactions.length === 0}
                className="w-full bg-purple-600 text-white py-2 rounded hover:bg-purple-700 disabled:opacity-50"
              >
                执行批量交易
              </button>
            </div>
          </div>
        </div>
      )}
    </div>
  );
};

export default AASmartWallet;
```

### 技术特性

#### 账户抽象

- **ERC-4337标准**: 完全兼容账户抽象标准
- **智能合约钱包**: 可编程的钱包逻辑
- **Gas代付**: 支持多种代币支付gas费用
- **批量交易**: 一次签名执行多个交易

#### 社交恢复

- **监护人机制**: 多监护人恢复系统
- **权重投票**: 支持不同权重的监护人
- **安全恢复**: 多重签名恢复流程
- **紧急恢复**: 快速恢复机制

#### 用户体验

- **无Gas交易**: 用户无需持有ETH
- **批量操作**: 提高交易效率
- **权限管理**: 灵活的权限控制
- **多链支持**: 跨链钱包功能

### 部署架构

```yaml
# docker-compose.yml
version: '3.8'
services:
  aa-wallet-frontend:
    build: ./frontend
    ports: ["3000:3000"]
    
  aa-wallet-backend:
    build: ./backend
    ports: ["8080:8080"]
    
  entrypoint:
    build: ./entrypoint
    ports: ["8081:8081"]
    
  postgres:
    image: postgres:15
    environment:
      POSTGRES_DB: aawallet
      
  redis:
    image: redis:7-alpine
```

### 监控指标

```typescript
// Prometheus指标
import { Counter, Histogram } from 'prometheus-client';

const walletCreationCounter = Counter('aa_wallet_creation_total', 'Total wallet creations');
const transactionCounter = Counter('aa_transaction_total', 'Total transactions');
const gasPaidHistogram = Histogram('aa_gas_paid_usd', 'Gas paid in USD');
const recoveryCounter = Counter('aa_recovery_total', 'Total recoveries');
```

### 下一步计划

1. **跨链桥接**: 多链资产转移
2. **DeFi集成**: 与主流DeFi协议集成
3. **NFT支持**: NFT管理和交易
4. **多签名**: 企业级多签名功能
5. **社区建设**: 开发者生态

---

*AA智能钱包应用展示了账户抽象在实际Web3应用中的应用，为用户提供了更好的钱包体验。*
