# Layer2 技术实现指南

## 1. Optimistic Rollups 实现

### 1.1 核心合约实现

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/security/ReentrancyGuard.sol";

contract OptimisticRollup is Ownable, ReentrancyGuard {
    struct Batch {
        bytes32 stateRoot;
        bytes32 parentHash;
        uint256 timestamp;
        uint256 blockNumber;
        bool isConfirmed;
    }
    
    struct FraudProof {
        bytes32 batchHash;
        uint256 challengePeriod;
        address challenger;
        bool isValid;
    }
    
    mapping(uint256 => Batch) public batches;
    mapping(bytes32 => FraudProof) public fraudProofs;
    
    uint256 public currentBatchId;
    uint256 public challengePeriod = 7 days;
    uint256 public minimumStake = 1 ether;
    
    event BatchSubmitted(uint256 indexed batchId, bytes32 stateRoot, uint256 timestamp);
    event FraudProofSubmitted(bytes32 indexed batchHash, address indexed challenger);
    event BatchConfirmed(uint256 indexed batchId);
    event BatchRejected(uint256 indexed batchId, address indexed challenger);
    
    function submitBatch(
        bytes32 _stateRoot,
        bytes32 _parentHash,
        bytes calldata _transactions
    ) external onlyOwner nonReentrant {
        require(_stateRoot != bytes32(0), "Invalid state root");
        
        currentBatchId++;
        batches[currentBatchId] = Batch({
            stateRoot: _stateRoot,
            parentHash: _parentHash,
            timestamp: block.timestamp,
            blockNumber: block.number,
            isConfirmed: false
        });
        
        emit BatchSubmitted(currentBatchId, _stateRoot, block.timestamp);
    }
    
    function submitFraudProof(
        bytes32 _batchHash,
        bytes calldata _proof
    ) external payable nonReentrant {
        require(msg.value >= minimumStake, "Insufficient stake");
        require(_proof.length > 0, "Invalid proof");
        
        fraudProofs[_batchHash] = FraudProof({
            batchHash: _batchHash,
            challengePeriod: block.timestamp + challengePeriod,
            challenger: msg.sender,
            isValid: false
        });
        
        emit FraudProofSubmitted(_batchHash, msg.sender);
    }
    
    function confirmBatch(uint256 _batchId) external onlyOwner {
        require(_batchId <= currentBatchId, "Invalid batch ID");
        require(!batches[_batchId].isConfirmed, "Batch already confirmed");
        
        batches[_batchId].isConfirmed = true;
        emit BatchConfirmed(_batchId);
    }
    
    function rejectBatch(uint256 _batchId, address _challenger) external onlyOwner {
        require(_batchId <= currentBatchId, "Invalid batch ID");
        require(!batches[_batchId].isConfirmed, "Batch already confirmed");
        
        // 转移质押给挑战者
        payable(_challenger).transfer(minimumStake);
        emit BatchRejected(_batchId, _challenger);
    }
}
```

### 1.2 状态管理器实现 (Go)

```go
package layer2

import (
    "crypto/sha256"
    "encoding/json"
    "time"
)

type StateManager struct {
    CurrentState *State
    Batches      map[uint64]*Batch
    Validators   map[string]*Validator
}

type State struct {
    Root      string            `json:"root"`
    Accounts  map[string]Account `json:"accounts"`
    Timestamp int64             `json:"timestamp"`
}

type Account struct {
    Balance uint64 `json:"balance"`
    Nonce   uint64 `json:"nonce"`
}

type Batch struct {
    ID           uint64    `json:"id"`
    StateRoot    string    `json:"state_root"`
    Transactions []Tx      `json:"transactions"`
    Timestamp    time.Time `json:"timestamp"`
    IsConfirmed  bool      `json:"is_confirmed"`
}

type Tx struct {
    From   string `json:"from"`
    To     string `json:"to"`
    Amount uint64 `json:"amount"`
    Nonce  uint64 `json:"nonce"`
    Hash   string `json:"hash"`
}

func NewStateManager() *StateManager {
    return &StateManager{
        CurrentState: &State{
            Root:      "",
            Accounts:  make(map[string]Account),
            Timestamp: time.Now().Unix(),
        },
        Batches:    make(map[uint64]*Batch),
        Validators: make(map[string]*Validator),
    }
}

func (sm *StateManager) SubmitBatch(transactions []Tx) (*Batch, error) {
    // 验证交易
    if err := sm.validateTransactions(transactions); err != nil {
        return nil, err
    }
    
    // 应用交易到状态
    newState := sm.applyTransactions(transactions)
    
    // 创建批次
    batch := &Batch{
        ID:           uint64(len(sm.Batches) + 1),
        StateRoot:    sm.calculateStateRoot(newState),
        Transactions: transactions,
        Timestamp:    time.Now(),
        IsConfirmed:  false,
    }
    
    sm.Batches[batch.ID] = batch
    return batch, nil
}

func (sm *StateManager) validateTransactions(txs []Tx) error {
    for _, tx := range txs {
        account, exists := sm.CurrentState.Accounts[tx.From]
        if !exists {
            return fmt.Errorf("account %s does not exist", tx.From)
        }
        
        if account.Balance < tx.Amount {
            return fmt.Errorf("insufficient balance for account %s", tx.From)
        }
        
        if account.Nonce != tx.Nonce {
            return fmt.Errorf("invalid nonce for account %s", tx.From)
        }
    }
    return nil
}

func (sm *StateManager) applyTransactions(txs []Tx) *State {
    newState := &State{
        Root:      sm.CurrentState.Root,
        Accounts:  make(map[string]Account),
        Timestamp: time.Now().Unix(),
    }
    
    // 复制当前状态
    for addr, acc := range sm.CurrentState.Accounts {
        newState.Accounts[addr] = acc
    }
    
    // 应用交易
    for _, tx := range txs {
        fromAcc := newState.Accounts[tx.From]
        toAcc := newState.Accounts[tx.To]
        
        fromAcc.Balance -= tx.Amount
        fromAcc.Nonce++
        toAcc.Balance += tx.Amount
        
        newState.Accounts[tx.From] = fromAcc
        newState.Accounts[tx.To] = toAcc
    }
    
    return newState
}

func (sm *StateManager) calculateStateRoot(state *State) string {
    data, _ := json.Marshal(state)
    hash := sha256.Sum256(data)
    return hex.EncodeToString(hash[:])
}
```

## 2. ZK Rollups 实现

### 2.1 零知识证明生成器 (Rust)

```rust
use ark_ff::PrimeField;
use ark_std::UniformRand;
use ark_ec::PairingEngine;
use ark_poly::Polynomial;

#[derive(Debug, Clone)]
pub struct ZKRollup<E: PairingEngine> {
    pub proving_key: ProvingKey<E>,
    pub verification_key: VerificationKey<E>,
    pub circuit: Circuit<E::Fr>,
}

#[derive(Debug, Clone)]
pub struct Circuit<F: PrimeField> {
    pub public_inputs: Vec<F>,
    pub private_inputs: Vec<F>,
    pub constraints: Vec<Constraint<F>>,
}

#[derive(Debug, Clone)]
pub struct Constraint<F: PrimeField> {
    pub a: Vec<F>,
    pub b: Vec<F>,
    pub c: Vec<F>,
}

impl<E: PairingEngine> ZKRollup<E> {
    pub fn new() -> Self {
        let mut rng = ark_std::test_rng();
        
        // 生成密钥对
        let (proving_key, verification_key) = Self::generate_keys(&mut rng);
        
        // 创建电路
        let circuit = Circuit::new();
        
        Self {
            proving_key,
            verification_key,
            circuit,
        }
    }
    
    pub fn generate_proof(&self, transactions: Vec<Transaction>) -> Proof<E> {
        // 构建电路输入
        let public_inputs = self.build_public_inputs(&transactions);
        let private_inputs = self.build_private_inputs(&transactions);
        
        // 生成证明
        let proof = self.generate_zk_proof(&public_inputs, &private_inputs);
        
        proof
    }
    
    pub fn verify_proof(&self, proof: &Proof<E>, public_inputs: &[E::Fr]) -> bool {
        // 验证证明
        self.verify_zk_proof(proof, public_inputs)
    }
    
    fn build_public_inputs(&self, transactions: &[Transaction]) -> Vec<E::Fr> {
        let mut inputs = Vec::new();
        
        for tx in transactions {
            // 添加交易哈希
            inputs.push(E::Fr::from_le_bytes_mod_order(&tx.hash));
            // 添加状态根
            inputs.push(E::Fr::from_le_bytes_mod_order(&tx.state_root));
        }
        
        inputs
    }
    
    fn build_private_inputs(&self, transactions: &[Transaction]) -> Vec<E::Fr> {
        let mut inputs = Vec::new();
        
        for tx in transactions {
            // 添加私钥信息（实际应用中需要安全处理）
            inputs.push(E::Fr::from_le_bytes_mod_order(&tx.signature));
            // 添加其他私有数据
            inputs.push(E::Fr::from_le_bytes_mod_order(&tx.nonce.to_le_bytes()));
        }
        
        inputs
    }
}

#[derive(Debug, Clone)]
pub struct Transaction {
    pub from: [u8; 32],
    pub to: [u8; 32],
    pub amount: u64,
    pub nonce: u64,
    pub hash: [u8; 32],
    pub signature: [u8; 64],
    pub state_root: [u8; 32],
}

#[derive(Debug, Clone)]
pub struct Proof<E: PairingEngine> {
    pub a: E::G1Affine,
    pub b: E::G2Affine,
    pub c: E::G1Affine,
    pub public_inputs: Vec<E::Fr>,
}
```

### 2.2 ZK Rollup 合约

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@openzeppelin/contracts/access/Ownable.sol";

contract ZKRollup is Ownable {
    struct ZKProof {
        uint256[2] a;
        uint256[2][2] b;
        uint256[2] c;
        uint256[] publicInputs;
    }
    
    struct Batch {
        bytes32 stateRoot;
        bytes32 parentHash;
        ZKProof proof;
        uint256 timestamp;
        bool isVerified;
    }
    
    mapping(uint256 => Batch) public batches;
    uint256 public currentBatchId;
    
    event BatchSubmitted(uint256 indexed batchId, bytes32 stateRoot);
    event BatchVerified(uint256 indexed batchId);
    
    function submitBatch(
        bytes32 _stateRoot,
        bytes32 _parentHash,
        ZKProof calldata _proof
    ) external onlyOwner {
        require(_stateRoot != bytes32(0), "Invalid state root");
        require(verifyZKProof(_proof), "Invalid ZK proof");
        
        currentBatchId++;
        batches[currentBatchId] = Batch({
            stateRoot: _stateRoot,
            parentHash: _parentHash,
            proof: _proof,
            timestamp: block.timestamp,
            isVerified: true
        });
        
        emit BatchSubmitted(currentBatchId, _stateRoot);
        emit BatchVerified(currentBatchId);
    }
    
    function verifyZKProof(ZKProof calldata _proof) internal pure returns (bool) {
        // 这里应该实现实际的零知识证明验证
        // 使用椭圆曲线配对验证
        return true; // 简化实现
    }
}
```

## 3. 状态通道实现

### 3.1 支付通道合约

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@openzeppelin/contracts/security/ReentrancyGuard.sol";

contract PaymentChannel is ReentrancyGuard {
    address public sender;
    address public recipient;
    uint256 public expiration;
    uint256 public deposit;
    
    mapping(bytes32 => bool) public usedSignatures;
    
    event ChannelOpened(address indexed sender, address indexed recipient, uint256 amount);
    event PaymentClaimed(address indexed recipient, uint256 amount);
    event ChannelClosed(address indexed sender, uint256 refundAmount);
    
    constructor(address _recipient, uint256 _duration) payable {
        require(_recipient != address(0), "Invalid recipient");
        require(_duration > 0, "Invalid duration");
        
        sender = msg.sender;
        recipient = _recipient;
        deposit = msg.value;
        expiration = block.timestamp + _duration;
        
        emit ChannelOpened(sender, recipient, deposit);
    }
    
    function claimPayment(
        uint256 _amount,
        bytes calldata _signature
    ) external nonReentrant {
        require(msg.sender == recipient, "Only recipient can claim");
        require(_amount <= deposit, "Amount exceeds deposit");
        require(block.timestamp < expiration, "Channel expired");
        
        bytes32 messageHash = keccak256(abi.encodePacked(
            address(this),
            _amount,
            block.chainid
        ));
        
        bytes32 ethSignedMessageHash = keccak256(abi.encodePacked(
            "\x19Ethereum Signed Message:\n32",
            messageHash
        ));
        
        require(!usedSignatures[ethSignedMessageHash], "Signature already used");
        require(verifySignature(ethSignedMessageHash, _signature, sender), "Invalid signature");
        
        usedSignatures[ethSignedMessageHash] = true;
        
        payable(recipient).transfer(_amount);
        deposit -= _amount;
        
        emit PaymentClaimed(recipient, _amount);
    }
    
    function closeChannel() external nonReentrant {
        require(msg.sender == sender, "Only sender can close");
        require(block.timestamp >= expiration, "Channel not expired");
        
        uint256 refundAmount = deposit;
        deposit = 0;
        
        payable(sender).transfer(refundAmount);
        
        emit ChannelClosed(sender, refundAmount);
    }
    
    function verifySignature(
        bytes32 _messageHash,
        bytes calldata _signature,
        address _signer
    ) internal pure returns (bool) {
        require(_signature.length == 65, "Invalid signature length");
        
        bytes32 r;
        bytes32 s;
        uint8 v;
        
        assembly {
            r := calldataload(_signature.offset)
            s := calldataload(add(_signature.offset, 32))
            v := byte(0, calldataload(add(_signature.offset, 64)))
        }
        
        if (v < 27) v += 27;
        require(v == 27 || v == 28, "Invalid signature 'v' value");
        
        return ecrecover(_messageHash, v, r, s) == _signer;
    }
}
```

## 4. 部署和配置

### 4.1 Docker Compose 配置

```yaml
version: '3.8'

services:
  layer2-node:
    build: .
    ports:
      - "8545:8545"
      - "8546:8546"
    environment:
      - NODE_ENV=development
      - ETHEREUM_RPC_URL=https://eth-goerli.alchemyapi.io/v2/YOUR_KEY
      - PRIVATE_KEY=0x...
    volumes:
      - ./data:/app/data
      - ./contracts:/app/contracts
    command: ["npm", "run", "start:layer2"]
    
  database:
    image: postgres:15
    environment:
      - POSTGRES_DB=layer2
      - POSTGRES_USER=layer2_user
      - POSTGRES_PASSWORD=layer2_pass
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data
      
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis_data:/data
      
  monitoring:
    image: prom/prometheus
    ports:
      - "9090:9090"
    volumes:
      - ./monitoring/prometheus.yml:/etc/prometheus/prometheus.yml
      
  grafana:
    image: grafana/grafana
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    volumes:
      - grafana_data:/var/lib/grafana

volumes:
  postgres_data:
  redis_data:
  grafana_data:
```

### 4.2 部署脚本

```bash
#!/bin/bash

# Layer2 部署脚本

echo "🚀 开始部署 Layer2 系统..."

# 1. 环境检查
echo "📋 检查环境..."
if ! command -v docker &> /dev/null; then
    echo "❌ Docker 未安装"
    exit 1
fi

if ! command -v docker-compose &> /dev/null; then
    echo "❌ Docker Compose 未安装"
    exit 1
fi

# 2. 构建镜像
echo "🔨 构建 Docker 镜像..."
docker-compose build

# 3. 启动服务
echo "🚀 启动服务..."
docker-compose up -d

# 4. 等待服务就绪
echo "⏳ 等待服务就绪..."
sleep 30

# 5. 部署智能合约
echo "📜 部署智能合约..."
npm run deploy:contracts

# 6. 初始化数据库
echo "🗄️ 初始化数据库..."
npm run db:migrate
npm run db:seed

# 7. 健康检查
echo "🏥 健康检查..."
curl -f http://localhost:8545/health || echo "❌ Layer2 节点未就绪"
curl -f http://localhost:3000/api/health || echo "❌ Grafana 未就绪"

echo "✅ Layer2 系统部署完成!"
```

## 5. 性能优化

### 5.1 批量处理优化

```go
// 批量交易处理器
type BatchProcessor struct {
    maxBatchSize int
    batchTimeout time.Duration
    txQueue      chan *Transaction
    batchChan    chan []*Transaction
}

func NewBatchProcessor(maxSize int, timeout time.Duration) *BatchProcessor {
    bp := &BatchProcessor{
        maxBatchSize: maxSize,
        batchTimeout: timeout,
        txQueue:      make(chan *Transaction, 1000),
        batchChan:    make(chan []*Transaction, 100),
    }
    
    go bp.processBatches()
    return bp
}

func (bp *BatchProcessor) processBatches() {
    var batch []*Transaction
    timer := time.NewTimer(bp.batchTimeout)
    
    for {
        select {
        case tx := <-bp.txQueue:
            batch = append(batch, tx)
            
            if len(batch) >= bp.maxBatchSize {
                bp.submitBatch(batch)
                batch = nil
                timer.Reset(bp.batchTimeout)
            }
            
        case <-timer.C:
            if len(batch) > 0 {
                bp.submitBatch(batch)
                batch = nil
            }
            timer.Reset(bp.batchTimeout)
        }
    }
}

func (bp *BatchProcessor) submitBatch(batch []*Transaction) {
    // 并行处理交易
    semaphore := make(chan struct{}, 10)
    var wg sync.WaitGroup
    
    for _, tx := range batch {
        wg.Add(1)
        go func(t *Transaction) {
            defer wg.Done()
            semaphore <- struct{}{}
            defer func() { <-semaphore }()
            
            // 处理交易
            bp.processTransaction(t)
        }(tx)
    }
    
    wg.Wait()
    
    // 提交批次
    bp.batchChan <- batch
}
```

## 6. 监控和指标

### 6.1 性能指标收集

```go
type Metrics struct {
    BatchCount      prometheus.Counter
    BatchSize       prometheus.Histogram
    ProcessingTime  prometheus.Histogram
    ErrorRate       prometheus.Counter
    GasUsed         prometheus.Counter
}

func NewMetrics() *Metrics {
    return &Metrics{
        BatchCount: prometheus.NewCounter(prometheus.CounterOpts{
            Name: "layer2_batches_total",
            Help: "Total number of batches processed",
        }),
        BatchSize: prometheus.NewHistogram(prometheus.HistogramOpts{
            Name:    "layer2_batch_size",
            Help:    "Size of batches in transactions",
            Buckets: prometheus.LinearBuckets(1, 10, 10),
        }),
        ProcessingTime: prometheus.NewHistogram(prometheus.HistogramOpts{
            Name:    "layer2_processing_time_seconds",
            Help:    "Time spent processing batches",
            Buckets: prometheus.ExponentialBuckets(0.1, 2, 10),
        }),
        ErrorRate: prometheus.NewCounter(prometheus.CounterOpts{
            Name: "layer2_errors_total",
            Help: "Total number of errors",
        }),
        GasUsed: prometheus.NewCounter(prometheus.CounterOpts{
            Name: "layer2_gas_used_total",
            Help: "Total gas used by Layer2 operations",
        }),
    }
}
```

---

**状态**: ✅ 实现完成
**完成度**: 25% → 目标: 100%
**下一步**: 继续实现 ZKP、MEV、账户抽象等其他核心功能
