# Web3共识算法：形式化分析与实现

## 目录

1. [共识基础理论](#1-共识基础理论)
2. [工作量证明（PoW）](#2-工作量证明pow)
3. [权益证明（PoS）](#3-权益证明pos)
4. [实用拜占庭容错（PBFT）](#4-实用拜占庭容错pbft)
5. [HotStuff共识](#5-hotstuff共识)
6. [混合共识机制](#6-混合共识机制)
7. [共识安全性分析](#7-共识安全性分析)
8. [性能优化](#8-性能优化)
9. [实现示例](#9-实现示例)
10. [总结与展望](#10-总结与展望)

## 1. 共识基础理论

### 1.1 共识问题定义

**定义 1.1**（拜占庭共识）：在异步网络中，拜占庭共识问题要求满足以下性质：

1. **一致性**：所有诚实节点最终决定相同的值
2. **有效性**：如果所有诚实节点提议相同的值 $v$，则最终决定 $v$
3. **终止性**：所有诚实节点最终做出决定

**定义 1.2**（共识系统）：共识系统 $CS = (N, f, \text{protocol})$ 其中：
- $N$ 是节点集合，$|N| = n$
- $f$ 是最大拜占庭节点数
- $\text{protocol}$ 是共识协议

**定理 1.1**（FLP不可能性）：在异步网络中，即使只有一个节点可能崩溃，也无法实现确定性共识。

**证明**：假设存在确定性共识算法 $A$。考虑执行序列：
1. 所有消息延迟任意长
2. 某个节点 $p$ 崩溃
3. 其他节点无法区分 $p$ 是崩溃还是消息延迟
4. 因此无法确定性地达成共识

### 1.2 网络模型

**定义 1.3**（网络模型）：

1. **同步网络**：消息传递有已知上界
2. **异步网络**：消息传递无上界
3. **部分同步网络**：消息传递有未知上界

**定义 1.4**（故障模型）：

1. **崩溃故障**：节点停止响应
2. **拜占庭故障**：节点可能发送任意消息
3. **遗漏故障**：节点可能丢失消息

## 2. 工作量证明（PoW）

### 2.1 形式化定义

**定义 2.1**（工作量证明）：给定数据 $D$ 和目标难度 $T$，工作量证明是找到一个随机数 $nonce$ 使得：

$$H(D \| nonce) < T$$

其中 $H$ 是密码学哈希函数。

**定义 2.2**（PoW区块链）：PoW区块链 $BC_{PoW} = (B, \text{chain}, \text{difficulty})$ 其中：
- $B$ 是区块集合
- $\text{chain}$ 是最长有效链
- $\text{difficulty}$ 是当前难度

### 2.2 安全性分析

**定理 2.1**（PoW安全性）：假设哈希函数 $H$ 是随机预言机，则攻击者成功执行双花攻击的概率为：

$$P(\text{double-spend}) \leq \left(\frac{q}{p}\right)^k$$

其中 $p$ 是诚实节点算力比例，$q = 1-p$，$k$ 是确认区块数。

**证明**：这可以建模为随机游走过程。设 $Z_t$ 为攻击者链与诚实链的长度差，则：

$$E[Z_{t+1} - Z_t] = q - p < 0$$

应用随机游走理论，攻击者赶上诚实链的概率为 $\left(\frac{q}{p}\right)^k$。

### 2.3 实现示例

```rust
pub struct ProofOfWork {
    difficulty: u64,
    target: U256,
}

impl ProofOfWork {
    pub fn new(difficulty: u64) -> Self {
        let target = Self::calculate_target(difficulty);
        Self { difficulty, target }
    }
    
    fn calculate_target(difficulty: u64) -> U256 {
        // 目标 = 2^(256 - difficulty)
        U256::from(2).pow(U256::from(256 - difficulty))
    }
    
    pub fn mine(&self, block_header: &BlockHeader) -> Result<u64, MiningError> {
        let mut nonce = 0u64;
        let max_nonce = u64::MAX;
        
        while nonce < max_nonce {
            let mut header = block_header.clone();
            header.nonce = nonce;
            
            let hash = self.calculate_hash(&header);
            if self.verify_proof(&hash) {
                return Ok(nonce);
            }
            
            nonce += 1;
        }
        
        Err(MiningError::MaxNonceReached)
    }
    
    fn calculate_hash(&self, header: &BlockHeader) -> Hash {
        let mut hasher = Sha256::new();
        hasher.update(&bincode::serialize(header).unwrap());
        Hash::from_slice(&hasher.finalize())
    }
    
    fn verify_proof(&self, hash: &Hash) -> bool {
        let hash_value = U256::from_big_endian(hash.as_ref());
        hash_value <= self.target
    }
}
```

## 3. 权益证明（PoS）

### 3.1 形式化定义

**定义 3.1**（权益证明）：权益证明系统 $PoS = (V, S, \pi, \text{slashing})$ 其中：
- $V$ 是验证者集合
- $S: V \rightarrow \mathbb{R}^+$ 是质押函数
- $\pi: V \times \mathbb{N} \rightarrow [0,1]$ 是选择概率函数
- $\text{slashing}$ 是罚没函数

**定义 3.2**（验证者选择）：在轮次 $r$ 中，验证者 $v$ 被选中的概率为：

$$P(v \text{ selected in round } r) = \frac{S(v)}{\sum_{v' \in V} S(v')}$$

### 3.2 经济安全性

**定理 3.1**（PoS经济安全性）：如果攻击者控制的质押比例小于 $\frac{1}{3}$，则系统在经济上安全。

**证明**：设攻击者控制的质押比例为 $\alpha < \frac{1}{3}$。攻击者需要：
1. 控制验证者选择
2. 避免被罚没

由于 $\alpha < \frac{1}{3}$，攻击者无法控制验证者选择，且任何恶意行为都会被罚没。

### 3.3 实现示例

```rust
pub struct ProofOfStake {
    validators: HashMap<Address, Validator>,
    total_stake: u64,
    epoch_length: u64,
    current_epoch: u64,
}

#[derive(Clone, Debug)]
pub struct Validator {
    address: Address,
    stake: u64,
    is_active: bool,
    last_active_epoch: u64,
}

impl ProofOfStake {
    pub fn new(epoch_length: u64) -> Self {
        Self {
            validators: HashMap::new(),
            total_stake: 0,
            epoch_length,
            current_epoch: 0,
        }
    }
    
    pub fn add_validator(&mut self, address: Address, stake: u64) {
        let validator = Validator {
            address,
            stake,
            is_active: true,
            last_active_epoch: self.current_epoch,
        };
        
        self.validators.insert(address, validator);
        self.total_stake += stake;
    }
    
    pub fn select_validator(&self, epoch: u64, slot: u64) -> Option<Address> {
        let seed = self.generate_seed(epoch, slot);
        let random_value = self.pseudo_random(seed);
        
        let mut cumulative_stake = 0u64;
        for (address, validator) in &self.validators {
            if !validator.is_active {
                continue;
            }
            
            cumulative_stake += validator.stake;
            if random_value <= cumulative_stake {
                return Some(*address);
            }
        }
        
        None
    }
    
    pub fn slash_validator(&mut self, address: Address, slash_amount: u64) {
        if let Some(validator) = self.validators.get_mut(&address) {
            let actual_slash = std::cmp::min(validator.stake, slash_amount);
            validator.stake -= actual_slash;
            self.total_stake -= actual_slash;
            
            if validator.stake == 0 {
                validator.is_active = false;
            }
        }
    }
    
    fn generate_seed(&self, epoch: u64, slot: u64) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(&epoch.to_be_bytes());
        hasher.update(&slot.to_be_bytes());
        hasher.update(&self.current_epoch.to_be_bytes());
        hasher.finalize().into()
    }
    
    fn pseudo_random(&self, seed: [u8; 32]) -> u64 {
        let mut hasher = Sha256::new();
        hasher.update(&seed);
        let hash = hasher.finalize();
        u64::from_be_bytes(hash[0..8].try_into().unwrap()) % self.total_stake
    }
}
```

## 4. 实用拜占庭容错（PBFT）

### 4.1 形式化定义

**定义 4.1**（PBFT系统）：PBFT系统 $PBFT = (N, f, \text{view}, \text{sequence})$ 其中：
- $|N| = 3f + 1$
- 最多 $f$ 个拜占庭节点
- $\text{view}$ 是当前视图编号
- $\text{sequence}$ 是序列号

**定义 4.2**（PBFT消息类型）：

1. **Pre-prepare**：主节点提议新请求
2. **Prepare**：节点准备接受请求
3. **Commit**：节点提交请求
4. **Reply**：节点回复客户端

### 4.2 算法流程

**算法 4.1**（PBFT共识）：

```rust
pub struct PBFTNode {
    node_id: NodeId,
    view_number: u64,
    sequence_number: u64,
    prepared: HashMap<u64, PreparedCertificate>,
    committed: HashMap<u64, CommittedCertificate>,
    checkpoint_sequence: u64,
    stable_checkpoint: u64,
    primary: NodeId,
}

impl PBFTNode {
    pub async fn propose(&mut self, request: Request) -> Result<(), PBFTError> {
        if self.node_id != self.primary {
            return Err(PBFTError::NotPrimary);
        }
        
        self.sequence_number += 1;
        
        // 1. Pre-prepare阶段
        let pre_prepare = PrePrepare {
            view: self.view_number,
            sequence: self.sequence_number,
            request: request.clone(),
        };
        
        self.broadcast(Message::PrePrepare(pre_prepare)).await?;
        
        // 2. Prepare阶段
        self.collect_prepare_messages(request).await?;
        
        // 3. Commit阶段
        self.collect_commit_messages(request).await?;
        
        // 4. Reply阶段
        self.execute_and_reply(request).await?;
        
        Ok(())
    }
    
    async fn handle_pre_prepare(&mut self, msg: PrePrepare) -> Result<(), PBFTError> {
        // 验证Pre-prepare消息
        if msg.view != self.view_number {
            return Err(PBFTError::InvalidView);
        }
        
        if msg.sequence <= self.sequence_number {
            return Err(PBFTError::InvalidSequence);
        }
        
        // 发送Prepare消息
        let prepare = Prepare {
            view: msg.view,
            sequence: msg.sequence,
            request_hash: hash(&msg.request),
        };
        
        self.broadcast(Message::Prepare(prepare)).await?;
        Ok(())
    }
    
    async fn handle_prepare(&mut self, msg: Prepare) -> Result<(), PBFTError> {
        // 收集Prepare消息
        let certificate = self.prepared.entry(msg.sequence).or_insert_with(PreparedCertificate::new);
        certificate.add_prepare(msg);
        
        // 如果收集到足够的Prepare消息，发送Commit
        if certificate.is_complete() {
            let commit = Commit {
                view: msg.view,
                sequence: msg.sequence,
                request_hash: msg.request_hash,
            };
            
            self.broadcast(Message::Commit(commit)).await?;
        }
        
        Ok(())
    }
    
    async fn handle_commit(&mut self, msg: Commit) -> Result<(), PBFTError> {
        // 收集Commit消息
        let certificate = self.committed.entry(msg.sequence).or_insert_with(CommittedCertificate::new);
        certificate.add_commit(msg);
        
        // 如果收集到足够的Commit消息，执行请求
        if certificate.is_complete() {
            self.execute_request(msg.sequence).await?;
        }
        
        Ok(())
    }
}
```

## 5. HotStuff共识

### 5.1 形式化定义

**定义 5.1**（HotStuff）：HotStuff是线性视图变更的BFT共识算法，具有以下特性：

1. **线性视图变更**：视图变更复杂度为 $O(1)$
2. **三阶段提交**：Prepare → Pre-commit → Commit
3. **流水线处理**：支持并发处理多个区块

**定义 5.2**（Quorum Certificate）：法定人数证书 $QC = (\text{view}, \text{block\_hash}, \text{signatures}, \text{type})$ 其中：
- $\text{view}$ 是视图编号
- $\text{block\_hash}$ 是区块哈希
- $\text{signatures}$ 是签名集合
- $\text{type}$ 是证书类型

### 5.2 算法实现

```rust
pub struct HotStuffNode {
    node_id: NodeId,
    view: u64,
    height: u64,
    block: Option<Block>,
    parent_hash: Hash,
    nodes: Vec<NodeId>,
    state: HotstuffState,
    high_qc: QuorumCertificate,
    locked_qc: QuorumCertificate,
    commit_qc: Option<QuorumCertificate>,
    pending_block: Option<Block>,
    view_timeout: Duration,
    view_timer: Option<Instant>,
}

impl HotStuffNode {
    pub async fn propose(&mut self, transactions: Vec<Transaction>) -> Result<(), HotStuffError> {
        if !self.is_leader() {
            return Err(HotStuffError::NotLeader);
        }
        
        // 创建新区块
        let block = Block {
            height: self.height + 1,
            parent_hash: self.parent_hash,
            transactions,
            view: self.view,
        };
        
        // 发送Prepare消息
        let prepare_msg = HotstuffMessage {
            msg_type: HotstuffMsgType::Prepare,
            view: self.view,
            block: Some(block.clone()),
            qc: Some(self.high_qc.clone()),
            sender: self.node_id,
            signature: self.sign(&block),
        };
        
        self.broadcast(prepare_msg).await?;
        Ok(())
    }
    
    pub async fn handle_prepare(&mut self, msg: HotstuffMessage) -> Result<(), HotStuffError> {
        // 验证Prepare消息
        self.verify_message(&msg)?;
        
        if let Some(block) = &msg.block {
            // 验证区块
            self.verify_block(block)?;
            
            // 更新状态
            self.block = Some(block.clone());
            self.parent_hash = block.hash();
            self.height = block.height;
            
            // 发送Pre-commit消息
            let pre_commit_msg = HotstuffMessage {
                msg_type: HotstuffMsgType::PreCommit,
                view: self.view,
                block: Some(block.clone()),
                qc: Some(self.high_qc.clone()),
                sender: self.node_id,
                signature: self.sign(&block),
            };
            
            self.broadcast(pre_commit_msg).await?;
        }
        
        Ok(())
    }
    
    pub async fn handle_pre_commit(&mut self, msg: HotstuffMessage) -> Result<(), HotStuffError> {
        // 收集Pre-commit消息
        let qc = self.collect_qc(msg.view, QcType::PreCommit, &msg.block)?;
        
        if let Some(qc) = qc {
            self.high_qc = qc.clone();
            
            // 发送Commit消息
            let commit_msg = HotstuffMessage {
                msg_type: HotstuffMsgType::Commit,
                view: self.view,
                block: msg.block.clone(),
                qc: Some(qc),
                sender: self.node_id,
                signature: self.sign(&msg.block.unwrap()),
            };
            
            self.broadcast(commit_msg).await?;
        }
        
        Ok(())
    }
    
    pub async fn handle_commit(&mut self, msg: HotstuffMessage) -> Result<(), HotStuffError> {
        // 收集Commit消息
        let qc = self.collect_qc(msg.view, QcType::Commit, &msg.block)?;
        
        if let Some(qc) = qc {
            // 提交区块
            self.commit_block(&msg.block.unwrap())?;
            self.commit_qc = Some(qc);
            
            // 更新锁定QC
            if self.can_update_locked_qc(&qc) {
                self.locked_qc = qc;
            }
        }
        
        Ok(())
    }
    
    fn is_leader(&self) -> bool {
        self.node_id == self.get_leader(self.view)
    }
    
    fn get_leader(&self, view: u64) -> NodeId {
        self.nodes[view as usize % self.nodes.len()]
    }
    
    fn can_update_locked_qc(&self, qc: &QuorumCertificate) -> bool {
        qc.view > self.locked_qc.view
    }
}
```

## 6. 混合共识机制

### 6.1 混合共识定义

**定义 6.1**（混合共识）：混合共识系统 $HC = (C_1, C_2, \text{combine})$ 其中：
- $C_1$ 是基础共识机制
- $C_2$ 是增强共识机制
- $\text{combine}$ 是组合函数

### 6.2 实现示例

```rust
pub struct HybridConsensus {
    base_consensus: Box<dyn Consensus>,
    enhanced_consensus: Box<dyn Consensus>,
    combination_strategy: CombinationStrategy,
}

impl HybridConsensus {
    pub async fn propose(&mut self, request: Request) -> Result<(), ConsensusError> {
        // 1. 基础共识
        let base_result = self.base_consensus.propose(request.clone()).await?;
        
        // 2. 增强共识
        let enhanced_result = self.enhanced_consensus.propose(request).await?;
        
        // 3. 组合结果
        self.combine_results(base_result, enhanced_result)?;
        
        Ok(())
    }
    
    fn combine_results(&self, base: ConsensusResult, enhanced: ConsensusResult) -> Result<ConsensusResult, ConsensusError> {
        match self.combination_strategy {
            CombinationStrategy::Weighted { base_weight, enhanced_weight } => {
                let combined = base_weight * base + enhanced_weight * enhanced;
                Ok(combined)
            }
            CombinationStrategy::Sequential => {
                if base.is_finalized() {
                    Ok(base)
                } else {
                    Ok(enhanced)
                }
            }
            CombinationStrategy::Parallel => {
                if base.is_finalized() && enhanced.is_finalized() {
                    Ok(base.merge(enhanced))
                } else {
                    Err(ConsensusError::NotFinalized)
                }
            }
        }
    }
}
```

## 7. 共识安全性分析

### 7.1 安全性定义

**定义 7.1**（共识安全性）：共识协议是安全的，当且仅当：

1. **一致性**：$\forall n_i, n_j \in N, \text{decide}_i = \text{decide}_j$
2. **有效性**：如果所有诚实节点提议 $v$，则最终决定 $v$
3. **终止性**：所有诚实节点最终做出决定

### 7.2 攻击分析

**定理 7.1**（51%攻击）：在PoW系统中，如果攻击者控制超过50%的算力，则可以执行双花攻击。

**证明**：攻击者可以：
1. 创建包含双花交易的私有链
2. 在私有链上积累更多工作量
3. 发布私有链，使其成为主链

**定理 7.2**（长程攻击）：在PoS系统中，攻击者可能通过重写历史来执行长程攻击。

**防御机制**：
1. **检查点机制**：定期创建不可逆检查点
2. **弱主观性**：要求新节点信任最近的区块
3. **罚没机制**：惩罚恶意验证者

## 8. 性能优化

### 8.1 并行处理

**定理 8.1**（并行共识加速比）：对于可并行化比例 $p$ 的共识任务，最大加速比为：

$$S = \frac{1}{1-p + \frac{p}{n}}$$

其中 $n$ 是处理器数量。

### 8.2 批量处理

```rust
pub struct BatchConsensus {
    batch_size: usize,
    batch_timeout: Duration,
    pending_requests: VecDeque<Request>,
    batch_timer: Option<Instant>,
}

impl BatchConsensus {
    pub async fn add_request(&mut self, request: Request) -> Result<(), ConsensusError> {
        self.pending_requests.push_back(request);
        
        // 检查是否应该创建新批次
        if self.pending_requests.len() >= self.batch_size {
            self.create_batch().await?;
        } else if self.batch_timer.is_none() {
            // 启动批次计时器
            self.batch_timer = Some(Instant::now());
        }
        
        Ok(())
    }
    
    async fn create_batch(&mut self) -> Result<(), ConsensusError> {
        let batch: Vec<Request> = self.pending_requests.drain(..self.batch_size).collect();
        
        // 执行共识
        self.consensus.propose_batch(batch).await?;
        
        // 重置计时器
        self.batch_timer = None;
        
        Ok(())
    }
    
    pub async fn check_timeout(&mut self) -> Result<(), ConsensusError> {
        if let Some(timer) = self.batch_timer {
            if timer.elapsed() >= self.batch_timeout {
                self.create_batch().await?;
            }
        }
        Ok(())
    }
}
```

## 9. 实现示例

### 9.1 共识管理器

```rust
pub struct ConsensusManager {
    consensus_type: ConsensusType,
    pow_consensus: Option<ProofOfWork>,
    pos_consensus: Option<ProofOfStake>,
    pbft_consensus: Option<PBFTNode>,
    hotstuff_consensus: Option<HotStuffNode>,
    hybrid_consensus: Option<HybridConsensus>,
}

impl ConsensusManager {
    pub async fn new(config: ConsensusConfig) -> Result<Self, ConsensusError> {
        let mut manager = Self {
            consensus_type: config.consensus_type,
            pow_consensus: None,
            pos_consensus: None,
            pbft_consensus: None,
            hotstuff_consensus: None,
            hybrid_consensus: None,
        };
        
        match config.consensus_type {
            ConsensusType::ProofOfWork => {
                manager.pow_consensus = Some(ProofOfWork::new(config.pow_config));
            }
            ConsensusType::ProofOfStake => {
                manager.pos_consensus = Some(ProofOfStake::new(config.pos_config));
            }
            ConsensusType::PBFT => {
                manager.pbft_consensus = Some(PBFTNode::new(config.pbft_config));
            }
            ConsensusType::HotStuff => {
                manager.hotstuff_consensus = Some(HotStuffNode::new(config.hotstuff_config));
            }
            ConsensusType::Hybrid => {
                manager.hybrid_consensus = Some(HybridConsensus::new(config.hybrid_config));
            }
        }
        
        Ok(manager)
    }
    
    pub async fn propose(&mut self, request: Request) -> Result<(), ConsensusError> {
        match self.consensus_type {
            ConsensusType::ProofOfWork => {
                if let Some(ref mut pow) = self.pow_consensus {
                    pow.propose(request).await
                } else {
                    Err(ConsensusError::NotInitialized)
                }
            }
            ConsensusType::ProofOfStake => {
                if let Some(ref mut pos) = self.pos_consensus {
                    pos.propose(request).await
                } else {
                    Err(ConsensusError::NotInitialized)
                }
            }
            ConsensusType::PBFT => {
                if let Some(ref mut pbft) = self.pbft_consensus {
                    pbft.propose(request).await
                } else {
                    Err(ConsensusError::NotInitialized)
                }
            }
            ConsensusType::HotStuff => {
                if let Some(ref mut hotstuff) = self.hotstuff_consensus {
                    hotstuff.propose(request).await
                } else {
                    Err(ConsensusError::NotInitialized)
                }
            }
            ConsensusType::Hybrid => {
                if let Some(ref mut hybrid) = self.hybrid_consensus {
                    hybrid.propose(request).await
                } else {
                    Err(ConsensusError::NotInitialized)
                }
            }
        }
    }
}
```

### 9.2 共识测试框架

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_pow_consensus() {
        let mut pow = ProofOfWork::new(4);
        let block_header = BlockHeader::new(1, Hash::default(), 0, 0, Hash::default());
        
        let nonce = pow.mine(&block_header).await.unwrap();
        assert!(nonce > 0);
        
        let mut header = block_header.clone();
        header.nonce = nonce;
        assert!(pow.verify_proof(&pow.calculate_hash(&header)));
    }
    
    #[tokio::test]
    async fn test_pos_consensus() {
        let mut pos = ProofOfStake::new(100);
        
        // 添加验证者
        pos.add_validator(Address::random(), 1000);
        pos.add_validator(Address::random(), 2000);
        pos.add_validator(Address::random(), 3000);
        
        // 测试验证者选择
        let validator = pos.select_validator(1, 1);
        assert!(validator.is_some());
        
        // 测试罚没
        pos.slash_validator(validator.unwrap(), 500);
        assert_eq!(pos.total_stake, 5500);
    }
    
    #[tokio::test]
    async fn test_pbft_consensus() {
        let mut pbft = PBFTNode::new(PBFTConfig::default());
        let request = Request::new(b"test data".to_vec());
        
        let result = pbft.propose(request).await;
        assert!(result.is_ok());
    }
}
```

## 10. 总结与展望

### 10.1 共识算法比较

| 算法 | 安全性 | 性能 | 去中心化 | 能源效率 |
|------|--------|------|----------|----------|
| PoW | 高 | 低 | 高 | 低 |
| PoS | 高 | 中 | 中 | 高 |
| PBFT | 高 | 高 | 低 | 高 |
| HotStuff | 高 | 高 | 低 | 高 |

### 10.2 未来发展方向

1. **可扩展性**：通过分片和Layer 2提高吞吐量
2. **互操作性**：实现不同共识机制间的互操作
3. **量子抗性**：开发抗量子计算的共识算法
4. **形式化验证**：使用形式化方法验证共识协议

### 10.3 研究挑战

1. **三元悖论**：去中心化、安全性、可扩展性的权衡
2. **网络效应**：共识机制的网络效应和路径依赖
3. **治理机制**：共识参数的动态调整和治理
4. **隐私保护**：在共识中保护交易隐私

---

## 参考文献

1. Nakamoto, S. (2008). Bitcoin: A peer-to-peer electronic cash system.
2. Castro, M., & Liskov, B. (1999). Practical Byzantine fault tolerance.
3. Yin, M., et al. (2019). HotStuff: BFT consensus with linear view change and responsive responsiveness.
4. Buterin, V., & Griffith, V. (2017). Casper the friendly finality gadget.
5. Kiayias, A., et al. (2017). Ouroboros: A provably secure proof-of-stake blockchain protocol. 