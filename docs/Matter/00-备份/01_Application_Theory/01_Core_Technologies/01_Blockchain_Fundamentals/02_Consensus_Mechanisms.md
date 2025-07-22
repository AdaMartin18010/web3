# 共识机制 (Consensus Mechanisms)

## 概述

共识机制是区块链网络中节点就网络状态达成一致的算法，确保去中心化环境下的数据一致性和网络安全。

## 1. 基本定义

**定义 1.1**（共识机制）：
分布式网络中节点就区块链状态达成一致的协议和算法。

**定义 1.2**（工作量证明 PoW）：
通过计算密码学难题证明计算工作量的共识机制。

**定义 1.3**（权益证明 PoS）：
根据节点持有的代币数量和质押时间确定出块权的共识机制。

## 2. 核心定理

**定理 2.1**（PoW安全性）：
在诚实节点算力占多数的情况下，PoW系统能抵御51%攻击。

**定理 2.2**（PoS最终确定性）：
在超过2/3节点诚实的PoS系统中，已确认的区块具有概率性最终确定性。

**定理 2.3**（共识效率权衡）：
共识机制在去中心化、安全性和可扩展性之间存在不可能三角。

## 3. 应用场景

- Bitcoin的PoW挖矿机制
- Ethereum 2.0的PoS验证
- 联盟链的PBFT共识

## 4. Rust代码示例

### PoW和PoS共识实现

```rust
use sha2::{Sha256, Digest};
use std::time::{SystemTime, UNIX_EPOCH};
use rand::Rng;

trait ConsensusAlgorithm {
    fn validate_block(&self, block: &Block) -> bool;
    fn select_proposer(&self) -> String;
}

#[derive(Debug, Clone)]
struct Block {
    index: u64,
    timestamp: u64,
    previous_hash: String,
    data: String,
    nonce: u64,
    hash: String,
    proposer: String,
}

impl Block {
    fn new(index: u64, previous_hash: String, data: String, proposer: String) -> Self {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let mut block = Block {
            index,
            timestamp,
            previous_hash,
            data,
            nonce: 0,
            hash: String::new(),
            proposer,
        };
        
        block.hash = block.calculate_hash();
        block
    }
    
    fn calculate_hash(&self) -> String {
        let data = format!(
            "{}{}{}{}{}{}",
            self.index, self.timestamp, self.previous_hash, self.data, self.nonce, self.proposer
        );
        format!("{:x}", Sha256::digest(data.as_bytes()))
    }
    
    fn mine_block(&mut self, difficulty: usize) {
        let target = "0".repeat(difficulty);
        while !self.hash.starts_with(&target) {
            self.nonce += 1;
            self.hash = self.calculate_hash();
        }
        println!("区块挖掘完成: {}", self.hash);
    }
}

struct ProofOfWork {
    difficulty: usize,
}

impl ProofOfWork {
    fn new(difficulty: usize) -> Self {
        ProofOfWork { difficulty }
    }
}

impl ConsensusAlgorithm for ProofOfWork {
    fn validate_block(&self, block: &Block) -> bool {
        let target = "0".repeat(self.difficulty);
        block.hash.starts_with(&target) && block.hash == block.calculate_hash()
    }
    
    fn select_proposer(&self) -> String {
        "miner".to_string() // 在PoW中，任何矿工都可以提议区块
    }
}

#[derive(Debug, Clone)]
struct Validator {
    id: String,
    stake: u64,
    age: u64, // 质押时间
}

struct ProofOfStake {
    validators: Vec<Validator>,
    total_stake: u64,
}

impl ProofOfStake {
    fn new(validators: Vec<Validator>) -> Self {
        let total_stake = validators.iter().map(|v| v.stake).sum();
        ProofOfStake {
            validators,
            total_stake,
        }
    }
    
    fn calculate_selection_probability(&self, validator: &Validator) -> f64 {
        (validator.stake as f64 * validator.age as f64) / (self.total_stake as f64)
    }
}

impl ConsensusAlgorithm for ProofOfStake {
    fn validate_block(&self, block: &Block) -> bool {
        // 验证提议者是否有效
        self.validators.iter().any(|v| v.id == block.proposer)
    }
    
    fn select_proposer(&self) -> String {
        let mut rng = rand::thread_rng();
        let random_value: f64 = rng.gen();
        let mut cumulative_probability = 0.0;
        
        for validator in &self.validators {
            cumulative_probability += self.calculate_selection_probability(validator);
            if random_value <= cumulative_probability {
                return validator.id.clone();
            }
        }
        
        // 默认返回第一个验证者
        self.validators[0].id.clone()
    }
}

struct ConsensusEngine<T: ConsensusAlgorithm> {
    algorithm: T,
    chain: Vec<Block>,
}

impl<T: ConsensusAlgorithm> ConsensusEngine<T> {
    fn new(algorithm: T) -> Self {
        let genesis_block = Block::new(
            0,
            "0".to_string(),
            "Genesis Block".to_string(),
            "genesis".to_string(),
        );
        
        ConsensusEngine {
            algorithm,
            chain: vec![genesis_block],
        }
    }
    
    fn add_block(&mut self, data: String) -> bool {
        let proposer = self.algorithm.select_proposer();
        let previous_hash = self.chain.last().unwrap().hash.clone();
        let index = self.chain.len() as u64;
        
        let mut new_block = Block::new(index, previous_hash, data, proposer);
        
        // 根据共识算法验证区块
        if self.algorithm.validate_block(&new_block) {
            self.chain.push(new_block);
            true
        } else {
            false
        }
    }
}

fn main() {
    // PoW示例
    println!("=== 工作量证明 (PoW) ===");
    let pow = ProofOfWork::new(4);
    let mut pow_engine = ConsensusEngine::new(pow);
    
    let mut block = Block::new(
        1,
        pow_engine.chain[0].hash.clone(),
        "PoW交易数据".to_string(),
        "miner1".to_string(),
    );
    block.mine_block(4);
    
    // PoS示例
    println!("\n=== 权益证明 (PoS) ===");
    let validators = vec![
        Validator { id: "validator1".to_string(), stake: 1000, age: 10 },
        Validator { id: "validator2".to_string(), stake: 2000, age: 5 },
        Validator { id: "validator3".to_string(), stake: 1500, age: 8 },
    ];
    
    let pos = ProofOfStake::new(validators);
    let mut pos_engine = ConsensusEngine::new(pos);
    
    for i in 1..=3 {
        let data = format!("PoS交易数据 {}", i);
        let success = pos_engine.add_block(data);
        println!("区块 {} 添加: {}", i, success);
    }
}
```

## 相关链接

- [区块链架构](01_Blockchain_Architecture.md)
- [交易处理](03_Transaction_Processing.md)
- [分布式系统理论](../../01_Theoretical_Foundations/04_Distributed_Systems_Theory/)
- [区块链基础总览](../)
- [核心技术总览](../../)

---

*共识机制为区块链网络提供去中心化的状态一致性和安全性保障。*
