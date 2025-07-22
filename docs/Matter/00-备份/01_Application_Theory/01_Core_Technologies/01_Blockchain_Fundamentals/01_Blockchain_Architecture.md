# 区块链架构 (Blockchain Architecture)

## 概述

区块链架构是Web3系统的核心基础设施，通过密码学哈希、默克尔树和分布式共识实现去中心化的信任机制。

## 1. 基本定义

**定义 1.1**（区块链）：
由密码学哈希链接的区块序列，每个区块包含交易数据和前一区块的哈希值。

**定义 1.2**（区块）：
包含区块头和交易列表的数据结构，其中区块头包含前一区块哈希、默克尔根、时间戳等元数据。

**定义 1.3**（默克尔树）：
二叉树结构，叶节点为交易哈希，内部节点为子节点哈希的哈希值。

## 2. 核心定理

**定理 2.1**（区块链不可篡改性）：
在密码学哈希函数安全的前提下，修改历史区块需要重新计算该区块及其后所有区块的哈希值。

**定理 2.2**（默克尔树验证效率）：
在包含$n$个交易的区块中，验证单个交易的存在性只需$O(\log n)$次哈希计算。

## 3. 应用场景

- 加密货币系统的账本结构
- 供应链溯源的数据存储
- 数字身份的证书管理

## 4. Rust代码示例

### 基础区块链实现

```rust
use sha2::{Sha256, Digest};
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Debug, Clone)]
struct Transaction {
    from: String,
    to: String,
    amount: u64,
    timestamp: u64,
}

impl Transaction {
    fn new(from: String, to: String, amount: u64) -> Self {
        Transaction {
            from,
            to,
            amount,
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        }
    }
    
    fn hash(&self) -> String {
        let data = format!("{}{}{}{}", self.from, self.to, self.amount, self.timestamp);
        format!("{:x}", Sha256::digest(data.as_bytes()))
    }
}

#[derive(Debug, Clone)]
struct MerkleTree {
    root: String,
    leaves: Vec<String>,
}

impl MerkleTree {
    fn new(transactions: &[Transaction]) -> Self {
        let leaves: Vec<String> = transactions.iter().map(|tx| tx.hash()).collect();
        let root = Self::calculate_root(&leaves);
        MerkleTree { root, leaves }
    }
    
    fn calculate_root(hashes: &[String]) -> String {
        if hashes.is_empty() {
            return String::new();
        }
        if hashes.len() == 1 {
            return hashes[0].clone();
        }
        
        let mut next_level = Vec::new();
        for chunk in hashes.chunks(2) {
            let combined = if chunk.len() == 2 {
                format!("{}{}", chunk[0], chunk[1])
            } else {
                format!("{}{}", chunk[0], chunk[0])
            };
            next_level.push(format!("{:x}", Sha256::digest(combined.as_bytes())));
        }
        
        Self::calculate_root(&next_level)
    }
}

#[derive(Debug, Clone)]
struct Block {
    index: u64,
    timestamp: u64,
    previous_hash: String,
    merkle_root: String,
    nonce: u64,
    hash: String,
    transactions: Vec<Transaction>,
}

impl Block {
    fn new(index: u64, previous_hash: String, transactions: Vec<Transaction>) -> Self {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let merkle_tree = MerkleTree::new(&transactions);
        let merkle_root = merkle_tree.root;
        
        let mut block = Block {
            index,
            timestamp,
            previous_hash,
            merkle_root,
            nonce: 0,
            hash: String::new(),
            transactions,
        };
        
        block.hash = block.calculate_hash();
        block
    }
    
    fn calculate_hash(&self) -> String {
        let data = format!(
            "{}{}{}{}{}",
            self.index, self.timestamp, self.previous_hash, self.merkle_root, self.nonce
        );
        format!("{:x}", Sha256::digest(data.as_bytes()))
    }
}

struct Blockchain {
    chain: Vec<Block>,
    difficulty: usize,
}

impl Blockchain {
    fn new() -> Self {
        let genesis_block = Block::new(0, "0".to_string(), vec![]);
        Blockchain {
            chain: vec![genesis_block],
            difficulty: 4,
        }
    }
    
    fn add_block(&mut self, transactions: Vec<Transaction>) {
        let previous_hash = self.chain.last().unwrap().hash.clone();
        let index = self.chain.len() as u64;
        let block = Block::new(index, previous_hash, transactions);
        self.chain.push(block);
    }
    
    fn is_valid(&self) -> bool {
        for i in 1..self.chain.len() {
            let current = &self.chain[i];
            let previous = &self.chain[i - 1];
            
            if current.hash != current.calculate_hash() {
                return false;
            }
            
            if current.previous_hash != previous.hash {
                return false;
            }
        }
        true
    }
}

fn main() {
    let mut blockchain = Blockchain::new();
    
    let tx1 = Transaction::new("Alice".to_string(), "Bob".to_string(), 50);
    let tx2 = Transaction::new("Bob".to_string(), "Charlie".to_string(), 25);
    
    blockchain.add_block(vec![tx1, tx2]);
    
    println!("区块链有效性: {}", blockchain.is_valid());
    println!("区块数量: {}", blockchain.chain.len());
}
```

## 相关链接

- [共识机制](02_Consensus_Mechanisms.md)
- [交易处理](03_Transaction_Processing.md)
- [智能合约基础](../02_Smart_Contracts/01_Smart_Contract_Fundamentals.md)
- [区块链基础总览](../)
- [核心技术总览](../../)

---

*区块链架构为Web3系统提供去中心化、不可篡改的数据存储和验证基础。*
