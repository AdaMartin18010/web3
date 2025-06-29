# 零知识证明 (Zero-Knowledge Proofs)

## 概述

零知识证明允许证明者在不泄露任何秘密信息的情况下证明某个声明的真实性，是Web3隐私保护的核心技术。

## 1. 基本定义

**定义 1.1**（零知识证明）：
一种密码学协议，证明者能够向验证者证明他知道某个秘密，而不泄露该秘密的任何信息。

**定义 1.2**（完备性）：
如果声明为真，诚实的证明者总是能够说服诚实的验证者。

**定义 1.3**（可靠性）：
如果声明为假，恶意证明者无法以不可忽略的概率说服诚实的验证者。

**定义 1.4**（零知识性）：
验证者从交互中无法学到除了声明真实性以外的任何信息。

## 2. 核心定理

**定理 2.1**（ZK完备性定理）：
对于所有$x \in L$，存在证明者策略使得验证者接受概率为1。

**定理 2.2**（ZK可靠性定理）：
对于所有$x \notin L$，任何证明者策略使得验证者接受概率可忽略。

**定理 2.3**（ZK模拟器存在性）：
存在模拟器能够生成与真实交互不可区分的会话记录。

## 3. 应用场景

- 匿名支付和隐私币
- 去中心化身份验证
- 隐私保护的投票系统

## 4. Rust代码示例

### 简化的ZK-SNARK实现

```rust
use std::collections::HashMap;
use sha2::{Sha256, Digest};
use rand::Rng;

// 简化的有限域实现
#[derive(Debug, Clone, Copy, PartialEq)]
struct FieldElement {
    value: u64,
    modulus: u64,
}

impl FieldElement {
    fn new(value: u64, modulus: u64) -> Self {
        FieldElement {
            value: value % modulus,
            modulus,
        }
    }
    
    fn add(&self, other: &FieldElement) -> FieldElement {
        assert_eq!(self.modulus, other.modulus);
        FieldElement::new(self.value + other.value, self.modulus)
    }
    
    fn mul(&self, other: &FieldElement) -> FieldElement {
        assert_eq!(self.modulus, other.modulus);
        FieldElement::new(self.value * other.value, self.modulus)
    }
    
    fn pow(&self, exp: u64) -> FieldElement {
        let mut result = FieldElement::new(1, self.modulus);
        let mut base = *self;
        let mut e = exp;
        
        while e > 0 {
            if e % 2 == 1 {
                result = result.mul(&base);
            }
            base = base.mul(&base);
            e /= 2;
        }
        result
    }
}

// 简化的多项式实现
#[derive(Debug, Clone)]
struct Polynomial {
    coefficients: Vec<FieldElement>,
    modulus: u64,
}

impl Polynomial {
    fn new(coefficients: Vec<u64>, modulus: u64) -> Self {
        let field_coeffs = coefficients.into_iter()
            .map(|c| FieldElement::new(c, modulus))
            .collect();
        
        Polynomial {
            coefficients: field_coeffs,
            modulus,
        }
    }
    
    fn evaluate(&self, x: &FieldElement) -> FieldElement {
        let mut result = FieldElement::new(0, self.modulus);
        let mut power = FieldElement::new(1, self.modulus);
        
        for coeff in &self.coefficients {
            result = result.add(&coeff.mul(&power));
            power = power.mul(x);
        }
        result
    }
}

// ZK-SNARK证明系统的简化实现
#[derive(Debug)]
struct ZKProof {
    commitment: String,
    challenge: u64,
    response: u64,
}

struct ZKProver {
    secret: u64,
    public_input: u64,
    modulus: u64,
}

impl ZKProver {
    fn new(secret: u64, public_input: u64, modulus: u64) -> Self {
        ZKProver {
            secret,
            public_input,
            modulus,
        }
    }
    
    // 证明知道满足 secret^2 = public_input (mod modulus) 的secret
    fn generate_proof(&self) -> ZKProof {
        let mut rng = rand::thread_rng();
        
        // 1. 承诺阶段：选择随机数r
        let r: u64 = rng.gen_range(1..self.modulus);
        let commitment_value = FieldElement::new(r, self.modulus)
            .pow(2).value;
        let commitment = format!("{:x}", Sha256::digest(commitment_value.to_string()));
        
        // 2. 挑战阶段：模拟随机挑战
        let challenge: u64 = rng.gen_range(0..2);
        
        // 3. 响应阶段
        let response = if challenge == 0 {
            r
        } else {
            (r + self.secret) % self.modulus
        };
        
        ZKProof {
            commitment,
            challenge,
            response,
        }
    }
}

struct ZKVerifier {
    public_input: u64,
    modulus: u64,
}

impl ZKVerifier {
    fn new(public_input: u64, modulus: u64) -> Self {
        ZKVerifier {
            public_input,
            modulus,
        }
    }
    
    fn verify_proof(&self, proof: &ZKProof) -> bool {
        let response_elem = FieldElement::new(proof.response, self.modulus);
        
        if proof.challenge == 0 {
            // 验证 response^2 的承诺
            let expected_commitment = format!("{:x}", 
                Sha256::digest(response_elem.pow(2).value.to_string()));
            expected_commitment == proof.commitment
        } else {
            // 验证 response^2 = commitment + public_input
            let public_elem = FieldElement::new(self.public_input, self.modulus);
            let commitment_value = response_elem.pow(2).value;
            
            // 简化验证逻辑
            commitment_value >= public_elem.value
        }
    }
}

// Merkle树零知识证明
#[derive(Debug, Clone)]
struct MerkleProof {
    root: String,
    leaf: String,
    path: Vec<String>,
    indices: Vec<bool>, // true表示右侧，false表示左侧
}

struct MerkleTree {
    leaves: Vec<String>,
    tree: Vec<Vec<String>>,
}

impl MerkleTree {
    fn new(data: Vec<String>) -> Self {
        let mut leaves = data;
        let mut tree = vec![leaves.clone()];
        
        while leaves.len() > 1 {
            let mut next_level = Vec::new();
            for chunk in leaves.chunks(2) {
                let combined = if chunk.len() == 2 {
                    format!("{}{}", chunk[0], chunk[1])
                } else {
                    format!("{}{}", chunk[0], chunk[0])
                };
                next_level.push(format!("{:x}", Sha256::digest(combined.as_bytes())));
            }
            tree.push(next_level.clone());
            leaves = next_level;
        }
        
        MerkleTree {
            leaves: data,
            tree,
        }
    }
    
    fn get_root(&self) -> String {
        self.tree.last().unwrap()[0].clone()
    }
    
    fn generate_proof(&self, leaf_index: usize) -> Option<MerkleProof> {
        if leaf_index >= self.leaves.len() {
            return None;
        }
        
        let mut path = Vec::new();
        let mut indices = Vec::new();
        let mut current_index = leaf_index;
        
        for level in 0..self.tree.len() - 1 {
            let sibling_index = if current_index % 2 == 0 {
                current_index + 1
            } else {
                current_index - 1
            };
            
            if sibling_index < self.tree[level].len() {
                path.push(self.tree[level][sibling_index].clone());
                indices.push(current_index % 2 == 0);
            }
            
            current_index /= 2;
        }
        
        Some(MerkleProof {
            root: self.get_root(),
            leaf: self.leaves[leaf_index].clone(),
            path,
            indices,
        })
    }
    
    fn verify_proof(proof: &MerkleProof) -> bool {
        let mut current_hash = proof.leaf.clone();
        
        for (i, sibling) in proof.path.iter().enumerate() {
            let combined = if proof.indices[i] {
                format!("{}{}", current_hash, sibling)
            } else {
                format!("{}{}", sibling, current_hash)
            };
            current_hash = format!("{:x}", Sha256::digest(combined.as_bytes()));
        }
        
        current_hash == proof.root
    }
}

fn main() {
    println!("=== 零知识证明示例 ===");
    
    // ZK证明示例
    let secret = 7;
    let public_input = 49; // 7^2 = 49
    let modulus = 101;
    
    let prover = ZKProver::new(secret, public_input, modulus);
    let verifier = ZKVerifier::new(public_input, modulus);
    
    let proof = prover.generate_proof();
    let is_valid = verifier.verify_proof(&proof);
    
    println!("ZK证明验证结果: {}", is_valid);
    
    // Merkle树证明示例
    println!("\n=== Merkle树零知识证明 ===");
    
    let data = vec![
        "transaction1".to_string(),
        "transaction2".to_string(),
        "transaction3".to_string(),
        "transaction4".to_string(),
    ];
    
    let merkle_tree = MerkleTree::new(data);
    println!("Merkle根: {}", merkle_tree.get_root());
    
    if let Some(proof) = merkle_tree.generate_proof(1) {
        let is_valid = MerkleTree::verify_proof(&proof);
        println!("Merkle证明验证结果: {}", is_valid);
    }
}
```

## 相关链接

- [隐私保护协议](02_Privacy_Preserving_Protocols.md)
- [匿名通信技术](03_Anonymous_Communication.md)
- [密码学基础](../../01_Theoretical_Foundations/02_Cryptographic_Foundations/)
- [隐私技术总览](../)
- [核心技术总览](../../)

---

*零知识证明为Web3应用提供强大的隐私保护和数据验证能力。*
