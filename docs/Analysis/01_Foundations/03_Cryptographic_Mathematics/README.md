# 密码学数学基础

## 概述

密码学数学基础为Web3技术提供了核心的安全保障，包括哈希函数、数字签名、零知识证明、多方安全计算等。本文档建立了完整的密码学数学理论体系，为区块链、智能合约、隐私保护等Web3核心技术提供数学支撑。

## 目录

1. [哈希函数理论](#1-哈希函数理论)
2. [数字签名理论](#2-数字签名理论)
3. [零知识证明理论](#3-零知识证明理论)
4. [多方安全计算](#4-多方安全计算)
5. [同态加密理论](#5-同态加密理论)
6. [在Web3中的应用](#6-在web3中的应用)

## 1. 哈希函数理论

### 1.1 哈希函数定义

**定义 1.1 (哈希函数)**
哈希函数 $H: \{0,1\}^* \to \{0,1\}^n$ 是一个将任意长度输入映射到固定长度输出的函数，满足：

1. **确定性**: 相同输入总是产生相同输出
2. **快速计算**: 对于任意输入 $x$，$H(x)$ 可以快速计算
3. **抗碰撞性**: 找到 $x \neq y$ 使得 $H(x) = H(y)$ 在计算上不可行

**定义 1.2 (抗第二原像性)**
哈希函数 $H$ 具有抗第二原像性，当且仅当给定 $x$，找到 $y \neq x$ 使得 $H(y) = H(x)$ 在计算上不可行。

**定义 1.3 (单向性)**
哈希函数 $H$ 具有单向性，当且仅当给定 $h$，找到 $x$ 使得 $H(x) = h$ 在计算上不可行。

### 1.2 Merkle树

**定义 1.4 (Merkle树)**
给定交易集合 $TX = \{tx_1, tx_2, \ldots, tx_n\}$，其Merkle树根 $root$ 定义为：

- 如果 $n = 1$，则 $root = Hash(tx_1)$
- 如果 $n > 1$，则将 $TX$ 分为两个大致相等的子集 $TX_L$ 和 $TX_R$，计算它们的Merkle根 $root_L$ 和 $root_R$，然后 $root = Hash(root_L || root_R)$

**定理 1.1 (Merkle树验证效率)**
在包含 $n$ 个交易的区块中，使用Merkle树可以在 $O(\log n)$ 时间和空间复杂度内验证特定交易的包含性。

**证明**：
在Merkle树中，验证交易包含性只需要提供从叶节点到根的路径上的所有兄弟节点哈希。在平衡的Merkle树中，这条路径长度为 $\log_2 n$，因此需要 $\log_2 n$ 个哈希值和 $\log_2 n$ 次哈希计算，复杂度为 $O(\log n)$。■

### 1.3 哈希函数实现

```rust
use sha2::{Sha256, Digest};
use std::collections::HashMap;

pub struct MerkleTree {
    root: [u8; 32],
    leaves: Vec<[u8; 32]>,
    nodes: HashMap<usize, [u8; 32]>,
}

impl MerkleTree {
    pub fn new(transactions: Vec<Vec<u8>>) -> Self {
        let leaves: Vec<[u8; 32]> = transactions
            .iter()
            .map(|tx| Self::hash(tx))
            .collect();
        
        let root = Self::build_tree(&leaves);
        let nodes = HashMap::new(); // 简化实现
        
        Self { root, leaves, nodes }
    }
    
    pub fn root(&self) -> [u8; 32] {
        self.root
    }
    
    pub fn verify_inclusion(&self, transaction: &[u8], proof: &MerkleProof) -> bool {
        let leaf_hash = Self::hash(transaction);
        let mut current_hash = leaf_hash;
        
        for (sibling_hash, is_right) in &proof.path {
            current_hash = if *is_right {
                Self::hash(&[&current_hash, sibling_hash].concat())
            } else {
                Self::hash(&[sibling_hash, &current_hash].concat())
            };
        }
        
        current_hash == self.root
    }
    
    fn build_tree(leaves: &[[u8; 32]]) -> [u8; 32] {
        if leaves.len() == 1 {
            return leaves[0];
        }
        
        let mut level = leaves.to_vec();
        while level.len() > 1 {
            let mut next_level = Vec::new();
            for chunk in level.chunks(2) {
                if chunk.len() == 2 {
                    next_level.push(Self::hash(&[&chunk[0], &chunk[1]].concat()));
                } else {
                    next_level.push(chunk[0]);
                }
            }
            level = next_level;
        }
        
        level[0]
    }
    
    fn hash(data: &[u8]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(data);
        hasher.finalize().into()
    }
}

pub struct MerkleProof {
    path: Vec<([u8; 32], bool)>, // (sibling_hash, is_right)
}
```

## 2. 数字签名理论

### 2.1 数字签名定义

**定义 2.1 (数字签名方案)**
数字签名方案是一个三元组 $(\text{Gen}, \text{Sign}, \text{Verify})$：

- $\text{Gen}() \to (pk, sk)$: 生成公钥和私钥
- $\text{Sign}(sk, m) \to \sigma$: 使用私钥对消息签名
- $\text{Verify}(pk, m, \sigma) \to \{0,1\}$: 使用公钥验证签名

**定义 2.2 (数字签名安全性)**
数字签名方案是安全的，当且仅当在适应性选择消息攻击下，攻击者无法伪造有效签名。

### 2.2 ECDSA签名

**算法 2.1 (ECDSA签名算法)**:

```rust
pub struct ECDSA {
    curve: EllipticCurve,
    base_point: Point,
    order: BigUint,
}

impl ECDSA {
    pub fn sign(&self, message: &[u8], private_key: &BigUint) -> Result<Signature, ECDSAError> {
        let message_hash = self.hash_message(message);
        let z = BigUint::from_bytes_be(&message_hash);
        
        loop {
            // 1. 选择随机数k
            let k = self.generate_random_k();
            
            // 2. 计算R = kG
            let r_point = self.curve.scalar_multiply(&k, &self.base_point);
            let r = self.point_to_integer(&r_point)?;
            
            if r == BigUint::zero() {
                continue;
            }
            
            // 3. 计算s = k^(-1)(z + rd) mod n
            let k_inv = self.modular_inverse(&k, &self.order)?;
            let rd = (r * private_key) % &self.order;
            let z_plus_rd = (z + rd) % &self.order;
            let s = (k_inv * z_plus_rd) % &self.order;
            
            if s == BigUint::zero() {
                continue;
            }
            
            return Ok(Signature { r, s });
        }
    }
    
    pub fn verify(&self, message: &[u8], signature: &Signature, public_key: &Point) -> bool {
        let message_hash = self.hash_message(message);
        let z = BigUint::from_bytes_be(&message_hash);
        
        // 1. 计算w = s^(-1) mod n
        let w = match self.modular_inverse(&signature.s, &self.order) {
            Ok(w) => w,
            Err(_) => return false,
        };
        
        // 2. 计算u1 = zw mod n, u2 = rw mod n
        let u1 = (z * &w) % &self.order;
        let u2 = (&signature.r * &w) % &self.order;
        
        // 3. 计算P = u1G + u2Q
        let p1 = self.curve.scalar_multiply(&u1, &self.base_point);
        let p2 = self.curve.scalar_multiply(&u2, public_key);
        let p = self.curve.add_points(&p1, &p2);
        
        // 4. 验证r = x(P) mod n
        if let Point::Finite(x, _) = p {
            let x_int = self.point_to_integer(&Point::Finite(x, FieldElement::zero(1)))?;
            let r_prime = x_int % &self.order;
            Ok(r_prime == signature.r)
        } else {
            Ok(false)
        }
    }
}

#[derive(Debug, Clone)]
pub struct Signature {
    r: BigUint,
    s: BigUint,
}
```

## 3. 零知识证明理论

### 3.1 零知识证明定义

**定义 3.1 (零知识证明系统)**
零知识证明系统是一个三元组 $(P, V, \mathcal{R})$，其中：

- $P$ 是证明者算法
- $V$ 是验证者算法
- $\mathcal{R}$ 是关系集合

**定义 3.2 (零知识性质)**
零知识证明系统具有零知识性质，当且仅当验证者除了知道陈述为真外，无法获得任何其他信息。

### 3.2 zk-SNARK

**算法 3.1 (zk-SNARK构造)**:

```rust
pub struct ZkSNARK {
    proving_key: ProvingKey,
    verification_key: VerificationKey,
}

impl ZkSNARK {
    pub fn setup(circuit: &Circuit) -> (ProvingKey, VerificationKey) {
        // 1. 生成随机参数
        let alpha = FieldElement::random();
        let beta = FieldElement::random();
        let gamma = FieldElement::random();
        let delta = FieldElement::random();
        
        // 2. 计算可信设置
        let proving_key = Self::compute_proving_key(circuit, &alpha, &beta, &gamma, &delta);
        let verification_key = Self::compute_verification_key(circuit, &alpha, &beta, &gamma, &delta);
        
        (proving_key, verification_key)
    }
    
    pub fn prove(&self, witness: &Witness, public_inputs: &[FieldElement]) -> Proof {
        // 1. 计算多项式承诺
        let a_commitment = self.commit_polynomial(&witness.a_poly);
        let b_commitment = self.commit_polynomial(&witness.b_poly);
        let c_commitment = self.commit_polynomial(&witness.c_poly);
        
        // 2. 计算线性组合
        let z_poly = self.compute_linear_combination(&witness);
        let z_commitment = self.commit_polynomial(&z_poly);
        
        // 3. 生成证明
        Proof {
            a_commitment,
            b_commitment,
            c_commitment,
            z_commitment,
            t_commitment: self.commit_t_polynomial(&witness),
        }
    }
    
    pub fn verify(&self, proof: &Proof, public_inputs: &[FieldElement]) -> bool {
        // 1. 验证多项式承诺
        if !self.verify_commitments(proof) {
            return false;
        }
        
        // 2. 验证约束满足
        if !self.verify_constraints(proof, public_inputs) {
            return false;
        }
        
        // 3. 验证知识证明
        self.verify_knowledge_proof(proof)
    }
}

pub struct Proof {
    a_commitment: Commitment,
    b_commitment: Commitment,
    c_commitment: Commitment,
    z_commitment: Commitment,
    t_commitment: Commitment,
}
```

## 4. 多方安全计算

### 4.1 秘密共享

**定义 4.1 (Shamir秘密共享)**
对于秘密 $s$ 和阈值 $t$，Shamir秘密共享生成 $n$ 个份额，使得：

1. 任意 $t$ 个份额可以重构秘密
2. 任意少于 $t$ 个份额无法获得关于秘密的任何信息

**算法 4.1 (Shamir秘密共享)**:

```rust
pub struct ShamirSecretSharing {
    threshold: usize,
    total_shares: usize,
    field: FiniteField,
}

impl ShamirSecretSharing {
    pub fn share(&self, secret: &FieldElement) -> Vec<Share> {
        // 1. 生成随机多项式 f(x) = secret + a1*x + a2*x^2 + ... + a(t-1)*x^(t-1)
        let mut coefficients = vec![secret.clone()];
        for _ in 1..self.threshold {
            coefficients.push(self.field.random_element());
        }
        
        // 2. 计算份额 f(i) for i = 1, 2, ..., n
        let mut shares = Vec::new();
        for i in 1..=self.total_shares {
            let x = FieldElement::from(i as u64);
            let y = self.evaluate_polynomial(&coefficients, &x);
            shares.push(Share { x, y });
        }
        
        shares
    }
    
    pub fn reconstruct(&self, shares: &[Share]) -> Result<FieldElement, ReconstructionError> {
        if shares.len() < self.threshold {
            return Err(ReconstructionError::InsufficientShares);
        }
        
        // 使用拉格朗日插值重构秘密
        let mut secret = FieldElement::zero();
        for i in 0..self.threshold {
            let mut numerator = FieldElement::one();
            let mut denominator = FieldElement::one();
            
            for j in 0..self.threshold {
                if i != j {
                    numerator = self.field.multiply(&numerator, &shares[j].x);
                    let diff = self.field.subtract(&shares[i].x, &shares[j].x);
                    denominator = self.field.multiply(&denominator, &diff);
                }
            }
            
            let lagrange_coeff = self.field.divide(&numerator, &denominator);
            let term = self.field.multiply(&shares[i].y, &lagrange_coeff);
            secret = self.field.add(&secret, &term);
        }
        
        Ok(secret)
    }
    
    fn evaluate_polynomial(&self, coefficients: &[FieldElement], x: &FieldElement) -> FieldElement {
        let mut result = FieldElement::zero();
        let mut power = FieldElement::one();
        
        for coeff in coefficients {
            let term = self.field.multiply(coeff, &power);
            result = self.field.add(&result, &term);
            power = self.field.multiply(&power, x);
        }
        
        result
    }
}

#[derive(Debug, Clone)]
pub struct Share {
    x: FieldElement,
    y: FieldElement,
}
```

## 5. 同态加密理论

### 5.1 同态加密定义

**定义 5.1 (同态加密)**
同态加密方案是一个四元组 $(\text{Gen}, \text{Enc}, \text{Dec}, \text{Eval})$，其中：

- $\text{Gen}() \to (pk, sk)$: 生成密钥对
- $\text{Enc}(pk, m) \to c$: 加密消息
- $\text{Dec}(sk, c) \to m$: 解密密文
- $\text{Eval}(pk, f, c_1, \ldots, c_n) \to c'$: 在密文上计算函数

**定义 5.2 (全同态加密)**
同态加密方案是全同态的，当且仅当可以对任意函数进行同态计算。

### 5.2 部分同态加密

```rust
pub struct PaillierEncryption {
    public_key: PaillierPublicKey,
    private_key: PaillierPrivateKey,
}

impl PaillierEncryption {
    pub fn encrypt(&self, message: &BigUint) -> BigUint {
        let r = self.generate_random_r();
        let g = &self.public_key.g;
        let n = &self.public_key.n;
        let n_squared = n * n;
        
        // c = g^m * r^n mod n^2
        let g_m = g.modpow(message, &n_squared);
        let r_n = r.modpow(n, &n_squared);
        (g_m * r_n) % &n_squared
    }
    
    pub fn decrypt(&self, ciphertext: &BigUint) -> BigUint {
        let n = &self.public_key.n;
        let n_squared = n * n;
        let lambda = &self.private_key.lambda;
        let mu = &self.private_key.mu;
        
        // m = L(c^lambda mod n^2) * mu mod n
        let c_lambda = ciphertext.modpow(lambda, &n_squared);
        let l_value = self.l_function(&c_lambda, n);
        (l_value * mu) % n
    }
    
    pub fn add(&self, c1: &BigUint, c2: &BigUint) -> BigUint {
        let n_squared = &self.public_key.n * &self.public_key.n;
        (c1 * c2) % &n_squared
    }
    
    pub fn multiply(&self, ciphertext: &BigUint, plaintext: &BigUint) -> BigUint {
        ciphertext.modpow(plaintext, &(&self.public_key.n * &self.public_key.n))
    }
    
    fn l_function(&self, x: &BigUint, n: &BigUint) -> BigUint {
        (x - BigUint::one()) / n
    }
    
    fn generate_random_r(&self) -> BigUint {
        // 生成与n互质的随机数
        use rand::Rng;
        let mut rng = rand::thread_rng();
        loop {
            let r = BigUint::from_bytes_be(&rng.gen::<[u8; 32]>());
            if r < &self.public_key.n && r > BigUint::zero() {
                if r.gcd(&self.public_key.n) == BigUint::one() {
                    return r;
                }
            }
        }
    }
}

pub struct PaillierPublicKey {
    n: BigUint,
    g: BigUint,
}

pub struct PaillierPrivateKey {
    lambda: BigUint,
    mu: BigUint,
}
```

## 6. 在Web3中的应用

### 6.1 区块链中的应用

**交易验证**：
- 使用数字签名验证交易有效性
- 使用哈希函数确保数据完整性
- 使用Merkle树高效验证交易包含性

**隐私保护**：
- 使用零知识证明保护用户隐私
- 使用同态加密支持隐私计算
- 使用多方安全计算实现隐私协议

### 6.2 智能合约中的应用

**可验证随机数**：
- 使用VRF生成可验证随机数
- 使用零知识证明验证随机性
- 使用门限签名实现分布式随机数

**隐私智能合约**：
- 使用同态加密实现隐私计算
- 使用零知识证明验证计算正确性
- 使用多方安全计算保护数据隐私

### 6.3 去中心化应用中的应用

**身份验证**：
- 使用零知识证明实现匿名身份验证
- 使用数字签名实现身份证明
- 使用多方安全计算实现身份管理

**数据市场**：
- 使用同态加密保护数据隐私
- 使用零知识证明验证数据质量
- 使用多方安全计算实现数据交易

## 总结

密码学数学基础为Web3技术提供了核心的安全保障：

1. **哈希函数**：为数据完整性提供基础，支持Merkle树等高效数据结构
2. **数字签名**：为身份验证和交易安全提供保障
3. **零知识证明**：为隐私保护提供理论基础
4. **多方安全计算**：为分布式隐私计算提供工具
5. **同态加密**：为隐私计算提供数学基础

这些理论基础确保了Web3系统的安全性和隐私性，为区块链、智能合约、去中心化应用等提供了可靠的技术支撑。

---

**最后更新**: 2024-12-19
**版本**: 1.0
**状态**: 初始构建完成 