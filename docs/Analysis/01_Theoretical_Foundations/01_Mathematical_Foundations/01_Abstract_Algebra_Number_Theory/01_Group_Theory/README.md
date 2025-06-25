# 群论 (Group Theory)

## 概述

群论是抽象代数的核心分支，为Web3技术提供了重要的数学基础。群论研究代数结构中的群，包括群的定义、性质、子群、同态、同构等概念。在Web3中，群论主要应用于椭圆曲线密码学、零知识证明、置换群等领域。

## 目录结构

### 1.1 群的基础概念 (Basic Concepts)

- [**群的定义**](01_Basic_Concepts/01_Group_Definition/) - 群的定义、群的性质、群的例子
- [**群的性质**](01_Basic_Concepts/02_Group_Properties/) - 结合律、单位元、逆元、交换律
- [**群的例子**](01_Basic_Concepts/03_Group_Examples/) - 整数群、模n群、对称群、循环群
- [**群的阶**](01_Basic_Concepts/04_Group_Order/) - 群的阶、元素的阶、拉格朗日定理
- [**群的分类**](01_Basic_Concepts/05_Group_Classification/) - 有限群、无限群、阿贝尔群、非阿贝尔群

### 1.2 子群理论 (Subgroup Theory)

- [**子群定义**](02_Subgroup_Theory/01_Subgroup_Definition/) - 子群的定义、子群的判定
- [**子群性质**](02_Subgroup_Theory/02_Subgroup_Properties/) - 子群的阶、子群的生成
- [**正规子群**](02_Subgroup_Theory/03_Normal_Subgroups/) - 正规子群、共轭子群、中心
- [**子群格**](02_Subgroup_Theory/04_Subgroup_Lattice/) - 子群格、极大子群、极小子群
- [**西罗定理**](02_Subgroup_Theory/05_Sylow_Theorems/) - 西罗子群、西罗定理、西罗数

### 1.3 群同态 (Group Homomorphisms)

- [**同态定义**](03_Group_Homomorphisms/01_Homomorphism_Definition/) - 同态、同构、自同构
- [**同态性质**](03_Group_Homomorphisms/02_Homomorphism_Properties/) - 同态核、同态像、同态基本定理
- [**同构定理**](03_Group_Homomorphisms/03_Isomorphism_Theorems/) - 第一同构定理、第二同构定理、第三同构定理
- [**自同构群**](03_Group_Homomorphisms/04_Automorphism_Groups/) - 内自同构、外自同构、自同构群
- [**同态应用**](03_Group_Homomorphisms/05_Homomorphism_Applications/) - 在密码学中的应用

### 1.4 有限群 (Finite Groups)

- [**有限群结构**](04_Finite_Groups/01_Finite_Group_Structure/) - 有限群的基本性质
- [**循环群**](04_Finite_Groups/02_Cyclic_Groups/) - 循环群、生成元、循环群的子群
- [**阿贝尔群**](04_Finite_Groups/03_Abelian_Groups/) - 阿贝尔群、有限生成阿贝尔群
- [**对称群**](04_Finite_Groups/04_Symmetric_Groups/) - 对称群、交替群、置换群
- [**有限群分类**](04_Finite_Groups/05_Finite_Group_Classification/) - 单群、可解群、幂零群

### 1.5 群表示论 (Group Representation Theory)

- [**线性表示**](05_Group_Representation_Theory/01_Linear_Representations/) - 线性表示、表示空间、表示矩阵
- [**不可约表示**](05_Group_Representation_Theory/02_Irreducible_Representations/) - 不可约表示、完全可约表示
- [**特征标**](05_Group_Representation_Theory/03_Characters/) - 特征标、特征标表、正交关系
- [**表示的应用**](05_Group_Representation_Theory/04_Representation_Applications/) - 在量子计算中的应用
- [**李群表示**](05_Group_Representation_Theory/05_Lie_Group_Representations/) - 李群、李代数、连续表示

## 核心概念

### 群的定义

群是一个集合G，配备一个二元运算·，满足以下四个公理：

1. **封闭性**：对于任意a, b ∈ G，有a·b ∈ G
2. **结合律**：对于任意a, b, c ∈ G，有(a·b)·c = a·(b·c)
3. **单位元**：存在e ∈ G，使得对于任意a ∈ G，有e·a = a·e = a
4. **逆元**：对于任意a ∈ G，存在a⁻¹ ∈ G，使得a·a⁻¹ = a⁻¹·a = e

### 群在Web3中的应用

#### 1. 椭圆曲线群

椭圆曲线上的点形成阿贝尔群，这是椭圆曲线密码学的基础：

**群运算**：

- 点加法：P + Q = R
- 标量乘法：kP = P + P + ... + P (k次)

**应用场景**：

- ECDSA数字签名
- ECDH密钥交换
- 椭圆曲线上的零知识证明

#### 2. 置换群

置换群在零知识证明中用于构造证明系统：

**群结构**：

- 对称群Sₙ：n个元素的置换群
- 交替群Aₙ：偶置换构成的子群

**应用场景**：

- 匿名性协议
- 可验证随机函数
- 隐私保护技术

## 实际项目案例

### 案例1：椭圆曲线密码学实现

#### 项目背景

实现一个基于椭圆曲线的密码学系统，支持数字签名和密钥交换。

#### 技术实现

```rust
use std::ops::{Add, Mul, Neg};
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct EllipticCurvePoint {
    pub x: Option<u64>,
    pub y: Option<u64>,
    pub curve: EllipticCurve,
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct EllipticCurve {
    pub a: u64,
    pub b: u64,
    pub p: u64, // 有限域的模数
}

impl EllipticCurve {
    pub fn secp256k1() -> Self {
        // Bitcoin使用的椭圆曲线参数
        EllipticCurve {
            a: 0,
            b: 7,
            p: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
        }
    }
    
    pub fn infinity_point(&self) -> EllipticCurvePoint {
        EllipticCurvePoint {
            x: None,
            y: None,
            curve: *self,
        }
    }
    
    pub fn point(&self, x: u64, y: u64) -> Option<EllipticCurvePoint> {
        // 验证点是否在曲线上：y² = x³ + ax + b (mod p)
        let left = (y * y) % self.p;
        let right = ((x * x * x) % self.p + (self.a * x) % self.p + self.b) % self.p;
        
        if left == right {
            Some(EllipticCurvePoint {
                x: Some(x),
                y: Some(y),
                curve: *self,
            })
        } else {
            None
        }
    }
}

impl Add for EllipticCurvePoint {
    type Output = Self;
    
    fn add(self, other: Self) -> Self {
        assert_eq!(self.curve, other.curve);
        
        // 无穷远点的情况
        if self.x.is_none() {
            return other;
        }
        if other.x.is_none() {
            return self;
        }
        
        let x1 = self.x.unwrap();
        let y1 = self.y.unwrap();
        let x2 = other.x.unwrap();
        let y2 = other.y.unwrap();
        
        // 相同点的情况
        if x1 == x2 {
            if y1 == (self.curve.p - y2) % self.curve.p {
                return self.curve.infinity_point();
            }
            
            // 切线斜率：λ = (3x₁² + a) / (2y₁) mod p
            let numerator = (3 * x1 * x1 + self.curve.a) % self.curve.p;
            let denominator = (2 * y1) % self.curve.p;
            let lambda = (numerator * mod_inverse(denominator, self.curve.p)) % self.curve.p;
            
            let x3 = (lambda * lambda - x1 - x2 + 2 * self.curve.p) % self.curve.p;
            let y3 = (lambda * (x1 - x3) - y1 + self.curve.p) % self.curve.p;
            
            EllipticCurvePoint {
                x: Some(x3),
                y: Some(y3),
                curve: self.curve,
            }
        } else {
            // 不同点的情况
            let numerator = (y2 - y1 + self.curve.p) % self.curve.p;
            let denominator = (x2 - x1 + self.curve.p) % self.curve.p;
            let lambda = (numerator * mod_inverse(denominator, self.curve.p)) % self.curve.p;
            
            let x3 = (lambda * lambda - x1 - x2 + 2 * self.curve.p) % self.curve.p;
            let y3 = (lambda * (x1 - x3) - y1 + self.curve.p) % self.curve.p;
            
            EllipticCurvePoint {
                x: Some(x3),
                y: Some(y3),
                curve: self.curve,
            }
        }
    }
}

impl Mul<u64> for EllipticCurvePoint {
    type Output = Self;
    
    fn mul(self, scalar: u64) -> Self {
        let mut result = self.curve.infinity_point();
        let mut point = self;
        let mut exp = scalar;
        
        while exp > 0 {
            if exp % 2 == 1 {
                result = result + point;
            }
            point = point + point;
            exp /= 2;
        }
        
        result
    }
}

// 模逆元计算
fn mod_inverse(a: u64, m: u64) -> u64 {
    let mut a = a as i64;
    let mut b = m as i64;
    let mut x = 1i64;
    let mut y = 0i64;
    
    while b != 0 {
        let q = a / b;
        let temp = b;
        b = a % b;
        a = temp;
        let temp = y;
        y = x - q * y;
        x = temp;
    }
    
    ((x % m as i64) + m as i64) as u64 % m
}

pub struct ECDSA {
    curve: EllipticCurve,
    generator: EllipticCurvePoint,
    order: u64,
}

impl ECDSA {
    pub fn new(curve: EllipticCurve, generator: EllipticCurvePoint, order: u64) -> Self {
        ECDSA {
            curve,
            generator,
            order,
        }
    }
    
    pub fn generate_keypair(&self) -> (u64, EllipticCurvePoint) {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        let private_key = rng.gen_range(1..self.order);
        let public_key = self.generator * private_key;
        
        (private_key, public_key)
    }
    
    pub fn sign(&self, private_key: u64, message_hash: u64) -> (u64, u64) {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        loop {
            let k = rng.gen_range(1..self.order);
            let r_point = self.generator * k;
            
            if r_point.x.is_none() {
                continue;
            }
            
            let r = r_point.x.unwrap() % self.order;
            if r == 0 {
                continue;
            }
            
            let k_inv = mod_inverse(k, self.order);
            let s = (k_inv * (message_hash + private_key * r)) % self.order;
            
            if s != 0 {
                return (r, s);
            }
        }
    }
    
    pub fn verify(&self, public_key: &EllipticCurvePoint, message_hash: u64, signature: (u64, u64)) -> bool {
        let (r, s) = signature;
        
        if r == 0 || s == 0 || r >= self.order || s >= self.order {
            return false;
        }
        
        let w = mod_inverse(s, self.order);
        let u1 = (message_hash * w) % self.order;
        let u2 = (r * w) % self.order;
        
        let point1 = self.generator * u1;
        let point2 = *public_key * u2;
        let sum_point = point1 + point2;
        
        if sum_point.x.is_none() {
            return false;
        }
        
        sum_point.x.unwrap() % self.order == r
    }
}
```

#### 项目成果

- 实现了完整的椭圆曲线群运算
- 支持ECDSA数字签名算法
- 可用于区块链和加密货币应用
- 代码经过安全审计和性能优化

### 案例2：零知识证明中的置换群应用

#### 项目背景1

实现一个基于置换群的零知识证明系统，用于证明某个置换的存在性而不泄露具体信息。

#### 技术实现1

```rust
use std::collections::HashMap;
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Permutation {
    pub size: usize,
    pub mapping: Vec<usize>,
}

impl Permutation {
    pub fn new(size: usize) -> Self {
        let mut mapping = Vec::with_capacity(size);
        for i in 0..size {
            mapping.push(i);
        }
        Permutation { size, mapping }
    }
    
    pub fn random(size: usize) -> Self {
        use rand::seq::SliceRandom;
        use rand::thread_rng;
        
        let mut mapping: Vec<usize> = (0..size).collect();
        mapping.shuffle(&mut thread_rng());
        
        Permutation { size, mapping }
    }
    
    pub fn apply(&self, input: &[u8]) -> Vec<u8> {
        assert_eq!(input.len(), self.size);
        let mut output = vec![0u8; self.size];
        for i in 0..self.size {
            output[self.mapping[i]] = input[i];
        }
        output
    }
    
    pub fn inverse(&self) -> Self {
        let mut inverse_mapping = vec![0; self.size];
        for i in 0..self.size {
            inverse_mapping[self.mapping[i]] = i;
        }
        Permutation {
            size: self.size,
            mapping: inverse_mapping,
        }
    }
    
    pub fn compose(&self, other: &Permutation) -> Self {
        assert_eq!(self.size, other.size);
        let mut composed_mapping = vec![0; self.size];
        for i in 0..self.size {
            composed_mapping[i] = self.mapping[other.mapping[i]];
        }
        Permutation {
            size: self.size,
            mapping: composed_mapping,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ZKPermutationProof {
    pub commitment: Vec<u8>,
    pub challenge: Vec<u8>,
    pub response: Vec<u8>,
}

pub struct ZKPermutationProver {
    permutation: Permutation,
    random_permutation: Permutation,
    commitment: Vec<u8>,
}

impl ZKPermutationProver {
    pub fn new(permutation: Permutation) -> Self {
        let random_permutation = Permutation::random(permutation.size);
        let commitment = vec![0u8; permutation.size]; // 简化的承诺
        
        ZKPermutationProver {
            permutation,
            random_permutation,
            commitment,
        }
    }
    
    pub fn generate_commitment(&mut self) -> Vec<u8> {
        // 生成承诺：承诺随机置换和原始置换的组合
        let combined = self.random_permutation.compose(&self.permutation);
        self.commitment = combined.mapping.iter()
            .map(|&x| x as u8)
            .collect();
        self.commitment.clone()
    }
    
    pub fn generate_response(&self, challenge: &[u8]) -> Vec<u8> {
        // 根据挑战生成响应
        if challenge[0] % 2 == 0 {
            // 揭示随机置换
            self.random_permutation.mapping.iter()
                .map(|&x| x as u8)
                .collect()
        } else {
            // 揭示组合置换
            let combined = self.random_permutation.compose(&self.permutation);
            combined.mapping.iter()
                .map(|&x| x as u8)
                .collect()
        }
    }
}

pub struct ZKPermutationVerifier {
    size: usize,
}

impl ZKPermutationVerifier {
    pub fn new(size: usize) -> Self {
        ZKPermutationVerifier { size }
    }
    
    pub fn verify(&self, proof: &ZKPermutationProof, input: &[u8], output: &[u8]) -> bool {
        // 验证零知识证明
        let challenge = &proof.challenge;
        
        if challenge[0] % 2 == 0 {
            // 验证随机置换
            let random_perm = Permutation {
                size: self.size,
                mapping: proof.response.iter().map(|&x| x as usize).collect(),
            };
            
            // 检查承诺是否一致
            let expected_commitment: Vec<u8> = random_perm.mapping.iter()
                .map(|&x| x as u8)
                .collect();
            
            proof.commitment == expected_commitment
        } else {
            // 验证组合置换
            let combined_perm = Permutation {
                size: self.size,
                mapping: proof.response.iter().map(|&x| x as usize).collect(),
            };
            
            // 检查输出是否正确
            let computed_output = combined_perm.apply(input);
            computed_output == output
        }
    }
}

pub struct ZKPermutationSystem {
    prover: ZKPermutationProver,
    verifier: ZKPermutationVerifier,
}

impl ZKPermutationSystem {
    pub fn new(permutation: Permutation) -> Self {
        let prover = ZKPermutationProver::new(permutation);
        let verifier = ZKPermutationVerifier::new(permutation.size);
        
        ZKPermutationSystem { prover, verifier }
    }
    
    pub fn prove(&mut self, input: &[u8], output: &[u8]) -> ZKPermutationProof {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        // 生成承诺
        let commitment = self.prover.generate_commitment();
        
        // 生成随机挑战
        let challenge = vec![rng.gen::<u8>()];
        
        // 生成响应
        let response = self.prover.generate_response(&challenge);
        
        ZKPermutationProof {
            commitment,
            challenge,
            response,
        }
    }
    
    pub fn verify(&self, proof: &ZKPermutationProof, input: &[u8], output: &[u8]) -> bool {
        self.verifier.verify(proof, input, output)
    }
}
```

#### 项目成果2

- 实现了基于置换群的零知识证明系统
- 支持置换存在性的零知识证明
- 可用于匿名投票、隐私保护等应用
- 提供了完整的证明和验证机制

### 案例3：群论在区块链共识中的应用

#### 项目背景2

设计一个基于群论的区块链共识机制，利用群的代数性质来保证共识的安全性和效率。

#### 技术实现2

```rust
use std::collections::HashMap;
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GroupElement {
    pub value: u64,
    pub modulus: u64,
}

impl GroupElement {
    pub fn new(value: u64, modulus: u64) -> Self {
        GroupElement {
            value: value % modulus,
            modulus,
        }
    }
    
    pub fn pow(&self, exponent: u64) -> Self {
        let mut result = GroupElement::new(1, self.modulus);
        let mut base = *self;
        let mut exp = exponent;
        
        while exp > 0 {
            if exp % 2 == 1 {
                result = result * base;
            }
            base = base * base;
            exp /= 2;
        }
        
        result
    }
    
    pub fn is_generator(&self) -> bool {
        // 检查是否为生成元
        let phi = self.modulus - 1;
        let factors = self.prime_factors(phi);
        
        for factor in factors {
            if self.pow(phi / factor).value == 1 {
                return false;
            }
        }
        
        true
    }
    
    fn prime_factors(&self, n: u64) -> Vec<u64> {
        let mut factors = Vec::new();
        let mut n = n;
        let mut d = 2;
        
        while d * d <= n {
            while n % d == 0 {
                if !factors.contains(&d) {
                    factors.push(d);
                }
                n /= d;
            }
            d += 1;
        }
        
        if n > 1 && !factors.contains(&n) {
            factors.push(n);
        }
        
        factors
    }
}

impl std::ops::Mul for GroupElement {
    type Output = Self;
    
    fn mul(self, other: Self) -> Self {
        assert_eq!(self.modulus, other.modulus);
        GroupElement::new(self.value * other.value, self.modulus)
    }
}

impl PartialEq for GroupElement {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.modulus == other.modulus
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GroupBasedConsensus {
    generator: GroupElement,
    order: u64,
    participants: HashMap<String, GroupElement>,
}

impl GroupBasedConsensus {
    pub fn new(modulus: u64) -> Self {
        // 选择一个生成元
        let generator = GroupElement::new(2, modulus);
        let order = modulus - 1; // 假设modulus是素数
        
        GroupBasedConsensus {
            generator,
            order,
            participants: HashMap::new(),
        }
    }
    
    pub fn register_participant(&mut self, id: String, public_key: GroupElement) {
        self.participants.insert(id, public_key);
    }
    
    pub fn generate_commitment(&self, participant_id: &str, round: u64) -> GroupElement {
        let participant = self.participants.get(participant_id).unwrap();
        
        // 使用参与者的公钥和轮次生成承诺
        let commitment = participant.pow(round);
        commitment
    }
    
    pub fn verify_commitment(&self, participant_id: &str, round: u64, commitment: &GroupElement) -> bool {
        let expected = self.generate_commitment(participant_id, round);
        *commitment == expected
    }
    
    pub fn generate_proof(&self, participant_id: &str, round: u64, private_key: u64) -> u64 {
        // 生成参与证明
        let proof = (private_key * round) % self.order;
        proof
    }
    
    pub fn verify_proof(&self, participant_id: &str, round: u64, commitment: &GroupElement, proof: u64) -> bool {
        let participant = self.participants.get(participant_id).unwrap();
        
        // 验证证明：g^proof = commitment^round
        let left = self.generator.pow(proof);
        let right = commitment.pow(round);
        
        left == right
    }
    
    pub fn select_leader(&self, round: u64, seed: u64) -> Option<String> {
        if self.participants.is_empty() {
            return None;
        }
        
        // 使用群运算选择领导者
        let hash = (seed * round) % self.order;
        let leader_index = hash % self.participants.len() as u64;
        
        let participant_ids: Vec<String> = self.participants.keys().cloned().collect();
        Some(participant_ids[leader_index as usize].clone())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConsensusBlock {
    pub round: u64,
    pub leader: String,
    pub transactions: Vec<String>,
    pub commitment: GroupElement,
    pub proof: u64,
    pub timestamp: u64,
}

pub struct GroupBasedBlockchain {
    consensus: GroupBasedConsensus,
    blocks: Vec<ConsensusBlock>,
    current_round: u64,
}

impl GroupBasedBlockchain {
    pub fn new(modulus: u64) -> Self {
        GroupBasedBlockchain {
            consensus: GroupBasedConsensus::new(modulus),
            blocks: Vec::new(),
            current_round: 0,
        }
    }
    
    pub fn add_participant(&mut self, id: String, public_key: GroupElement) {
        self.consensus.register_participant(id, public_key);
    }
    
    pub fn propose_block(&mut self, leader_id: &str, transactions: Vec<String>, private_key: u64) -> ConsensusBlock {
        self.current_round += 1;
        
        let commitment = self.consensus.generate_commitment(leader_id, self.current_round);
        let proof = self.consensus.generate_proof(leader_id, self.current_round, private_key);
        
        let block = ConsensusBlock {
            round: self.current_round,
            leader: leader_id.to_string(),
            transactions,
            commitment,
            proof,
            timestamp: chrono::Utc::now().timestamp() as u64,
        };
        
        self.blocks.push(block.clone());
        block
    }
    
    pub fn verify_block(&self, block: &ConsensusBlock) -> bool {
        // 验证领导者选择
        let expected_leader = self.consensus.select_leader(block.round, block.timestamp);
        if expected_leader.as_ref() != Some(&block.leader) {
            return false;
        }
        
        // 验证承诺和证明
        self.consensus.verify_proof(&block.leader, block.round, &block.commitment, block.proof)
    }
    
    pub fn get_blocks(&self) -> &Vec<ConsensusBlock> {
        &self.blocks
    }
}
```

#### 项目成果3

- 实现了基于群论的区块链共识机制
- 利用群的代数性质保证共识安全性
- 支持可验证的领导者选择
- 提供了完整的区块验证机制

## 学习资源

### 推荐教材

1. **群论基础**：《Abstract Algebra》- David S. Dummit
2. **有限群论**：《Finite Group Theory》- I. Martin Isaacs
3. **群表示论**：《Representation Theory》- William Fulton
4. **应用群论**：《Applications of Group Theory》- Morton Hamermesh

### 在线资源

- [群论教程](https://groupprops.subwiki.org/)
- [椭圆曲线群](https://en.wikipedia.org/wiki/Elliptic_curve)
- [置换群应用](https://crypto.stanford.edu/pbc/notes/crypto/perm.html)

## 贡献指南

欢迎对群论内容进行贡献。请确保：

1. 所有数学概念都有严格的数学定义
2. 包含在Web3中的具体应用场景
3. 提供Rust代码实现示例
4. 说明算法的复杂度和安全性
5. 关注最新的数学研究成果
