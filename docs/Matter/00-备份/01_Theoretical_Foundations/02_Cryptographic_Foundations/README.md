# 密码学基础 (Cryptographic Foundations)

## 概述

密码学是Web3与区块链安全的数学基石，涵盖对称/非对称加密、哈希函数、数字签名、零知识证明、多方安全计算、抗量子密码等核心理论。密码学为分布式系统提供数据完整性、身份认证、隐私保护和共识安全。

## 目录结构

### 1. [对称与非对称加密](01_Symmetric_Asymmetric_Cryptography/)

- 对称加密算法（AES、ChaCha20）
- 非对称加密算法（RSA、ECC）
- 密钥生成与管理

### 2. [哈希函数与Merkle树](02_Hash_Functions_Merkle_Tree/)

- 哈希函数定义与性质
- Merkle树结构与证明
- 区块链数据完整性

### 3. [数字签名与身份认证](03_Digital_Signature_Authentication/)

- 数字签名算法（ECDSA、EdDSA、Schnorr）
- 签名安全性
- 身份认证协议

### 4. [零知识证明与隐私保护](04_Zero_Knowledge_Privacy/)

- 零知识证明（zk-SNARK、zk-STARK）
- 隐私保护协议
- 匿名交易

### 5. [多方安全计算与抗量子密码](05_MPC_Quantum_Resistant/)

- 多方安全计算（MPC）
- 抗量子密码学
- 未来密码学趋势

## 核心定义与定理

### 密码学安全模型

**定义 1.1**（计算安全性）：
一个密码方案在计算上安全，如果对于任何多项式时间攻击者，破解该方案的概率可忽略。

**定义 1.2**（可忽略函数）：
函数 $f: \mathbb{N} \to \mathbb{R}$ 可忽略，如果对任意多项式 $p$，存在 $N$ 使得 $n > N$ 时 $|f(n)| < 1/p(n)$。

**定义 1.3**（语义安全）：
加密方案 $\Pi = (Gen, Enc, Dec)$ 语义安全，如果对于任意多项式时间攻击者 $\mathcal{A}$，存在可忽略函数 $negl$，使得：
$$|Pr[PrivK_{\mathcal{A},\Pi}^{eav}(n) = 1] - \frac{1}{2}| \leq negl(n)$$

### 经典难题假设

- **离散对数难题**：给定群 $G$ 的生成元 $g$ 和 $h = g^x$，计算 $x$ 困难。
- **椭圆曲线离散对数难题**：给定椭圆曲线 $E$ 上点 $P$ 和 $Q = xP$，计算 $x$ 困难。
- **RSA难题**：给定 $N = pq$ 和 $e$，计算 $d$ 使 $ed \equiv 1 \pmod{\phi(N)}$ 困难。

### 哈希函数性质

- **抗原像性**：给定 $y$，找到 $x$ 使 $H(x) = y$ 困难。
- **抗第二原像性**：给定 $x$，找到 $x' \neq x$ 使 $H(x) = H(x')$ 困难。
- **抗碰撞性**：找到 $x \neq x'$ 使 $H(x) = H(x')$ 困难。

### Merkle树

**定义 2.1**（Merkle树）：
对数据块 $D = (d_1, ..., d_n)$，其Merkle根 $root$ 递归定义为：

- $n=1$ 时 $root = H(d_1)$
- $n>1$ 时 $root = H(root_L || root_R)$

**定理 2.1**（Merkle树证明）：
包含 $n$ 个数据的Merkle树，证明某数据块包含性只需 $O(\log n)$ 大小的证明。

### 零知识证明

- **定义**：证明者能向验证者证明命题成立而不泄露任何额外信息。
- **应用**：隐私交易、身份认证、链下计算等。

## 应用场景

- 区块链数据完整性与不可篡改
- 数字资产身份认证与签名
- 隐私保护与匿名交易
- 多方安全计算与链下协作
- 抗量子安全的未来区块链

## Rust代码示例

### 哈希函数与Merkle树

```rust
pub trait HashFunction {
    type Output: AsRef<[u8]> + Clone;
    fn hash(&self, data: &[u8]) -> Self::Output;
    fn hash_length(&self) -> usize;
}

pub struct SHA256;
impl HashFunction for SHA256 {
    type Output = [u8; 32];
    fn hash(&self, data: &[u8]) -> Self::Output {
        use sha2::{Sha256, Digest};
        let mut hasher = Sha256::new();
        hasher.update(data);
        let result = hasher.finalize();
        let mut arr = [0u8; 32];
        arr.copy_from_slice(&result);
        arr
    }
    fn hash_length(&self) -> usize { 32 }
}

pub struct MerkleTree<T: HashFunction> {
    hash_function: T,
    root: Option<T::Output>,
    leaves: Vec<T::Output>,
}

impl<T: HashFunction> MerkleTree<T> {
    pub fn new(hash_function: T) -> Self {
        Self { hash_function, root: None, leaves: Vec::new() }
    }
    pub fn add_leaf(&mut self, data: &[u8]) {
        let leaf_hash = self.hash_function.hash(data);
        self.leaves.push(leaf_hash);
        self.root = None;
    }
    pub fn compute_root(&mut self) -> T::Output {
        if self.leaves.is_empty() {
            return self.hash_function.hash(&[]);
        }
        let mut current_level = self.leaves.clone();
        while current_level.len() > 1 {
            let mut next_level = Vec::new();
            for chunk in current_level.chunks(2) {
                if chunk.len() == 1 {
                    next_level.push(chunk[0].clone());
                } else {
                    let combined = [chunk[0].as_ref(), chunk[1].as_ref()].concat();
                    next_level.push(self.hash_function.hash(&combined));
                }
            }
            current_level = next_level;
        }
        let root = current_level[0].clone();
        self.root = Some(root.clone());
        root
    }
}
```

## 相关链接

- [数学基础](../01_Mathematical_Foundations/)
- [形式化理论](../03_Formal_Theory/)
- [分布式系统理论](../04_Distributed_Systems_Theory/)
- [控制论与系统理论](../05_Control_Systems_Theory/)
- [哲学基础](../06_Philosophical_Foundations/)

---

*密码学为Web3系统的安全性、隐私性和可扩展性提供坚实基础。*
