# 密码学基础理论 (Cryptography Foundation)

## 目录

1. [密码学基础概念](#1-密码学基础概念)
2. [哈希函数理论](#2-哈希函数理论)
3. [数字签名理论](#3-数字签名理论)
4. [零知识证明](#4-零知识证明)
5. [后量子密码学](#5-后量子密码学)
6. [密码学安全性分析](#6-密码学安全性分析)
7. [实现示例](#7-实现示例)
8. [参考与扩展](#8-参考与扩展)

## 1. 密码学基础概念

### 1.1 密码学定义

**定义 1.1.1 (密码学)**
密码学是研究信息安全的科学，包括加密、解密、认证、完整性验证等技术。

**定义 1.1.2 (密码系统)**
密码系统是一个五元组 $\mathcal{C} = (M, C, K, E, D)$，其中：

- $M$ 是明文空间
- $C$ 是密文空间
- $K$ 是密钥空间
- $E: K \times M \to C$ 是加密函数
- $D: K \times C \to M$ 是解密函数

**定义 1.1.3 (密码系统正确性)**
密码系统满足正确性，当且仅当：
$$\forall k \in K, \forall m \in M: D(k, E(k, m)) = m$$

### 1.2 密码学安全模型

**定义 1.2.1 (计算安全性)**
密码系统是 $(t, \epsilon)$-计算安全的，如果任何运行时间不超过 $t$ 的算法，成功攻击的概率不超过 $\epsilon$。

**定义 1.2.2 (信息论安全性)**
密码系统是信息论安全的，如果即使攻击者拥有无限计算能力，也无法获得关于明文的信息。

**定理 1.2.1 (完美保密性)**
一次性密码本(One-Time Pad)是信息论安全的。

**证明：** 通过信息论分析：

设明文为 $m$，密钥为 $k$，密文为 $c = m \oplus k$。

对于任意明文 $m_1, m_2$ 和密文 $c$：
$$P(m = m_1 | c) = P(m = m_2 | c) = \frac{1}{|M|}$$

因此，密文不泄露任何关于明文的信息。■

## 2. 哈希函数理论

### 2.1 哈希函数定义

**定义 2.1.1 (哈希函数)**
哈希函数 $H: \{0,1\}^* \to \{0,1\}^n$ 将任意长度的输入映射到固定长度的输出。

**定义 2.1.2 (密码学哈希函数)**
密码学哈希函数 $H$ 必须满足以下性质：

1. **抗碰撞性 (Collision Resistance)**：找到 $x \neq y$ 使得 $H(x) = H(y)$ 是困难的
2. **抗第二原像性 (Second Preimage Resistance)**：给定 $x$，找到 $y \neq x$ 使得 $H(x) = H(y)$ 是困难的
3. **抗第一原像性 (Preimage Resistance)**：给定 $h$，找到 $x$ 使得 $H(x) = h$ 是困难的

### 2.2 哈希函数安全性

**定理 2.2.1 (生日攻击)**
对于 $n$ 比特的哈希函数，找到碰撞需要约 $2^{n/2}$ 次哈希计算。

**证明：** 通过生日悖论：

设哈希函数输出空间大小为 $N = 2^n$。

根据生日悖论，当随机选择 $k$ 个元素时，存在碰撞的概率为：
$$P(\text{collision}) \approx 1 - e^{-k^2/(2N)}$$

当 $k \approx \sqrt{2N} = 2^{n/2}$ 时，碰撞概率约为 $1 - e^{-1} \approx 0.63$。

因此，找到碰撞需要约 $2^{n/2}$ 次计算。■

**定理 2.2.2 (Merkle-Damgård构造安全性)**
如果压缩函数 $f$ 是抗碰撞的，则Merkle-Damgård构造的哈希函数也是抗碰撞的。

**证明：** 通过反证法：

假设Merkle-Damgård构造的哈希函数存在碰撞，即存在 $x \neq y$ 使得 $H(x) = H(y)$。

由于 $x \neq y$，在Merkle-Damgård构造的某个步骤中，压缩函数 $f$ 的输入必然不同，但输出相同。

这与压缩函数 $f$ 的抗碰撞性矛盾。■

### 2.3 常用哈希函数

**定义 2.3.1 (SHA-256)**
SHA-256是一个256比特的哈希函数，基于Merkle-Damgård构造。

**定义 2.3.2 (Keccak/SHA-3)**
Keccak是SHA-3的候选算法，基于海绵构造(Sponge Construction)。

**定理 2.3.1 (海绵构造安全性)**
海绵构造的哈希函数在随机预言机模型下是安全的。

## 3. 数字签名理论

### 3.1 数字签名定义

**定义 3.1.1 (数字签名方案)**
数字签名方案是一个三元组 $\mathcal{S} = (Gen, Sign, Verify)$，其中：

- $Gen$ 是密钥生成算法
- $Sign$ 是签名算法
- $Verify$ 是验证算法

**定义 3.1.2 (数字签名安全性)**
数字签名方案必须满足：

1. **不可伪造性 (Unforgeability)**：攻击者无法伪造有效签名
2. **不可否认性 (Non-repudiation)**：签名者无法否认其签名
3. **完整性 (Integrity)**：签名确保消息未被篡改

### 3.2 RSA签名

**定义 3.2.1 (RSA签名)**
RSA签名方案基于RSA困难性问题：

1. **密钥生成**：选择大素数 $p, q$，计算 $n = pq$，选择 $e$ 使得 $\gcd(e, \phi(n)) = 1$，计算 $d = e^{-1} \bmod \phi(n)$
2. **签名**：$\sigma = m^d \bmod n$
3. **验证**：检查 $m = \sigma^e \bmod n$

**定理 3.2.1 (RSA签名安全性)**
RSA签名的安全性基于大数分解问题的困难性。

**证明：** 通过归约：

如果存在攻击者能够伪造RSA签名，则可以利用该攻击者解决大数分解问题。

因此，RSA签名的安全性基于大数分解问题的困难性。■

### 3.3 ECDSA签名

**定义 3.3.1 (ECDSA签名)**
ECDSA (Elliptic Curve Digital Signature Algorithm) 基于椭圆曲线离散对数问题：

1. **密钥生成**：选择椭圆曲线 $E$ 和基点 $G$，选择私钥 $d$，计算公钥 $Q = dG$
2. **签名**：选择随机数 $k$，计算 $R = kG$，$r = x_R \bmod n$，$s = k^{-1}(H(m) + dr) \bmod n$
3. **验证**：计算 $u_1 = H(m)s^{-1} \bmod n$，$u_2 = rs^{-1} \bmod n$，检查 $R = u_1G + u_2Q$

**定理 3.3.1 (ECDSA安全性)**
ECDSA的安全性基于椭圆曲线离散对数问题的困难性。

**证明：** 通过归约：

如果存在攻击者能够伪造ECDSA签名，则可以利用该攻击者解决椭圆曲线离散对数问题。

因此，ECDSA的安全性基于椭圆曲线离散对数问题的困难性。■

### 3.4 Schnorr签名

**定义 3.4.1 (Schnorr签名)**
Schnorr签名是一种基于离散对数问题的数字签名方案：

1. **密钥生成**：选择群 $G$ 和生成元 $g$，选择私钥 $x$，计算公钥 $y = g^x$
2. **签名**：选择随机数 $k$，计算 $R = g^k$，$e = H(m || R)$，$s = k + ex \bmod q$
3. **验证**：计算 $R' = g^s y^{-e}$，检查 $e = H(m || R')$

**定理 3.4.1 (Schnorr签名安全性)**
Schnorr签名在随机预言机模型下是安全的。

**证明：** 通过Forking Lemma：

如果存在攻击者能够伪造Schnorr签名，则可以利用Forking Lemma提取离散对数。

因此，Schnorr签名在随机预言机模型下是安全的。■

## 4. 零知识证明

### 4.1 零知识证明定义

**定义 4.1.1 (零知识证明系统)**
零知识证明系统是一个三元组 $\mathcal{ZK} = (P, V, \mathcal{R})$，其中：

- $P$ 是证明者
- $V$ 是验证者
- $\mathcal{R}$ 是关系集合

**定义 4.1.2 (零知识证明性质)**
零知识证明系统必须满足：

1. **完备性 (Completeness)**：诚实验证者接受诚实证明者
2. **可靠性 (Soundness)**：不诚实证明者无法欺骗验证者
3. **零知识性 (Zero-Knowledge)**：验证者无法获得额外信息

### 4.2 Schnorr零知识证明

**定义 4.2.1 (Schnorr零知识证明)**
Schnorr零知识证明用于证明离散对数知识：

1. **承诺**：证明者选择随机数 $r$，计算 $A = g^r$
2. **挑战**：验证者发送随机挑战 $c$
3. **响应**：证明者计算 $z = r + cx$，发送给验证者
4. **验证**：验证者检查 $g^z = A \cdot y^c$

**定理 4.2.1 (Schnorr零知识性)**
Schnorr协议是零知识的。

**证明：** 通过构造模拟器：

模拟器可以生成与真实协议不可区分的视图，而不需要知道秘密值 $x$。

因此，Schnorr协议是零知识的。■

### 4.3 zk-SNARK

**定义 4.3.1 (zk-SNARK)**
zk-SNARK (Zero-Knowledge Succinct Non-Interactive Argument of Knowledge) 是一种非交互式零知识证明系统。

**定理 4.3.1 (zk-SNARK安全性)**
zk-SNARK在通用群模型下是安全的。

**证明：** 通过通用群模型：

在通用群模型中，攻击者只能执行群运算，无法利用群的具体结构。

因此，zk-SNARK在通用群模型下是安全的。■

## 5. 后量子密码学

### 5.1 量子计算威胁

**定义 5.1.1 (量子计算威胁)**
量子计算机能够解决某些经典计算机难以解决的问题，如大数分解和离散对数。

**定理 5.1.1 (Shor算法)**
Shor算法可以在量子计算机上在多项式时间内解决大数分解和离散对数问题。

**证明：** 通过量子傅里叶变换：

Shor算法利用量子傅里叶变换找到周期，从而解决大数分解和离散对数问题。

时间复杂度为 $O((\log N)^3)$，其中 $N$ 是问题规模。■

### 5.2 格密码学

**定义 5.2.1 (格问题)**
格问题包括：

1. **最短向量问题 (SVP)**：找到格中最短的非零向量
2. **最近向量问题 (CVP)**：找到格中距离给定点最近的向量
3. **学习带错误问题 (LWE)**：从带噪声的线性方程中恢复秘密

**定理 5.2.1 (格密码安全性)**
基于格问题的密码系统在量子计算下保持安全性。

**证明：** 通过复杂度分析：

目前已知的量子算法无法有效解决格问题。格问题在量子计算下仍然困难。

因此，基于格问题的密码系统在量子计算下保持安全性。■

### 5.3 多变量密码学

**定义 5.3.1 (多变量密码学)**
多变量密码学基于求解多变量多项式系统的困难性。

**定理 5.3.1 (多变量密码安全性)**
多变量密码系统在量子计算下保持安全性。

**证明：** 通过复杂度分析：

求解多变量多项式系统在量子计算下仍然困难。

因此，多变量密码系统在量子计算下保持安全性。■

## 6. 密码学安全性分析

### 6.1 攻击模型

**定义 6.1.1 (攻击模型)**
攻击模型定义了攻击者的能力和限制：

1. **唯密文攻击 (Ciphertext-Only Attack)**
2. **已知明文攻击 (Known-Plaintext Attack)**
3. **选择明文攻击 (Chosen-Plaintext Attack)**
4. **选择密文攻击 (Chosen-Ciphertext Attack)**

### 6.2 安全性证明

**定理 6.2.1 (密码学安全性)**
在适当的假设下，密码系统能够抵抗已知的攻击。

**证明：** 通过形式化验证：

1. **模型检查**：验证密码系统在各种场景下的行为
2. **定理证明**：证明密码系统满足安全性质
3. **模拟攻击**：测试密码系统对攻击的抵抗能力

## 7. 实现示例

### 7.1 哈希函数实现

```rust
// SHA-256哈希函数实现
pub struct SHA256 {
    state: [u32; 8],
    buffer: [u8; 64],
    buffer_len: usize,
    total_len: u64,
}

impl SHA256 {
    pub fn new() -> Self {
        SHA256 {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
            ],
            buffer: [0; 64],
            buffer_len: 0,
            total_len: 0,
        }
    }
    
    pub fn update(&mut self, data: &[u8]) {
        self.total_len += data.len() as u64;
        
        let mut data_pos = 0;
        
        // 处理缓冲区中的数据
        if self.buffer_len > 0 {
            let copy_len = (64 - self.buffer_len).min(data.len());
            self.buffer[self.buffer_len..self.buffer_len + copy_len].copy_from_slice(&data[..copy_len]);
            self.buffer_len += copy_len;
            data_pos += copy_len;
            
            if self.buffer_len == 64 {
                self.process_block(&self.buffer);
                self.buffer_len = 0;
            }
        }
        
        // 处理完整块
        while data_pos + 64 <= data.len() {
            self.process_block(&data[data_pos..data_pos + 64]);
            data_pos += 64;
        }
        
        // 保存剩余数据
        if data_pos < data.len() {
            self.buffer[..data.len() - data_pos].copy_from_slice(&data[data_pos..]);
            self.buffer_len = data.len() - data_pos;
        }
    }
    
    pub fn finalize(mut self) -> [u8; 32] {
        // 添加填充
        let mut padding = [0u8; 64];
        padding[0] = 0x80;
        
        if self.buffer_len >= 56 {
            self.update(&padding[..64 - self.buffer_len]);
            self.update(&padding[..56]);
        } else {
            self.update(&padding[..56 - self.buffer_len]);
        }
        
        // 添加长度
        let length_bytes = (self.total_len * 8).to_be_bytes();
        self.update(&length_bytes);
        
        // 输出结果
        let mut result = [0u8; 32];
        for (i, word) in self.state.iter().enumerate() {
            result[i * 4..(i + 1) * 4].copy_from_slice(&word.to_be_bytes());
        }
        
        result
    }
    
    fn process_block(&mut self, block: &[u8]) {
        let mut w = [0u32; 64];
        
        // 准备消息调度
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                block[i * 4], block[i * 4 + 1], block[i * 4 + 2], block[i * 4 + 3]
            ]);
        }
        
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        
        // 初始化工作变量
        let mut a = self.state[0];
        let mut b = self.state[1];
        let mut c = self.state[2];
        let mut d = self.state[3];
        let mut e = self.state[4];
        let mut f = self.state[5];
        let mut g = self.state[6];
        let mut h = self.state[7];
        
        // 主循环
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ (!e & g);
            let temp1 = h.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);
            
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        
        // 更新状态
        self.state[0] = self.state[0].wrapping_add(a);
        self.state[1] = self.state[1].wrapping_add(b);
        self.state[2] = self.state[2].wrapping_add(c);
        self.state[3] = self.state[3].wrapping_add(d);
        self.state[4] = self.state[4].wrapping_add(e);
        self.state[5] = self.state[5].wrapping_add(f);
        self.state[6] = self.state[6].wrapping_add(g);
        self.state[7] = self.state[7].wrapping_add(h);
    }
}

// SHA-256常量
const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];
```

### 7.2 ECDSA签名实现

```rust
// ECDSA签名实现
#[derive(Clone, Debug)]
pub struct ECDSA {
    curve: Secp256k1,
}

#[derive(Clone, Debug)]
pub struct ECDSAPrivateKey {
    key: SecretKey,
}

#[derive(Clone, Debug)]
pub struct ECDSAPublicKey {
    key: PublicKey,
}

#[derive(Clone, Debug)]
pub struct ECDSASignature {
    r: [u8; 32],
    s: [u8; 32],
}

impl ECDSA {
    pub fn new() -> Self {
        ECDSA {
            curve: Secp256k1::new(),
        }
    }
    
    pub fn generate_keypair(&self) -> (ECDSAPrivateKey, ECDSAPublicKey) {
        let (secret_key, public_key) = self.curve.generate_keypair(&mut thread_rng());
        
        (ECDSAPrivateKey { key: secret_key }, ECDSAPublicKey { key: public_key })
    }
    
    pub fn sign(&self, private_key: &ECDSAPrivateKey, message: &[u8]) -> Result<ECDSASignature, SignatureError> {
        let message_hash = self.hash_message(message);
        let signature = self.curve.sign(&message_hash, &private_key.key);
        
        let (r, s) = signature.serialize_compact();
        
        Ok(ECDSASignature { r, s })
    }
    
    pub fn verify(&self, public_key: &ECDSAPublicKey, message: &[u8], signature: &ECDSASignature) -> bool {
        let message_hash = self.hash_message(message);
        
        let signature_obj = Signature::from_compact(&[&signature.r, &signature.s].concat())
            .map_err(|_| SignatureError::InvalidSignature)?;
        
        self.curve.verify(&message_hash, &signature_obj, &public_key.key).is_ok()
    }
    
    fn hash_message(&self, message: &[u8]) -> Message {
        let mut hasher = sha2::Sha256::new();
        hasher.update(message);
        let hash = hasher.finalize();
        Message::from_slice(&hash).unwrap()
    }
}

#[derive(Debug)]
pub enum SignatureError {
    InvalidSignature,
    InvalidKey,
    InvalidMessage,
}
```

### 7.3 零知识证明实现

```rust
// Schnorr零知识证明实现
#[derive(Clone, Debug)]
pub struct SchnorrZK {
    curve: Secp256k1,
}

#[derive(Clone, Debug)]
pub struct SchnorrProof {
    commitment: [u8; 33],
    challenge: [u8; 32],
    response: [u8; 32],
}

impl SchnorrZK {
    pub fn new() -> Self {
        SchnorrZK {
            curve: Secp256k1::new(),
        }
    }
    
    pub fn prove(&self, secret_key: &[u8], public_key: &[u8], message: &[u8]) -> Result<SchnorrProof, ZKError> {
        // 生成随机数
        let mut rng = thread_rng();
        let k = SecretKey::new(&mut rng);
        
        // 计算承诺
        let commitment_point = PublicKey::from_secret_key(&self.curve, &k);
        let commitment = commitment_point.serialize();
        
        // 计算挑战
        let mut hasher = sha2::Sha256::new();
        hasher.update(&commitment);
        hasher.update(public_key);
        hasher.update(message);
        let challenge_bytes = hasher.finalize();
        
        // 计算响应
        let secret_key_scalar = Scalar::from_be_bytes(secret_key.try_into().unwrap()).unwrap();
        let challenge_scalar = Scalar::from_be_bytes(challenge_bytes.try_into().unwrap()).unwrap();
        let k_scalar = Scalar::from_be_bytes(k.secret_bytes().try_into().unwrap()).unwrap();
        
        let response_scalar = k_scalar + challenge_scalar * secret_key_scalar;
        let response = response_scalar.to_be_bytes();
        
        Ok(SchnorrProof {
            commitment,
            challenge: challenge_bytes.into(),
            response,
        })
    }
    
    pub fn verify(&self, public_key: &[u8], message: &[u8], proof: &SchnorrProof) -> bool {
        // 重构挑战
        let mut hasher = sha2::Sha256::new();
        hasher.update(&proof.commitment);
        hasher.update(public_key);
        hasher.update(message);
        let challenge_bytes = hasher.finalize();
        
        // 验证证明
        let commitment_point = PublicKey::from_slice(&proof.commitment).unwrap();
        let public_key_point = PublicKey::from_slice(public_key).unwrap();
        
        let challenge_scalar = Scalar::from_be_bytes(challenge_bytes.try_into().unwrap()).unwrap();
        let response_scalar = Scalar::from_be_bytes(proof.response.try_into().unwrap()).unwrap();
        
        let left_side = commitment_point + public_key_point * challenge_scalar;
        let right_side = PublicKey::from_secret_key(&self.curve, &SecretKey::from_slice(&proof.response).unwrap());
        
        left_side == right_side
    }
}

#[derive(Debug)]
pub enum ZKError {
    InvalidInput,
    InvalidProof,
    VerificationFailed,
}
```

## 8. 参考与扩展

### 8.1 相关理论

- [区块链基础理论](../01_Foundations/Blockchain_Formal_Model.md)
- [共识机制理论](../02_Consensus_Theory/Consensus_Formal_Proofs.md)
- [网络安全理论](../04_Network/Network_Security_Theory.md)
- [隐私保护理论](../05_Security_Privacy/Privacy_Protection_Theory.md)

### 8.2 高级主题

- [后量子密码学](../05_Security_Privacy/Post_Quantum_Cryptography.md)
- [同态加密](../05_Security_Privacy/Homomorphic_Encryption.md)
- [多方计算](../05_Security_Privacy/Secure_Multi_Party_Computation.md)
- [量子密码学](../11_Future_Trends/Quantum_Cryptography.md)

### 8.3 实现参考

- [Rust密码学实现](../03_Technology_Stack/Rust_Cryptography_Implementation.md)
- [Go密码学实现](../03_Technology_Stack/Go_Cryptography_Implementation.md)
- [密码学库比较](../03_Technology_Stack/Cryptography_Library_Comparison.md)

### 8.4 外部参考

- [Applied Cryptography](https://www.schneier.com/books/applied_cryptography/)
- [Handbook of Applied Cryptography](https://cacr.uwaterloo.ca/hac/)
- [Introduction to Modern Cryptography](https://www.cs.umd.edu/~jkatz/imc.html)
- [Post-Quantum Cryptography](https://pqcrypto.org/)
- [Zero-Knowledge Proofs](https://zkproof.org/)
