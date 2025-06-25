# 密码学基础 (Cryptographic Foundations)

## 概述

密码学基础是Web3技术的安全核心，为区块链、智能合约、隐私保护等提供数学安全保障。本目录涵盖现代密码学的理论基础和实际应用，特别关注在Web3环境中的使用。

## 目录结构

### 2.1 对称密码学 (Symmetric Cryptography)

- [**分组密码**](01_Symmetric_Cryptography/01_Block_Ciphers/) - AES、DES、3DES、分组密码模式
- [**流密码**](01_Symmetric_Cryptography/02_Stream_Ciphers/) - ChaCha20、RC4、流密码设计
- [**哈希函数**](01_Symmetric_Cryptography/03_Hash_Functions/) - SHA系列、MD5、哈希函数安全性
- [**消息认证码**](01_Symmetric_Cryptography/04_Message_Authentication_Codes/) - HMAC、CBC-MAC、认证加密
- [**密钥派生函数**](01_Symmetric_Cryptography/05_Key_Derivation_Functions/) - PBKDF2、Argon2、密钥扩展

### 2.2 非对称密码学 (Asymmetric Cryptography)

- [**RSA密码系统**](02_Asymmetric_Cryptography/01_RSA_Cryptosystem/) - RSA算法、密钥生成、安全性分析
- [**椭圆曲线密码学**](02_Asymmetric_Cryptography/02_Elliptic_Curve_Cryptography/) - ECDSA、ECDH、椭圆曲线选择
- [**数字签名**](02_Asymmetric_Cryptography/03_Digital_Signatures/) - 数字签名方案、安全性证明、标准化
- [**公钥基础设施**](02_Asymmetric_Cryptography/04_Public_Key_Infrastructure/) - PKI、证书链、信任模型
- [**身份基加密**](02_Asymmetric_Cryptography/05_Identity_Based_Encryption/) - IBE、双线性对、基于身份的密码学

### 2.3 哈希函数与数字签名 (Hash Functions & Digital Signatures)

- [**密码学哈希函数**](03_Hash_Functions_Digital_Signatures/01_Cryptographic_Hash_Functions/) - 哈希函数性质、抗碰撞性、生日攻击
- [**Merkle树**](03_Hash_Functions_Digital_Signatures/02_Merkle_Trees/) - Merkle树构造、证明、在区块链中的应用
- [**数字签名方案**](03_Hash_Functions_Digital_Signatures/03_Digital_Signature_Schemes/) - DSA、EdDSA、多重签名
- [**阈值签名**](03_Hash_Functions_Digital_Signatures/04_Threshold_Signatures/) - 分布式签名、门限密码学
- [**聚合签名**](03_Hash_Functions_Digital_Signatures/05_Aggregate_Signatures/) - 批量验证、聚合签名方案

### 2.4 零知识证明系统 (Zero Knowledge Proof Systems)

- [**零知识证明基础**](04_Zero_Knowledge_Proofs/01_Zero_Knowledge_Proof_Basics/) - 交互式证明、完备性、可靠性、零知识性
- [**zk-SNARKs**](04_Zero_Knowledge_Proofs/02_zk_SNARKs/) - 简洁非交互式零知识证明、可信设置、电路编译
- [**zk-STARKs**](04_Zero_Knowledge_Proofs/03_zk_STARKs/) - 透明零知识证明、抗量子性、可扩展性
- [**Bulletproofs**](04_Zero_Knowledge_Proofs/04_Bulletproofs/) - 范围证明、内积证明、无可信设置
- [**递归零知识证明**](04_Zero_Knowledge_Proofs/05_Recursive_Zero_Knowledge_Proofs/) - 递归组合、证明聚合、可扩展性

### 2.5 多方安全计算 (Multi-Party Secure Computation)

- [**秘密共享**](05_Multi_Party_Secure_Computation/01_Secret_Sharing/) - Shamir秘密共享、门限方案、可验证秘密共享
- [**同态加密**](05_Multi_Party_Secure_Computation/02_Homomorphic_Encryption/) - 部分同态、全同态加密、BGV方案
- [**安全多方计算**](05_Multi_Party_Secure_Computation/03_Secure_Multi_Party_Computation/) - Yao混淆电路、GMW协议、BGW协议
- [**函数秘密共享**](05_Multi_Party_Secure_Computation/04_Function_Secret_Sharing/) - 分布式点函数、函数求值
- [**联邦学习中的隐私保护**](05_Multi_Party_Secure_Computation/05_Privacy_Preserving_Federated_Learning/) - 差分隐私、安全聚合

### 2.6 后量子密码学 (Post-Quantum Cryptography)

- [**格密码学**](06_Post_Quantum_Cryptography/01_Lattice_Based_Cryptography/) - LWE问题、NTRU、格基密码学
- [**基于哈希的签名**](06_Post_Quantum_Cryptography/02_Hash_Based_Signatures/) - Merkle签名、XMSS、SPHINCS+
- [**多变量密码学**](06_Post_Quantum_Cryptography/03_Multivariate_Cryptography/) - Rainbow、HFE、多变量签名
- [**基于编码的密码学**](06_Post_Quantum_Cryptography/04_Code_Based_Cryptography/) - McEliece、Niederreiter、纠错码
- [**基于同源性的密码学**](06_Post_Quantum_Cryptography/05_Isogeny_Based_Cryptography/) - SIDH、CSIDH、超奇异同源

## 核心概念

### 密码学安全性

密码学系统的安全性基于计算复杂性假设，主要包括：

**定义**：一个密码学方案是安全的，如果对于任何多项式时间的敌手，其成功概率都是可忽略的。

**常见假设**：

- 离散对数假设 (DLP)
- 椭圆曲线离散对数假设 (ECDLP)
- 大整数分解假设 (IFP)
- 格上最短向量问题 (SVP)
- 学习带误差问题 (LWE)

### 零知识证明

零知识证明允许证明者向验证者证明某个陈述为真，而不泄露任何额外信息。

**性质**：

- **完备性**：诚实的证明者能够说服诚实的验证者
- **可靠性**：不诚实的证明者无法说服诚实的验证者
- **零知识性**：验证者无法获得除陈述为真之外的任何信息

### 同态加密

同态加密允许在加密数据上进行计算，而无需解密。

**类型**：

- **部分同态**：支持有限的计算操作
- **全同态**：支持任意计算操作
- **近似同态**：支持近似计算

## 在Web3中的应用

### 1. 区块链安全

- **数字签名**：交易签名、区块签名
- **哈希函数**：区块哈希、交易哈希、Merkle根
- **零知识证明**：隐私交易、可验证计算

### 2. 智能合约

- **阈值签名**：多重签名钱包
- **同态加密**：隐私智能合约
- **零知识证明**：可验证随机数、隐私投票

### 3. 隐私保护

- **环签名**：隐私交易
- **零知识证明**：身份验证、凭证证明
- **同态加密**：隐私计算

### 4. 跨链技术

- **哈希时间锁合约**：原子交换
- **零知识证明**：跨链验证
- **多方计算**：跨链桥安全

## 学习资源

### 推荐教材

1. **密码学基础**：《Introduction to Modern Cryptography》- Jonathan Katz
2. **零知识证明**：《Proofs, Arguments, and Zero-Knowledge》- Justin Thaler
3. **后量子密码学**：《Post-Quantum Cryptography》- Daniel J. Bernstein
4. **同态加密**：《A Guide to Fully Homomorphic Encryption》- Craig Gentry

### 在线资源

- [密码学课程](https://cryptography.stanford.edu/)
- [零知识证明教程](https://zkproof.org/)
- [后量子密码学标准化](https://csrc.nist.gov/projects/post-quantum-cryptography)

## Rust实现示例

### AES加密实现

```rust
use aes::Aes128;
use aes::cipher::{
    BlockEncrypt, BlockDecrypt,
    KeyInit,
    generic_array::GenericArray,
};

pub struct AESCipher {
    cipher: Aes128,
}

impl AESCipher {
    pub fn new(key: &[u8; 16]) -> Self {
        let cipher = Aes128::new_from_slice(key).unwrap();
        AESCipher { cipher }
    }
    
    pub fn encrypt_block(&self, plaintext: &[u8; 16]) -> [u8; 16] {
        let mut block = GenericArray::clone_from_slice(plaintext);
        self.cipher.encrypt_block(&mut block);
        block.into()
    }
    
    pub fn decrypt_block(&self, ciphertext: &[u8; 16]) -> [u8; 16] {
        let mut block = GenericArray::clone_from_slice(ciphertext);
        self.cipher.decrypt_block(&mut block);
        block.into()
    }
}
```

### SHA256哈希函数

```rust
use sha2::{Sha256, Digest};

pub fn sha256_hash(data: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hasher.finalize().into()
}

pub fn double_sha256(data: &[u8]) -> [u8; 32] {
    sha256_hash(&sha256_hash(data))
}
```

### ECDSA签名

```rust
use secp256k1::{Secp256k1, SecretKey, PublicKey, Message, Signature};
use rand::rngs::OsRng;

pub struct ECDSASigner {
    secp: Secp256k1<secp256k1::All>,
}

impl ECDSASigner {
    pub fn new() -> Self {
        ECDSASigner {
            secp: Secp256k1::new(),
        }
    }
    
    pub fn generate_keypair(&self) -> (SecretKey, PublicKey) {
        let secret_key = SecretKey::new(&mut OsRng);
        let public_key = PublicKey::from_secret_key(&self.secp, &secret_key);
        (secret_key, public_key)
    }
    
    pub fn sign(&self, secret_key: &SecretKey, message: &[u8]) -> Signature {
        let message = Message::from_slice(message).unwrap();
        self.secp.sign(&message, secret_key)
    }
    
    pub fn verify(&self, public_key: &PublicKey, message: &[u8], signature: &Signature) -> bool {
        let message = Message::from_slice(message).unwrap();
        self.secp.verify(&message, signature, public_key).is_ok()
    }
}
```

### Merkle树实现

```rust
use sha2::{Sha256, Digest};

#[derive(Debug, Clone)]
pub struct MerkleTree {
    pub root: [u8; 32],
    pub leaves: Vec<[u8; 32]>,
    pub tree: Vec<Vec<[u8; 32]>>,
}

impl MerkleTree {
    pub fn new(leaves: Vec<[u8; 32]>) -> Self {
        let mut tree = vec![leaves.clone()];
        let mut current_level = leaves;
        
        while current_level.len() > 1 {
            let mut next_level = Vec::new();
            for chunk in current_level.chunks(2) {
                let hash = if chunk.len() == 2 {
                    Self::hash_pair(&chunk[0], &chunk[1])
                } else {
                    chunk[0]
                };
                next_level.push(hash);
            }
            tree.push(next_level.clone());
            current_level = next_level;
        }
        
        let root = if !current_level.is_empty() {
            current_level[0]
        } else {
            [0u8; 32]
        };
        
        MerkleTree {
            root,
            leaves,
            tree,
        }
    }
    
    fn hash_pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(left);
        hasher.update(right);
        hasher.finalize().into()
    }
    
    pub fn generate_proof(&self, leaf_index: usize) -> Vec<[u8; 32]> {
        let mut proof = Vec::new();
        let mut index = leaf_index;
        
        for level in &self.tree[..self.tree.len()-1] {
            let sibling_index = if index % 2 == 0 { index + 1 } else { index - 1 };
            if sibling_index < level.len() {
                proof.push(level[sibling_index]);
            }
            index /= 2;
        }
        
        proof
    }
    
    pub fn verify_proof(&self, leaf: &[u8; 32], proof: &[[u8; 32]], leaf_index: usize) -> bool {
        let mut current_hash = *leaf;
        let mut index = leaf_index;
        
        for sibling in proof {
            current_hash = if index % 2 == 0 {
                Self::hash_pair(&current_hash, sibling)
            } else {
                Self::hash_pair(sibling, &current_hash)
            };
            index /= 2;
        }
        
        current_hash == self.root
    }
}
```

## 贡献指南

欢迎对密码学基础内容进行贡献。请确保：

1. 所有密码学定义都有严格的数学表述
2. 包含安全性分析和证明
3. 提供Rust代码实现
4. 说明在Web3中的具体应用场景
5. 关注最新的密码学发展，特别是后量子密码学
