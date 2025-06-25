# 对称密码学 (Symmetric Cryptography)

## 概述

对称密码学是密码学的基础分支，使用相同的密钥进行加密和解密。在Web3中，对称密码学主要用于数据加密、消息认证、密钥派生等场景。本目录涵盖分组密码、流密码、哈希函数、消息认证码等核心技术。

## 目录结构

### 1.1 分组密码 (Block Ciphers)

- [**AES算法**](01_Block_Ciphers/01_AES/) - AES-128、AES-192、AES-256、加密模式
- [**DES算法**](01_Block_Ciphers/02_DES/) - DES、3DES、加密模式、安全性分析
- [**其他分组密码**](01_Block_Ciphers/03_Other_Block_Ciphers/) - Camellia、Twofish、Serpent
- [**加密模式**](01_Block_Ciphers/04_Encryption_Modes/) - ECB、CBC、CFB、OFB、CTR、GCM
- [**填充方案**](01_Block_Ciphers/05_Padding_Schemes/) - PKCS#7、ISO 10126、ANSI X.923

### 1.2 流密码 (Stream Ciphers)

- [**RC4算法**](02_Stream_Ciphers/01_RC4/) - RC4、RC4A、安全性分析
- [**ChaCha20**](02_Stream_Ciphers/02_ChaCha20/) - ChaCha20、ChaCha20-Poly1305
- [**Salsa20**](02_Stream_Ciphers/03_Salsa20/) - Salsa20、Salsa20/12、Salsa20/8
- [**其他流密码**](02_Stream_Ciphers/04_Other_Stream_Ciphers/) - Trivium、Grain、MICKEY
- [**流密码分析**](02_Stream_Ciphers/05_Stream_Cipher_Analysis/) - 线性分析、差分分析

### 1.3 哈希函数 (Hash Functions)

- [**SHA家族**](03_Hash_Functions/01_SHA_Family/) - SHA-1、SHA-2、SHA-3
- [**MD5算法**](03_Hash_Functions/02_MD5/) - MD5、安全性分析、碰撞攻击
- [**其他哈希函数**](03_Hash_Functions/03_Other_Hash_Functions/) - RIPEMD、Whirlpool、BLAKE
- [**哈希应用**](03_Hash_Functions/04_Hash_Applications/) - 数字签名、消息认证、密码存储
- [**哈希分析**](03_Hash_Functions/05_Hash_Analysis/) - 生日攻击、彩虹表、预像攻击

### 1.4 消息认证码 (Message Authentication Codes)

- [**HMAC**](04_Message_Authentication_Codes/01_HMAC/) - HMAC-SHA256、HMAC-SHA512
- [**CMAC**](04_Message_Authentication_Codes/02_CMAC/) - CMAC-AES、CMAC-DES
- [**GMAC**](04_Message_Authentication_Codes/03_GMAC/) - GMAC、GCM模式
- [**其他MAC**](04_Message_Authentication_Codes/04_Other_MACs/) - Poly1305、UMAC、VMAC
- [**MAC应用**](04_Message_Authentication_Codes/05_MAC_Applications/) - 消息完整性、密钥确认

### 1.5 密钥管理 (Key Management)

- [**密钥生成**](05_Key_Management/01_Key_Generation/) - 随机数生成、密钥派生
- [**密钥存储**](05_Key_Management/02_Key_Storage/) - 密钥保护、硬件安全模块
- [**密钥分发**](05_Key_Management/03_Key_Distribution/) - 密钥协商、密钥传输
- [**密钥更新**](05_Key_Management/04_Key_Update/) - 密钥轮换、密钥撤销
- [**密钥恢复**](05_Key_Management/05_Key_Recovery/) - 密钥备份、密钥恢复机制

## 核心概念

### 对称密码学原理

对称密码学使用相同的密钥进行加密和解密：

**加密过程**：C = E(K, P)
**解密过程**：P = D(K, C)

其中：

- K：密钥
- P：明文
- C：密文
- E：加密函数
- D：解密函数

### 在Web3中的应用

#### 1. 数据加密

- **链下数据加密**：保护存储在IPFS等分布式存储中的敏感数据
- **状态加密**：加密智能合约的敏感状态数据
- **通信加密**：保护P2P网络中的消息传输

#### 2. 消息认证

- **交易签名验证**：确保交易数据的完整性
- **区块验证**：验证区块数据的完整性
- **协议消息认证**：保护共识协议消息

#### 3. 密钥派生

- **钱包密钥派生**：从种子短语派生多个密钥
- **会话密钥生成**：为临时通信生成密钥
- **密钥分层**：建立密钥层次结构

## 实际项目案例

### 案例1：区块链钱包加密系统

#### 项目背景

实现一个安全的区块链钱包系统，使用对称密码学保护私钥和敏感数据。

#### 技术实现

```rust
use aes_gcm::{Aes256Gcm, Key, Nonce};
use aes_gcm::aead::{Aead, NewAead};
use argon2::{self, Config};
use rand::{Rng, RngCore};
use serde::{Serialize, Deserialize};
use sha2::{Sha256, Digest};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EncryptedWallet {
    pub encrypted_data: Vec<u8>,
    pub salt: Vec<u8>,
    pub nonce: Vec<u8>,
    pub tag: Vec<u8>,
}

pub struct WalletEncryption {
    master_key: [u8; 32],
}

impl WalletEncryption {
    pub fn new(password: &str, salt: &[u8]) -> Self {
        // 使用Argon2派生主密钥
        let config = Config::default();
        let mut master_key = [0u8; 32];
        argon2::hash_raw(password.as_bytes(), salt, &config)
            .unwrap()
            .copy_to_slice(&mut master_key);
        
        WalletEncryption { master_key }
    }
    
    pub fn encrypt_wallet(&self, wallet_data: &[u8]) -> EncryptedWallet {
        let mut rng = rand::thread_rng();
        
        // 生成随机盐和随机数
        let mut salt = [0u8; 16];
        let mut nonce_bytes = [0u8; 12];
        rng.fill_bytes(&mut salt);
        rng.fill_bytes(&mut nonce_bytes);
        
        // 创建AES-GCM密钥和随机数
        let key = Key::from_slice(&self.master_key);
        let nonce = Nonce::from_slice(&nonce_bytes);
        let cipher = Aes256Gcm::new(key);
        
        // 加密数据
        let encrypted_data = cipher.encrypt(nonce, wallet_data)
            .expect("Encryption failed");
        
        // 分离密文和认证标签
        let (ciphertext, tag) = encrypted_data.split_at(encrypted_data.len() - 16);
        
        EncryptedWallet {
            encrypted_data: ciphertext.to_vec(),
            salt: salt.to_vec(),
            nonce: nonce_bytes.to_vec(),
            tag: tag.to_vec(),
        }
    }
    
    pub fn decrypt_wallet(&self, encrypted_wallet: &EncryptedWallet) -> Result<Vec<u8>, String> {
        // 重建AES-GCM密钥和随机数
        let key = Key::from_slice(&self.master_key);
        let nonce = Nonce::from_slice(&encrypted_wallet.nonce);
        let cipher = Aes256Gcm::new(key);
        
        // 重建完整密文
        let mut full_ciphertext = encrypted_wallet.encrypted_data.clone();
        full_ciphertext.extend_from_slice(&encrypted_wallet.tag);
        
        // 解密数据
        cipher.decrypt(nonce, full_ciphertext.as_slice())
            .map_err(|e| format!("Decryption failed: {}", e))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WalletData {
    pub private_keys: Vec<String>,
    pub addresses: Vec<String>,
    pub metadata: HashMap<String, String>,
}

impl WalletData {
    pub fn new() -> Self {
        WalletData {
            private_keys: Vec::new(),
            addresses: Vec::new(),
            metadata: HashMap::new(),
        }
    }
    
    pub fn add_key(&mut self, private_key: String, address: String) {
        self.private_keys.push(private_key);
        self.addresses.push(address);
    }
    
    pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
        serde_json::to_vec(self)
            .map_err(|e| format!("Serialization failed: {}", e))
    }
    
    pub fn from_bytes(data: &[u8]) -> Result<Self, String> {
        serde_json::from_slice(data)
            .map_err(|e| format!("Deserialization failed: {}", e))
    }
}

pub struct SecureWallet {
    encryption: WalletEncryption,
    wallet_data: WalletData,
}

impl SecureWallet {
    pub fn new(password: &str) -> Self {
        let mut rng = rand::thread_rng();
        let mut salt = [0u8; 16];
        rng.fill_bytes(&mut salt);
        
        let encryption = WalletEncryption::new(password, &salt);
        let wallet_data = WalletData::new();
        
        SecureWallet {
            encryption,
            wallet_data,
        }
    }
    
    pub fn unlock(&mut self, password: &str, encrypted_wallet: &EncryptedWallet) -> Result<(), String> {
        // 重新创建加密器
        let encryption = WalletEncryption::new(password, &encrypted_wallet.salt);
        
        // 解密钱包数据
        let decrypted_data = encryption.decrypt_wallet(encrypted_wallet)?;
        self.wallet_data = WalletData::from_bytes(&decrypted_data)?;
        self.encryption = encryption;
        
        Ok(())
    }
    
    pub fn lock(&self) -> Result<EncryptedWallet, String> {
        let wallet_bytes = self.wallet_data.to_bytes()?;
        Ok(self.encryption.encrypt_wallet(&wallet_bytes))
    }
    
    pub fn add_key(&mut self, private_key: String, address: String) {
        self.wallet_data.add_key(private_key, address);
    }
    
    pub fn get_addresses(&self) -> &Vec<String> {
        &self.wallet_data.addresses
    }
    
    pub fn export_encrypted(&self) -> Result<EncryptedWallet, String> {
        self.lock()
    }
}
```

#### 项目成果

- 实现了基于AES-GCM的安全钱包加密系统
- 使用Argon2进行密钥派生，抵抗暴力破解
- 支持钱包的加密存储和解密加载
- 提供了完整的密钥管理功能

### 案例2：分布式存储数据加密

#### 项目背景1

实现一个用于IPFS等分布式存储系统的数据加密层，保护存储在公共网络中的敏感数据。

#### 技术实现1

```rust
use aes_gcm::{Aes256Gcm, Key, Nonce};
use aes_gcm::aead::{Aead, NewAead};
use rand::{Rng, RngCore};
use serde::{Serialize, Deserialize};
use sha2::{Sha256, Digest};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EncryptedData {
    pub ciphertext: Vec<u8>,
    pub nonce: Vec<u8>,
    pub tag: Vec<u8>,
    pub metadata: DataMetadata,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataMetadata {
    pub version: u8,
    pub algorithm: String,
    pub key_id: String,
    pub created_at: u64,
    pub size: usize,
}

pub struct DataEncryption {
    key: [u8; 32],
}

impl DataEncryption {
    pub fn new(key: [u8; 32]) -> Self {
        DataEncryption { key }
    }
    
    pub fn encrypt_data(&self, data: &[u8], key_id: &str) -> EncryptedData {
        let mut rng = rand::thread_rng();
        
        // 生成随机数
        let mut nonce_bytes = [0u8; 12];
        rng.fill_bytes(&mut nonce_bytes);
        
        // 创建AES-GCM密钥和随机数
        let key = Key::from_slice(&self.key);
        let nonce = Nonce::from_slice(&nonce_bytes);
        let cipher = Aes256Gcm::new(key);
        
        // 加密数据
        let encrypted_data = cipher.encrypt(nonce, data)
            .expect("Encryption failed");
        
        // 分离密文和认证标签
        let (ciphertext, tag) = encrypted_data.split_at(encrypted_data.len() - 16);
        
        let metadata = DataMetadata {
            version: 1,
            algorithm: "AES-256-GCM".to_string(),
            key_id: key_id.to_string(),
            created_at: chrono::Utc::now().timestamp() as u64,
            size: data.len(),
        };
        
        EncryptedData {
            ciphertext: ciphertext.to_vec(),
            nonce: nonce_bytes.to_vec(),
            tag: tag.to_vec(),
            metadata,
        }
    }
    
    pub fn decrypt_data(&self, encrypted_data: &EncryptedData) -> Result<Vec<u8>, String> {
        // 重建AES-GCM密钥和随机数
        let key = Key::from_slice(&self.key);
        let nonce = Nonce::from_slice(&encrypted_data.nonce);
        let cipher = Aes256Gcm::new(key);
        
        // 重建完整密文
        let mut full_ciphertext = encrypted_data.ciphertext.clone();
        full_ciphertext.extend_from_slice(&encrypted_data.tag);
        
        // 解密数据
        cipher.decrypt(nonce, full_ciphertext.as_slice())
            .map_err(|e| format!("Decryption failed: {}", e))
    }
}

pub struct DistributedStorageEncryption {
    encryption: DataEncryption,
    key_manager: KeyManager,
}

#[derive(Debug, Clone)]
pub struct KeyManager {
    keys: HashMap<String, [u8; 32]>,
}

impl KeyManager {
    pub fn new() -> Self {
        KeyManager {
            keys: HashMap::new(),
        }
    }
    
    pub fn generate_key(&mut self, key_id: &str) -> [u8; 32] {
        let mut key = [0u8; 32];
        rand::thread_rng().fill_bytes(&mut key);
        self.keys.insert(key_id.to_string(), key);
        key
    }
    
    pub fn get_key(&self, key_id: &str) -> Option<&[u8; 32]> {
        self.keys.get(key_id)
    }
    
    pub fn remove_key(&mut self, key_id: &str) {
        self.keys.remove(key_id);
    }
}

impl DistributedStorageEncryption {
    pub fn new() -> Self {
        let key_manager = KeyManager::new();
        let default_key = [0u8; 32]; // 临时默认密钥
        
        DistributedStorageEncryption {
            encryption: DataEncryption::new(default_key),
            key_manager,
        }
    }
    
    pub fn encrypt_for_storage(&mut self, data: &[u8], key_id: &str) -> EncryptedData {
        // 生成或获取密钥
        let key = if let Some(existing_key) = self.key_manager.get_key(key_id) {
            *existing_key
        } else {
            self.key_manager.generate_key(key_id)
        };
        
        // 创建加密器
        let encryption = DataEncryption::new(key);
        
        // 加密数据
        encryption.encrypt_data(data, key_id)
    }
    
    pub fn decrypt_from_storage(&self, encrypted_data: &EncryptedData) -> Result<Vec<u8>, String> {
        let key_id = &encrypted_data.metadata.key_id;
        
        // 获取密钥
        let key = self.key_manager.get_key(key_id)
            .ok_or_else(|| format!("Key not found: {}", key_id))?;
        
        // 创建加密器
        let encryption = DataEncryption::new(*key);
        
        // 解密数据
        encryption.decrypt_data(encrypted_data)
    }
    
    pub fn store_encrypted(&self, encrypted_data: &EncryptedData) -> String {
        // 序列化加密数据
        let serialized = serde_json::to_string(encrypted_data)
            .expect("Serialization failed");
        
        // 计算哈希作为存储ID
        let mut hasher = Sha256::new();
        hasher.update(serialized.as_bytes());
        let hash = hasher.finalize();
        
        // 返回十六进制哈希作为存储ID
        format!("{:x}", hash)
    }
    
    pub fn load_encrypted(&self, storage_id: &str, encrypted_json: &str) -> Result<EncryptedData, String> {
        // 验证存储ID
        let mut hasher = Sha256::new();
        hasher.update(encrypted_json.as_bytes());
        let hash = hasher.finalize();
        let expected_id = format!("{:x}", hash);
        
        if storage_id != expected_id {
            return Err("Storage ID mismatch".to_string());
        }
        
        // 反序列化加密数据
        serde_json::from_str(encrypted_json)
            .map_err(|e| format!("Deserialization failed: {}", e))
    }
}
```

#### 项目成果1

- 实现了分布式存储的数据加密层
- 支持多种密钥管理和数据版本控制
- 提供了数据完整性验证和存储ID生成
- 可用于IPFS、Filecoin等分布式存储系统

### 案例3：区块链交易消息认证

#### 项目背景2

实现一个基于HMAC的区块链交易消息认证系统，确保交易数据的完整性和真实性。

#### 技术实现2

```rust
use hmac::{Hmac, Mac, NewMac};
use sha2::{Sha256, Digest};
use serde::{Serialize, Deserialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transaction {
    pub from: String,
    pub to: String,
    pub amount: u64,
    pub nonce: u64,
    pub timestamp: u64,
    pub signature: String,
    pub mac: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransactionMAC {
    pub transaction_hash: String,
    pub mac: String,
    pub key_id: String,
    pub timestamp: u64,
}

pub struct TransactionAuthenticator {
    mac_keys: HashMap<String, Vec<u8>>,
    current_key_id: String,
}

impl TransactionAuthenticator {
    pub fn new() -> Self {
        let mut mac_keys = HashMap::new();
        let key_id = "key_001".to_string();
        
        // 生成MAC密钥
        let mut key = [0u8; 32];
        rand::thread_rng().fill_bytes(&mut key);
        mac_keys.insert(key_id.clone(), key.to_vec());
        
        TransactionAuthenticator {
            mac_keys,
            current_key_id: key_id,
        }
    }
    
    pub fn create_transaction(&self, from: &str, to: &str, amount: u64) -> Transaction {
        let nonce = rand::thread_rng().gen::<u64>();
        let timestamp = chrono::Utc::now().timestamp() as u64;
        
        let mut transaction = Transaction {
            from: from.to_string(),
            to: to.to_string(),
            amount,
            nonce,
            timestamp,
            signature: String::new(),
            mac: String::new(),
        };
        
        // 计算交易哈希
        let transaction_hash = self.calculate_transaction_hash(&transaction);
        
        // 生成MAC
        let mac = self.generate_mac(&transaction_hash);
        
        transaction.mac = mac;
        transaction
    }
    
    pub fn calculate_transaction_hash(&self, transaction: &Transaction) -> String {
        let mut hasher = Sha256::new();
        
        // 计算不包括签名和MAC的哈希
        hasher.update(transaction.from.as_bytes());
        hasher.update(transaction.to.as_bytes());
        hasher.update(transaction.amount.to_le_bytes());
        hasher.update(transaction.nonce.to_le_bytes());
        hasher.update(transaction.timestamp.to_le_bytes());
        
        format!("{:x}", hasher.finalize())
    }
    
    pub fn generate_mac(&self, data: &str) -> String {
        let key = self.mac_keys.get(&self.current_key_id)
            .expect("MAC key not found");
        
        let mut mac = Hmac::<Sha256>::new_from_slice(key)
            .expect("HMAC creation failed");
        
        mac.update(data.as_bytes());
        format!("{:x}", mac.finalize().into_bytes())
    }
    
    pub fn verify_transaction(&self, transaction: &Transaction) -> bool {
        // 计算交易哈希
        let transaction_hash = self.calculate_transaction_hash(transaction);
        
        // 验证MAC
        let expected_mac = self.generate_mac(&transaction_hash);
        transaction.mac == expected_mac
    }
    
    pub fn rotate_mac_key(&mut self) {
        let new_key_id = format!("key_{:03}", self.mac_keys.len() + 1);
        
        // 生成新密钥
        let mut new_key = [0u8; 32];
        rand::thread_rng().fill_bytes(&mut new_key);
        self.mac_keys.insert(new_key_id.clone(), new_key.to_vec());
        
        // 更新当前密钥ID
        self.current_key_id = new_key_id;
    }
    
    pub fn get_key_info(&self) -> Vec<String> {
        self.mac_keys.keys().cloned().collect()
    }
}

pub struct BlockchainMessageAuth {
    authenticator: TransactionAuthenticator,
    pending_transactions: Vec<Transaction>,
    verified_transactions: Vec<Transaction>,
}

impl BlockchainMessageAuth {
    pub fn new() -> Self {
        BlockchainMessageAuth {
            authenticator: TransactionAuthenticator::new(),
            pending_transactions: Vec::new(),
            verified_transactions: Vec::new(),
        }
    }
    
    pub fn submit_transaction(&mut self, from: &str, to: &str, amount: u64) -> Transaction {
        let transaction = self.authenticator.create_transaction(from, to, amount);
        self.pending_transactions.push(transaction.clone());
        transaction
    }
    
    pub fn verify_pending_transactions(&mut self) -> Vec<Transaction> {
        let mut verified = Vec::new();
        let mut invalid = Vec::new();
        
        for transaction in self.pending_transactions.drain(..) {
            if self.authenticator.verify_transaction(&transaction) {
                verified.push(transaction);
            } else {
                invalid.push(transaction);
            }
        }
        
        // 将验证通过的交易移到已验证列表
        self.verified_transactions.extend(verified.clone());
        
        verified
    }
    
    pub fn get_transaction_statistics(&self) -> (usize, usize) {
        (self.pending_transactions.len(), self.verified_transactions.len())
    }
    
    pub fn rotate_keys(&mut self) {
        self.authenticator.rotate_mac_key();
    }
    
    pub fn export_verified_transactions(&self) -> Vec<Transaction> {
        self.verified_transactions.clone()
    }
}
```

#### 项目成果2

- 实现了基于HMAC的交易消息认证系统
- 支持交易数据的完整性验证
- 提供了密钥轮换和交易统计功能
- 可用于区块链交易的安全验证

## 学习资源

### 推荐教材

1. **密码学基础**：《Applied Cryptography》- Bruce Schneier
2. **对称密码学**：《The Design of Rijndael》- Joan Daemen
3. **哈希函数**：《Handbook of Applied Cryptography》- Alfred Menezes
4. **密钥管理**：《Cryptography Engineering》- Ferguson, Schneier, Kohno

### 在线资源

- [AES标准](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197.pdf)
- [SHA-3标准](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf)
- [HMAC标准](https://tools.ietf.org/html/rfc2104)

## 贡献指南

欢迎对对称密码学内容进行贡献。请确保：

1. 所有算法都有详细的实现说明
2. 包含在Web3中的具体应用场景
3. 提供Rust代码实现示例
4. 说明算法的安全性和性能特点
5. 关注最新的密码学研究成果
