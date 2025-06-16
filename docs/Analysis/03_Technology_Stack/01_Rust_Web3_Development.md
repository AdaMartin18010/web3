# Rust Web3开发技术栈分析

## 目录

1. [Rust在Web3中的优势](#1-rust在web3中的优势)
2. [核心库和框架](#2-核心库和框架)
3. [智能合约开发](#3-智能合约开发)
4. [性能优化技术](#4-性能优化技术)
5. [安全最佳实践](#5-安全最佳实践)
6. [测试策略](#6-测试策略)
7. [部署和监控](#7-部署和监控)

## 1. Rust在Web3中的优势

### 1.1 内存安全

**定义 1.1** (内存安全)
Rust通过所有权系统保证内存安全，满足以下性质：

- **无空指针解引用**：所有指针都保证非空
- **无悬垂指针**：指针不会指向已释放的内存
- **无数据竞争**：并发访问时不会产生数据竞争

**定理 1.1** (所有权系统正确性)
Rust的所有权系统可以静态检测所有内存安全问题。

**证明**：
通过类型系统和借用检查器，Rust编译器可以在编译时验证：

1. 每个值都有唯一的所有者
2. 借用规则得到遵守
3. 生命周期得到正确管理

这确保了运行时不会出现内存安全问题。■

### 1.2 零成本抽象

**定义 1.2** (零成本抽象)
Rust的抽象机制满足"零成本"原则：

$$\text{Cost}(abstraction) = \text{Cost}(equivalent\_manual\_code)$$

**定理 1.2** (零成本抽象定理)
Rust的泛型、trait和闭包都是零成本抽象。

**证明**：
1. **泛型**：编译时单态化，无运行时开销
2. **Trait**：静态分发，无虚函数调用开销
3. **闭包**：编译时优化，与普通函数性能相同■

### 1.3 并发安全

**定义 1.3** (并发安全)
Rust的类型系统保证并发安全：

$$\forall t_1, t_2 \in \text{Threads}: \text{Safe}(t_1 \parallel t_2)$$

**定理 1.3** (并发安全保证)
Rust的Send和Sync trait保证线程安全。

**证明**：
- **Send**：类型可以安全地发送到另一个线程
- **Sync**：类型可以安全地在多个线程间共享

编译器静态检查这些约束，确保并发安全。■

## 2. 核心库和框架

### 2.1 区块链框架

#### 2.1.1 Substrate框架

**定义 2.1** (Substrate框架)
Substrate是一个模块化区块链框架，提供：

- **运行时模块**：可配置的区块链逻辑
- **共识引擎**：可插拔的共识机制
- **网络层**：P2P网络通信
- **存储层**：键值存储系统

```rust
use substrate_runtime::{
    decl_module, decl_storage, decl_event, decl_error,
    dispatch::DispatchResult, ensure,
};

decl_module! {
    pub struct Module<T: Config> for enum Call where origin: T::Origin {
        #[weight = 10_000]
        pub fn transfer(origin, to: T::AccountId, amount: T::Balance) -> DispatchResult {
            let sender = ensure_signed(origin)?;
            
            // 检查余额
            let sender_balance = <Balances<T>>::get(&sender);
            ensure!(sender_balance >= amount, Error::<T>::InsufficientBalance);
            
            // 执行转账
            <Balances<T>>::mutate(&sender, |balance| *balance -= amount);
            <Balances<T>>::mutate(&to, |balance| *balance += amount);
            
            // 发出事件
            Self::deposit_event(Event::Transfer(sender, to, amount));
            
            Ok(())
        }
    }
}

decl_storage! {
    trait Store for Module<T: Config> as TemplateModule {
        Balances: map hasher(blake2_128_concat) T::AccountId => T::Balance;
    }
}

decl_event!(
    pub enum Event<T> where
        AccountId = <T as system::Config>::AccountId,
        Balance = <T as Config>::Balance,
    {
        Transfer(AccountId, AccountId, Balance),
    }
);

decl_error! {
    pub enum Error for Module<T: Config> {
        InsufficientBalance,
    }
}
```

#### 2.1.2 Solana框架

**定义 2.2** (Solana程序)
Solana程序是运行在Solana区块链上的智能合约：

```rust
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    entrypoint,
    entrypoint::ProgramResult,
    msg,
    program_error::ProgramError,
    pubkey::Pubkey,
    program_pack::{Pack, IsInitialized},
    sysvar::{rent::Rent, Sysvar},
};

entrypoint!(process_instruction);

pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let accounts_iter = &mut accounts.iter();
    let payer = next_account_info(accounts_iter)?;
    let account = next_account_info(accounts_iter)?;
    let rent = &Rent::from_account_info(next_account_info(accounts_iter)?)?;
    
    if !payer.is_signer {
        return Err(ProgramError::MissingRequiredSignature);
    }
    
    if !account.is_writable {
        return Err(ProgramError::InvalidAccountData);
    }
    
    if account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    
    // 处理指令
    msg!("Processing instruction");
    
    Ok(())
}
```

### 2.2 密码学库

#### 2.2.1 哈希函数

```rust
use sha2::{Sha256, Digest};
use ripemd::Ripemd160;
use blake2::{Blake2b, Digest as Blake2Digest};

pub struct HashUtils;

impl HashUtils {
    pub fn sha256(data: &[u8]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(data);
        let result = hasher.finalize();
        let mut hash = [0u8; 32];
        hash.copy_from_slice(&result);
        hash
    }
    
    pub fn ripemd160(data: &[u8]) -> [u8; 20] {
        let mut hasher = Ripemd160::new();
        hasher.update(data);
        let result = hasher.finalize();
        let mut hash = [0u8; 20];
        hash.copy_from_slice(&result);
        hash
    }
    
    pub fn blake2b(data: &[u8]) -> [u8; 64] {
        let mut hasher = Blake2b::new();
        hasher.update(data);
        let result = hasher.finalize();
        let mut hash = [0u8; 64];
        hash.copy_from_slice(&result);
        hash
    }
    
    pub fn double_sha256(data: &[u8]) -> [u8; 32] {
        Self::sha256(&Self::sha256(data))
    }
}
```

#### 2.2.2 数字签名

```rust
use secp256k1::{Secp256k1, SecretKey, PublicKey, Message, Signature};
use ed25519_dalek::{Keypair, PublicKey as EdPublicKey, SecretKey as EdSecretKey, Signature as EdSignature, Signer, Verifier};

pub struct CryptoService;

impl CryptoService {
    // ECDSA签名
    pub fn ecdsa_sign(private_key: &[u8], message: &[u8]) -> Result<Signature, Box<dyn std::error::Error>> {
        let secp = Secp256k1::new();
        let secret_key = SecretKey::from_slice(private_key)?;
        let message = Message::from_slice(message)?;
        let signature = secp.sign(&message, &secret_key);
        Ok(signature)
    }
    
    pub fn ecdsa_verify(public_key: &[u8], message: &[u8], signature: &Signature) -> Result<bool, Box<dyn std::error::Error>> {
        let secp = Secp256k1::new();
        let public_key = PublicKey::from_slice(public_key)?;
        let message = Message::from_slice(message)?;
        Ok(secp.verify(&message, signature, &public_key).is_ok())
    }
    
    // Ed25519签名
    pub fn ed25519_sign(keypair: &Keypair, message: &[u8]) -> EdSignature {
        keypair.sign(message)
    }
    
    pub fn ed25519_verify(public_key: &EdPublicKey, message: &[u8], signature: &EdSignature) -> bool {
        public_key.verify(message, signature).is_ok()
    }
}
```

### 2.3 网络通信

#### 2.3.1 libp2p集成

```rust
use libp2p::{
    core::{upgrade, transport, PeerId},
    floodsub::{Floodsub, FloodsubEvent, Topic},
    mdns::{Mdns, MdnsEvent},
    swarm::{NetworkBehaviourEventProcess, Swarm},
    tcp::TokioTcpConfig,
    noise,
    yamux,
};
use tokio::{io::{AsyncReadExt, AsyncWriteExt}, select};
use std::error::Error;

#[derive(NetworkBehaviour)]
struct MyBehaviour {
    floodsub: Floodsub,
    mdns: Mdns,
}

impl NetworkBehaviourEventProcess<FloodsubEvent> for MyBehaviour {
    fn inject_event(&mut self, event: FloodsubEvent) {
        match event {
            FloodsubEvent::Message(message) => {
                println!("Received message: {:?}", message.data);
            }
            _ => {}
        }
    }
}

impl NetworkBehaviourEventProcess<MdnsEvent> for MyBehaviour {
    fn inject_event(&mut self, event: MdnsEvent) {
        match event {
            MdnsEvent::Discovered(list) => {
                for (peer, _) in list {
                    self.floodsub.add_node_to_partial_view(peer);
                }
            }
            MdnsEvent::Expired(list) => {
                for (peer, _) in list {
                    if !self.mdns.has_node(&peer) {
                        self.floodsub.remove_node_from_partial_view(&peer);
                    }
                }
            }
        }
    }
}

pub struct P2PNetwork {
    swarm: Swarm<MyBehaviour>,
}

impl P2PNetwork {
    pub async fn new() -> Result<Self, Box<dyn Error>> {
        let local_key = identity::Keypair::generate_ed25519();
        let local_peer_id = PeerId::from(local_key.public());
        
        let noise_keys = noise::Keypair::<noise::X25519Spec>::new()
            .into_authentic(&local_key)
            .expect("Signing libp2p-noise static DH keypair failed.");
        
        let transport = TokioTcpConfig::new()
            .nodelay(true)
            .upgrade(upgrade::Version::V1)
            .authenticate(noise::NoiseConfig::xx(noise_keys).into_authenticated())
            .multiplex(yamux::YamuxConfig::default())
            .boxed();
        
        let mut behaviour = MyBehaviour {
            floodsub: Floodsub::new(local_peer_id),
            mdns: Mdns::new(Default::default()).await?,
        };
        
        let topic = Topic::new("blockchain");
        behaviour.floodsub.subscribe(topic.clone());
        
        let swarm = Swarm::new(transport, behaviour, local_peer_id);
        
        Ok(Self { swarm })
    }
    
    pub async fn run(&mut self) -> Result<(), Box<dyn Error>> {
        loop {
            select! {
                event = self.swarm.next() => {
                    match event {
                        Some(event) => {
                            // 处理网络事件
                            println!("Network event: {:?}", event);
                        }
                        None => break,
                    }
                }
            }
        }
        Ok(())
    }
}
```

## 3. 智能合约开发

### 3.1 Ink!框架

**定义 3.1** (Ink!智能合约)
Ink!是用于Substrate的智能合约语言，基于Rust：

```rust
#![cfg_attr(not(feature = "std"), no_std)]

use ink_lang as ink;

#[ink::contract]
mod token {
    use ink_storage::traits::SpreadAllocate;
    
    #[ink(storage)]
    #[derive(SpreadAllocate)]
    pub struct Token {
        /// 代币总供应量
        total_supply: Balance,
        /// 账户余额映射
        balances: ink_storage::Mapping<AccountId, Balance>,
        /// 授权映射
        allowances: ink_storage::Mapping<(AccountId, AccountId), Balance>,
        /// 合约所有者
        owner: AccountId,
    }
    
    #[ink(event)]
    pub struct Transfer {
        #[ink(topic)]
        from: Option<AccountId>,
        #[ink(topic)]
        to: Option<AccountId>,
        value: Balance,
    }
    
    #[ink(event)]
    pub struct Approval {
        #[ink(topic)]
        owner: AccountId,
        #[ink(topic)]
        spender: AccountId,
        value: Balance,
    }
    
    impl Token {
        #[ink(constructor)]
        pub fn new(initial_supply: Balance) -> Self {
            ink_lang::utils::initialize_contract(|contract: &mut Self| {
                contract.total_supply = initial_supply;
                contract.owner = Self::env().caller();
                contract.balances.insert(contract.owner, &initial_supply);
                
                Self::env().emit_event(Transfer {
                    from: None,
                    to: Some(contract.owner),
                    value: initial_supply,
                });
            })
        }
        
        #[ink(message)]
        pub fn total_supply(&self) -> Balance {
            self.total_supply
        }
        
        #[ink(message)]
        pub fn balance_of(&self, owner: AccountId) -> Balance {
            self.balances.get(owner).unwrap_or(0)
        }
        
        #[ink(message)]
        pub fn transfer(&mut self, to: AccountId, value: Balance) -> bool {
            let from = self.env().caller();
            self.transfer_from_to(from, to, value)
        }
        
        #[ink(message)]
        pub fn approve(&mut self, spender: AccountId, value: Balance) -> bool {
            let owner = self.env().caller();
            self.allowances.insert((owner, spender), &value);
            
            self.env().emit_event(Approval {
                owner,
                spender,
                value,
            });
            
            true
        }
        
        #[ink(message)]
        pub fn transfer_from(&mut self, from: AccountId, to: AccountId, value: Balance) -> bool {
            let caller = self.env().caller();
            let allowance = self.allowances.get((from, caller)).unwrap_or(0);
            
            if allowance < value {
                return false;
            }
            
            self.allowances.insert((from, caller), &(allowance - value));
            self.transfer_from_to(from, to, value)
        }
        
        fn transfer_from_to(&mut self, from: AccountId, to: AccountId, value: Balance) -> bool {
            let from_balance = self.balances.get(from).unwrap_or(0);
            
            if from_balance < value {
                return false;
            }
            
            self.balances.insert(from, &(from_balance - value));
            let to_balance = self.balances.get(to).unwrap_or(0);
            self.balances.insert(to, &(to_balance + value));
            
            self.env().emit_event(Transfer {
                from: Some(from),
                to: Some(to),
                value,
            });
            
            true
        }
    }
    
    #[cfg(test)]
    mod tests {
        use super::*;
        use ink_lang as ink;
        
        #[ink::test]
        fn new_works() {
            let contract = Token::new(100);
            assert_eq!(contract.total_supply(), 100);
        }
        
        #[ink::test]
        fn transfer_works() {
            let mut contract = Token::new(100);
            let accounts = ink_env::test::default_accounts::<ink_env::DefaultEnvironment>();
            
            assert_eq!(contract.balance_of(accounts.alice), 100);
            assert!(contract.transfer(accounts.bob, 50));
            assert_eq!(contract.balance_of(accounts.alice), 50);
            assert_eq!(contract.balance_of(accounts.bob), 50);
        }
    }
}
```

### 3.2 合约测试策略

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use ink_env::test;
    
    fn set_sender(sender: AccountId) {
        ink_env::test::set_caller::<Environment>(sender);
    }
    
    fn set_balance(account: AccountId, balance: Balance) {
        ink_env::test::set_account_balance::<Environment>(account, balance);
    }
    
    #[ink::test]
    fn test_token_transfer() {
        let accounts = test::default_accounts::<Environment>();
        let mut token = Token::new(1000);
        
        set_sender(accounts.alice);
        set_balance(accounts.alice, 1000);
        
        // 测试转账
        assert!(token.transfer(accounts.bob, 500));
        assert_eq!(token.balance_of(accounts.alice), 500);
        assert_eq!(token.balance_of(accounts.bob), 500);
        
        // 测试余额不足
        assert!(!token.transfer(accounts.bob, 1000));
    }
    
    #[ink::test]
    fn test_approval_and_transfer_from() {
        let accounts = test::default_accounts::<Environment>();
        let mut token = Token::new(1000);
        
        set_sender(accounts.alice);
        set_balance(accounts.alice, 1000);
        
        // 授权
        assert!(token.approve(accounts.bob, 300));
        
        // 使用授权转账
        set_sender(accounts.bob);
        assert!(token.transfer_from(accounts.alice, accounts.charlie, 200));
        assert_eq!(token.balance_of(accounts.alice), 800);
        assert_eq!(token.balance_of(accounts.charlie), 200);
        
        // 测试授权不足
        assert!(!token.transfer_from(accounts.alice, accounts.charlie, 200));
    }
}
```

## 4. 性能优化技术

### 4.1 内存管理

**定义 4.1** (内存优化)
Rust的内存优化策略包括：

- **零拷贝**：避免不必要的数据复制
- **内存池**：重用内存分配
- **SIMD优化**：利用向量化指令

```rust
use std::alloc::{alloc, dealloc, Layout};
use std::ptr::NonNull;

pub struct MemoryPool {
    blocks: Vec<NonNull<u8>>,
    block_size: usize,
    layout: Layout,
}

impl MemoryPool {
    pub fn new(block_size: usize, capacity: usize) -> Self {
        let layout = Layout::from_size_align(block_size, 8).unwrap();
        let mut blocks = Vec::with_capacity(capacity);
        
        for _ in 0..capacity {
            unsafe {
                let ptr = alloc(layout);
                if !ptr.is_null() {
                    blocks.push(NonNull::new_unchecked(ptr));
                }
            }
        }
        
        Self { blocks, block_size, layout }
    }
    
    pub fn allocate(&mut self) -> Option<NonNull<u8>> {
        self.blocks.pop()
    }
    
    pub fn deallocate(&mut self, ptr: NonNull<u8>) {
        self.blocks.push(ptr);
    }
}

impl Drop for MemoryPool {
    fn drop(&mut self) {
        for ptr in &self.blocks {
            unsafe {
                dealloc(ptr.as_ptr(), self.layout);
            }
        }
    }
}
```

### 4.2 并发优化

```rust
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;
use tokio::sync::mpsc;

pub struct AsyncTaskQueue {
    sender: mpsc::Sender<Box<dyn FnOnce() + Send>>,
    workers: Vec<tokio::task::JoinHandle<()>>,
}

impl AsyncTaskQueue {
    pub fn new(worker_count: usize) -> Self {
        let (sender, mut receiver) = mpsc::channel(1000);
        let mut workers = Vec::new();
        
        for _ in 0..worker_count {
            let mut receiver = receiver.clone();
            let worker = tokio::spawn(async move {
                while let Some(task) = receiver.recv().await {
                    task();
                }
            });
            workers.push(worker);
        }
        
        Self { sender, workers }
    }
    
    pub async fn submit<F>(&self, task: F) -> Result<(), mpsc::error::SendError<Box<dyn FnOnce() + Send>>>
    where
        F: FnOnce() + Send + 'static,
    {
        self.sender.send(Box::new(task)).await
    }
    
    pub async fn shutdown(self) {
        drop(self.sender);
        for worker in self.workers {
            let _ = worker.await;
        }
    }
}
```

## 5. 安全最佳实践

### 5.1 输入验证

```rust
use std::collections::HashMap;

pub struct InputValidator;

impl InputValidator {
    pub fn validate_address(address: &str) -> Result<(), String> {
        if address.len() != 42 || !address.starts_with("0x") {
            return Err("Invalid address format".to_string());
        }
        
        if !address[2..].chars().all(|c| c.is_ascii_hexdigit()) {
            return Err("Invalid hex characters".to_string());
        }
        
        Ok(())
    }
    
    pub fn validate_amount(amount: u64, max_amount: u64) -> Result<(), String> {
        if amount == 0 {
            return Err("Amount cannot be zero".to_string());
        }
        
        if amount > max_amount {
            return Err("Amount exceeds maximum".to_string());
        }
        
        Ok(())
    }
    
    pub fn sanitize_string(input: &str) -> String {
        input
            .chars()
            .filter(|c| c.is_alphanumeric() || c.is_whitespace())
            .collect()
    }
}
```

### 5.2 加密安全

```rust
use rand::{Rng, rngs::OsRng};
use aes_gcm::{Aes256Gcm, Key, Nonce};
use aes_gcm::aead::{Aead, NewAead};

pub struct CryptoUtils;

impl CryptoUtils {
    pub fn generate_random_bytes(length: usize) -> Vec<u8> {
        let mut rng = OsRng::default();
        let mut bytes = vec![0u8; length];
        rng.fill(&mut bytes);
        bytes
    }
    
    pub fn encrypt_aes_gcm(key: &[u8], plaintext: &[u8]) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let cipher = Aes256Gcm::new_from_slice(key)?;
        let nonce = Nonce::from_slice(b"unique nonce");
        let ciphertext = cipher.encrypt(nonce, plaintext)?;
        Ok(ciphertext)
    }
    
    pub fn decrypt_aes_gcm(key: &[u8], ciphertext: &[u8]) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let cipher = Aes256Gcm::new_from_slice(key)?;
        let nonce = Nonce::from_slice(b"unique nonce");
        let plaintext = cipher.decrypt(nonce, ciphertext)?;
        Ok(plaintext)
    }
}
```

## 6. 测试策略

### 6.1 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_hash_functions() {
        let data = b"Hello, World!";
        let sha256_hash = HashUtils::sha256(data);
        let ripemd160_hash = HashUtils::ripemd160(data);
        
        assert_eq!(sha256_hash.len(), 32);
        assert_eq!(ripemd160_hash.len(), 20);
        
        // 验证哈希的一致性
        let sha256_hash2 = HashUtils::sha256(data);
        assert_eq!(sha256_hash, sha256_hash2);
    }
    
    #[test]
    fn test_crypto_signatures() {
        let private_key = b"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
        let message = b"Test message";
        
        let signature = CryptoService::ecdsa_sign(private_key, message).unwrap();
        let public_key = [0u8; 33]; // 实际应用中需要从私钥派生
        
        let is_valid = CryptoService::ecdsa_verify(&public_key, message, &signature).unwrap();
        assert!(is_valid);
    }
    
    #[test]
    fn test_input_validation() {
        // 测试地址验证
        assert!(InputValidator::validate_address("0x1234567890123456789012345678901234567890").is_ok());
        assert!(InputValidator::validate_address("invalid").is_err());
        
        // 测试金额验证
        assert!(InputValidator::validate_amount(100, 1000).is_ok());
        assert!(InputValidator::validate_amount(0, 1000).is_err());
        assert!(InputValidator::validate_amount(2000, 1000).is_err());
    }
}
```

### 6.2 集成测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    use tokio::test;
    
    #[test]
    async fn test_p2p_network() {
        let mut network1 = P2PNetwork::new().await.unwrap();
        let mut network2 = P2PNetwork::new().await.unwrap();
        
        // 测试网络连接和消息传递
        // 实际实现中需要更复杂的测试逻辑
    }
    
    #[test]
    async fn test_async_task_queue() {
        let queue = AsyncTaskQueue::new(4);
        let counter = Arc::new(Mutex::new(0));
        
        for _ in 0..10 {
            let counter = counter.clone();
            queue.submit(move || {
                let mut count = counter.lock().unwrap();
                *count += 1;
            }).await.unwrap();
        }
        
        // 等待任务完成
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        
        let final_count = *counter.lock().unwrap();
        assert_eq!(final_count, 10);
    }
}
```

## 7. 部署和监控

### 7.1 配置管理

```rust
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;

#[derive(Debug, Serialize, Deserialize)]
pub struct Config {
    pub network: NetworkConfig,
    pub database: DatabaseConfig,
    pub security: SecurityConfig,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct NetworkConfig {
    pub port: u16,
    pub max_peers: usize,
    pub bootstrap_nodes: Vec<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DatabaseConfig {
    pub path: String,
    pub max_size: usize,
    pub cache_size: usize,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct SecurityConfig {
    pub private_key_path: String,
    pub enable_tls: bool,
    pub certificate_path: Option<String>,
}

impl Config {
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn std::error::Error>> {
        let content = fs::read_to_string(path)?;
        let config: Config = serde_json::from_str(&content)?;
        Ok(config)
    }
    
    pub fn save<P: AsRef<Path>>(&self, path: P) -> Result<(), Box<dyn std::error::Error>> {
        let content = serde_json::to_string_pretty(self)?;
        fs::write(path, content)?;
        Ok(())
    }
}
```

### 7.2 指标收集

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::collections::HashMap;
use std::sync::Mutex;

pub struct Metrics {
    counters: HashMap<String, AtomicU64>,
    gauges: HashMap<String, AtomicU64>,
    histograms: HashMap<String, Mutex<Vec<f64>>>,
}

impl Metrics {
    pub fn new() -> Self {
        Self {
            counters: HashMap::new(),
            gauges: HashMap::new(),
            histograms: HashMap::new(),
        }
    }
    
    pub fn increment_counter(&self, name: &str) {
        let counter = self.counters
            .entry(name.to_string())
            .or_insert_with(|| AtomicU64::new(0));
        counter.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn set_gauge(&self, name: &str, value: u64) {
        let gauge = self.gauges
            .entry(name.to_string())
            .or_insert_with(|| AtomicU64::new(0));
        gauge.store(value, Ordering::Relaxed);
    }
    
    pub fn record_histogram(&self, name: &str, value: f64) {
        let histogram = self.histograms
            .entry(name.to_string())
            .or_insert_with(|| Mutex::new(Vec::new()));
        
        if let Ok(mut hist) = histogram.lock() {
            hist.push(value);
        }
    }
    
    pub fn get_metrics(&self) -> String {
        let mut output = String::new();
        
        // 输出计数器
        for (name, counter) in &self.counters {
            output.push_str(&format!("{}: {}\n", name, counter.load(Ordering::Relaxed)));
        }
        
        // 输出仪表
        for (name, gauge) in &self.gauges {
            output.push_str(&format!("{}: {}\n", name, gauge.load(Ordering::Relaxed)));
        }
        
        // 输出直方图统计
        for (name, histogram) in &self.histograms {
            if let Ok(hist) = histogram.lock() {
                if !hist.is_empty() {
                    let min = hist.iter().fold(f64::INFINITY, |a, &b| a.min(b));
                    let max = hist.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
                    let avg = hist.iter().sum::<f64>() / hist.len() as f64;
                    output.push_str(&format!("{}: min={}, max={}, avg={}\n", name, min, max, avg));
                }
            }
        }
        
        output
    }
}
```

## 总结

本文档详细分析了Rust在Web3开发中的技术栈，包括：

1. **Rust优势**：内存安全、零成本抽象、并发安全
2. **核心框架**：Substrate、Solana、密码学库
3. **智能合约**：Ink!框架和测试策略
4. **性能优化**：内存管理和并发优化
5. **安全实践**：输入验证和加密安全
6. **测试策略**：单元测试和集成测试
7. **部署监控**：配置管理和指标收集

Rust凭借其安全性和性能优势，成为Web3开发的重要选择，特别是在需要高性能和强安全保证的区块链应用中。

---

**参考文献**：

1. Rust Programming Language Book
2. Substrate Documentation
3. Solana Program Framework
4. libp2p Documentation
5. Ink! Smart Contract Framework
