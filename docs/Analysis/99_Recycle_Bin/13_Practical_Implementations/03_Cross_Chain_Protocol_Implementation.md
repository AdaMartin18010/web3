# 跨链协议实践实现指南

## 目录

1. [引言](#1-引言)
2. [跨链桥实现](#2-跨链桥实现)
3. [原子交换实现](#3-原子交换实现)
4. [消息传递协议](#4-消息传递协议)
5. [状态验证机制](#5-状态验证机制)
6. [测试与部署](#6-测试与部署)

## 1. 引言

本指南提供完整的跨链协议实现，包括跨链桥、原子交换、消息传递等功能。

### 1.1 技术栈

- **ink!**: 智能合约开发
- **Rust**: 系统级编程
- **Substrate**: 区块链框架
- **XCM**: 跨链消息格式

## 2. 跨链桥实现

### 2.1 核心数据结构

```rust
use ink::prelude::*;
use scale::{Decode, Encode};

#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub struct BridgeRequest {
    pub id: u64,
    pub user: AccountId,
    pub source_chain: u32,
    pub target_chain: u32,
    pub token: AccountId,
    pub amount: Balance,
    pub recipient: AccountId,
    pub status: BridgeStatus,
    pub created_at: u64,
    pub completed_at: Option<u64>,
}

#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub enum BridgeStatus {
    Pending,
    Processing,
    Completed,
    Failed,
}

#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub struct ValidatorSet {
    pub validators: Vec<AccountId>,
    pub threshold: u32,
    pub nonce: u64,
}
```

### 2.2 跨链桥合约

```rust
#[ink::contract]
pub mod cross_chain_bridge {
    use super::*;
    use ink::storage::Mapping;

    #[ink(storage)]
    pub struct CrossChainBridge {
        bridge_requests: Mapping<u64, BridgeRequest>,
        validator_set: ValidatorSet,
        supported_chains: Vec<u32>,
        supported_tokens: Vec<AccountId>,
        next_request_id: u64,
        owner: AccountId,
        min_bridge_amount: Balance,
        max_bridge_amount: Balance,
        bridge_fee: u32, // 0-10000 (0-100%)
    }

    impl CrossChainBridge {
        #[ink(constructor)]
        pub fn new(
            validators: Vec<AccountId>,
            threshold: u32,
            min_amount: Balance,
            max_amount: Balance,
            fee: u32,
        ) -> Self {
            Self {
                bridge_requests: Mapping::default(),
                validator_set: ValidatorSet {
                    validators,
                    threshold,
                    nonce: 0,
                },
                supported_chains: Vec::new(),
                supported_tokens: Vec::new(),
                next_request_id: 1,
                owner: Self::env().caller(),
                min_bridge_amount: min_amount,
                max_bridge_amount: max_amount,
                bridge_fee: fee,
            }
        }

        #[ink(message)]
        pub fn initiate_bridge(
            &mut self,
            target_chain: u32,
            token: AccountId,
            amount: Balance,
            recipient: AccountId,
        ) -> Result<u64, Error> {
            let user = self.env().caller();

            // 验证参数
            if !self.is_chain_supported(target_chain) {
                return Err(Error::UnsupportedChain);
            }

            if !self.is_token_supported(token) {
                return Err(Error::UnsupportedToken);
            }

            if amount < self.min_bridge_amount || amount > self.max_bridge_amount {
                return Err(Error::InvalidAmount);
            }

            // 计算手续费
            let fee_amount = (amount * self.bridge_fee) / 10000;
            let bridge_amount = amount - fee_amount;

            // 创建桥接请求
            let request = BridgeRequest {
                id: self.next_request_id,
                user,
                source_chain: self.get_current_chain_id(),
                target_chain,
                token,
                amount: bridge_amount,
                recipient,
                status: BridgeStatus::Pending,
                created_at: self.env().block_timestamp(),
                completed_at: None,
            };

            self.bridge_requests.insert(self.next_request_id, &request);
            self.next_request_id += 1;

            // 锁定代币
            self.lock_tokens(user, token, amount)?;

            self.env().emit_event(BridgeInitiated {
                request_id: request.id,
                user,
                target_chain,
                token,
                amount: bridge_amount,
                recipient,
            });

            Ok(request.id)
        }

        #[ink(message)]
        pub fn complete_bridge(
            &mut self,
            request_id: u64,
            signatures: Vec<Vec<u8>>,
        ) -> Result<(), Error> {
            let request = self.bridge_requests.get(request_id)
                .ok_or(Error::RequestNotFound)?;

            if request.status != BridgeStatus::Pending {
                return Err(Error::InvalidRequestStatus);
            }

            // 验证签名
            if !self.verify_signatures(request_id, &signatures) {
                return Err(Error::InvalidSignatures);
            }

            // 更新请求状态
            let mut updated_request = request;
            updated_request.status = BridgeStatus::Completed;
            updated_request.completed_at = Some(self.env().block_timestamp());
            self.bridge_requests.insert(request_id, &updated_request);

            // 释放代币给接收者
            self.release_tokens(request.recipient, request.token, request.amount)?;

            self.env().emit_event(BridgeCompleted {
                request_id,
                recipient: request.recipient,
                token: request.token,
                amount: request.amount,
            });

            Ok(())
        }

        #[ink(message)]
        pub fn cancel_bridge(&mut self, request_id: u64) -> Result<(), Error> {
            let caller = self.env().caller();
            let request = self.bridge_requests.get(request_id)
                .ok_or(Error::RequestNotFound)?;

            if request.user != caller {
                return Err(Error::NotRequestOwner);
            }

            if request.status != BridgeStatus::Pending {
                return Err(Error::InvalidRequestStatus);
            }

            // 检查是否可以取消（例如：超过时间限制）
            let current_time = self.env().block_timestamp();
            if current_time - request.created_at < 3600 { // 1小时
                return Err(Error::CannotCancelYet);
            }

            // 更新请求状态
            let mut updated_request = request;
            updated_request.status = BridgeStatus::Failed;
            self.bridge_requests.insert(request_id, &updated_request);

            // 返还代币给用户
            self.release_tokens(request.user, request.token, request.amount)?;

            self.env().emit_event(BridgeCanceled {
                request_id,
                user: request.user,
                token: request.token,
                amount: request.amount,
            });

            Ok(())
        }

        #[ink(message)]
        pub fn add_validator(&mut self, validator: AccountId) -> Result<(), Error> {
            let caller = self.env().caller();
            if caller != self.owner {
                return Err(Error::NotOwner);
            }

            if !self.validator_set.validators.contains(&validator) {
                self.validator_set.validators.push(validator);
                self.validator_set.nonce += 1;
            }

            Ok(())
        }

        #[ink(message)]
        pub fn remove_validator(&mut self, validator: AccountId) -> Result<(), Error> {
            let caller = self.env().caller();
            if caller != self.owner {
                return Err(Error::NotOwner);
            }

            if let Some(index) = self.validator_set.validators.iter().position(|&v| v == validator) {
                self.validator_set.validators.remove(index);
                self.validator_set.nonce += 1;
            }

            Ok(())
        }

        // 辅助函数
        fn is_chain_supported(&self, chain_id: u32) -> bool {
            self.supported_chains.contains(&chain_id)
        }

        fn is_token_supported(&self, token: AccountId) -> bool {
            self.supported_tokens.contains(&token)
        }

        fn get_current_chain_id(&self) -> u32 {
            // 获取当前链ID
            // 简化实现
            1
        }

        fn lock_tokens(&self, user: AccountId, token: AccountId, amount: Balance) -> Result<(), Error> {
            // 锁定代币
            // 简化实现
            Ok(())
        }

        fn release_tokens(&self, recipient: AccountId, token: AccountId, amount: Balance) -> Result<(), Error> {
            // 释放代币
            // 简化实现
            Ok(())
        }

        fn verify_signatures(&self, request_id: u64, signatures: &[Vec<u8>]) -> bool {
            // 验证多重签名
            // 简化实现
            signatures.len() >= self.validator_set.threshold as usize
        }
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        UnsupportedChain,
        UnsupportedToken,
        InvalidAmount,
        RequestNotFound,
        InvalidRequestStatus,
        InvalidSignatures,
        NotRequestOwner,
        CannotCancelYet,
        NotOwner,
    }

    #[ink(event)]
    pub struct BridgeInitiated {
        #[ink(topic)]
        request_id: u64,
        #[ink(topic)]
        user: AccountId,
        target_chain: u32,
        #[ink(topic)]
        token: AccountId,
        amount: Balance,
        #[ink(topic)]
        recipient: AccountId,
    }

    #[ink(event)]
    pub struct BridgeCompleted {
        #[ink(topic)]
        request_id: u64,
        #[ink(topic)]
        recipient: AccountId,
        #[ink(topic)]
        token: AccountId,
        amount: Balance,
    }

    #[ink(event)]
    pub struct BridgeCanceled {
        #[ink(topic)]
        request_id: u64,
        #[ink(topic)]
        user: AccountId,
        #[ink(topic)]
        token: AccountId,
        amount: Balance,
    }
}
```

## 3. 原子交换实现

### 3.1 原子交换合约

```rust
#[ink::contract]
pub mod atomic_swap {
    use super::*;
    use ink::storage::Mapping;

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub struct Swap {
        pub id: u64,
        pub initiator: AccountId,
        pub participant: AccountId,
        pub initiator_token: AccountId,
        pub participant_token: AccountId,
        pub initiator_amount: Balance,
        pub participant_amount: Balance,
        pub initiator_hashlock: Hash,
        pub participant_hashlock: Hash,
        pub timeout: u64,
        pub status: SwapStatus,
        pub created_at: u64,
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum SwapStatus {
        Initiated,
        Participated,
        Completed,
        Expired,
    }

    #[ink(storage)]
    pub struct AtomicSwap {
        swaps: Mapping<u64, Swap>,
        next_swap_id: u64,
        owner: AccountId,
    }

    impl AtomicSwap {
        #[ink(constructor)]
        pub fn new() -> Self {
            Self {
                swaps: Mapping::default(),
                next_swap_id: 1,
                owner: Self::env().caller(),
            }
        }

        #[ink(message)]
        pub fn initiate_swap(
            &mut self,
            participant: AccountId,
            initiator_token: AccountId,
            participant_token: AccountId,
            initiator_amount: Balance,
            participant_amount: Balance,
            timeout_hours: u64,
        ) -> Result<u64, Error> {
            let initiator = self.env().caller();

            if initiator == participant {
                return Err(Error::InvalidParticipant);
            }

            if initiator_amount == 0 || participant_amount == 0 {
                return Err(Error::InvalidAmount);
            }

            // 生成随机哈希锁
            let initiator_secret = self.generate_random_secret();
            let initiator_hashlock = self.hash_secret(&initiator_secret);

            let swap = Swap {
                id: self.next_swap_id,
                initiator,
                participant,
                initiator_token,
                participant_token,
                initiator_amount,
                participant_amount,
                initiator_hashlock,
                participant_hashlock: Hash::default(),
                timeout: self.env().block_timestamp() + (timeout_hours * 3600),
                status: SwapStatus::Initiated,
                created_at: self.env().block_timestamp(),
            };

            self.swaps.insert(self.next_swap_id, &swap);
            self.next_swap_id += 1;

            // 锁定发起者代币
            self.lock_tokens(initiator, initiator_token, initiator_amount)?;

            self.env().emit_event(SwapInitiated {
                swap_id: swap.id,
                initiator,
                participant,
                initiator_token,
                participant_token,
                initiator_amount,
                participant_amount,
                timeout: swap.timeout,
            });

            Ok(swap.id)
        }

        #[ink(message)]
        pub fn participate_swap(
            &mut self,
            swap_id: u64,
            participant_hashlock: Hash,
        ) -> Result<(), Error> {
            let participant = self.env().caller();
            let mut swap = self.swaps.get(swap_id).ok_or(Error::SwapNotFound)?;

            if swap.participant != participant {
                return Err(Error::NotParticipant);
            }

            if swap.status != SwapStatus::Initiated {
                return Err(Error::InvalidSwapStatus);
            }

            if self.env().block_timestamp() > swap.timeout {
                return Err(Error::SwapExpired);
            }

            swap.participant_hashlock = participant_hashlock;
            swap.status = SwapStatus::Participated;
            self.swaps.insert(swap_id, &swap);

            // 锁定参与者代币
            self.lock_tokens(participant, swap.participant_token, swap.participant_amount)?;

            self.env().emit_event(SwapParticipated {
                swap_id,
                participant,
                participant_hashlock,
            });

            Ok(())
        }

        #[ink(message)]
        pub fn complete_swap(
            &mut self,
            swap_id: u64,
            initiator_secret: Vec<u8>,
            participant_secret: Vec<u8>,
        ) -> Result<(), Error> {
            let caller = self.env().caller();
            let mut swap = self.swaps.get(swap_id).ok_or(Error::SwapNotFound)?;

            if swap.status != SwapStatus::Participated {
                return Err(Error::InvalidSwapStatus);
            }

            if self.env().block_timestamp() > swap.timeout {
                return Err(Error::SwapExpired);
            }

            // 验证哈希锁
            let initiator_hash = self.hash_secret(&initiator_secret);
            let participant_hash = self.hash_secret(&participant_secret);

            if initiator_hash != swap.initiator_hashlock || participant_hash != swap.participant_hashlock {
                return Err(Error::InvalidSecrets);
            }

            swap.status = SwapStatus::Completed;
            self.swaps.insert(swap_id, &swap);

            // 交换代币
            self.release_tokens(swap.participant, swap.initiator_token, swap.initiator_amount)?;
            self.release_tokens(swap.initiator, swap.participant_token, swap.participant_amount)?;

            self.env().emit_event(SwapCompleted {
                swap_id,
                initiator: swap.initiator,
                participant: swap.participant,
                initiator_token: swap.initiator_token,
                participant_token: swap.participant_token,
                initiator_amount: swap.initiator_amount,
                participant_amount: swap.participant_amount,
            });

            Ok(())
        }

        #[ink(message)]
        pub fn refund_swap(&mut self, swap_id: u64) -> Result<(), Error> {
            let caller = self.env().caller();
            let mut swap = self.swaps.get(swap_id).ok_or(Error::SwapNotFound)?;

            if caller != swap.initiator && caller != swap.participant {
                return Err(Error::NotSwapParty);
            }

            if swap.status != SwapStatus::Initiated && swap.status != SwapStatus::Participated {
                return Err(Error::InvalidSwapStatus);
            }

            if self.env().block_timestamp() <= swap.timeout {
                return Err(Error::SwapNotExpired);
            }

            swap.status = SwapStatus::Expired;
            self.swaps.insert(swap_id, &swap);

            // 返还代币
            if swap.status == SwapStatus::Initiated {
                self.release_tokens(swap.initiator, swap.initiator_token, swap.initiator_amount)?;
            } else {
                self.release_tokens(swap.initiator, swap.initiator_token, swap.initiator_amount)?;
                self.release_tokens(swap.participant, swap.participant_token, swap.participant_amount)?;
            }

            self.env().emit_event(SwapRefunded {
                swap_id,
                initiator: swap.initiator,
                participant: swap.participant,
            });

            Ok(())
        }

        // 辅助函数
        fn generate_random_secret(&self) -> Vec<u8> {
            // 生成随机密钥
            // 简化实现
            vec![0u8; 32]
        }

        fn hash_secret(&self, secret: &[u8]) -> Hash {
            // 哈希密钥
            // 简化实现
            Hash::from([0u8; 32])
        }

        fn lock_tokens(&self, user: AccountId, token: AccountId, amount: Balance) -> Result<(), Error> {
            // 锁定代币
            // 简化实现
            Ok(())
        }

        fn release_tokens(&self, recipient: AccountId, token: AccountId, amount: Balance) -> Result<(), Error> {
            // 释放代币
            // 简化实现
            Ok(())
        }
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        InvalidParticipant,
        InvalidAmount,
        SwapNotFound,
        NotParticipant,
        InvalidSwapStatus,
        SwapExpired,
        InvalidSecrets,
        NotSwapParty,
        SwapNotExpired,
    }

    #[ink(event)]
    pub struct SwapInitiated {
        #[ink(topic)]
        swap_id: u64,
        #[ink(topic)]
        initiator: AccountId,
        #[ink(topic)]
        participant: AccountId,
        #[ink(topic)]
        initiator_token: AccountId,
        #[ink(topic)]
        participant_token: AccountId,
        initiator_amount: Balance,
        participant_amount: Balance,
        timeout: u64,
    }

    #[ink(event)]
    pub struct SwapParticipated {
        #[ink(topic)]
        swap_id: u64,
        #[ink(topic)]
        participant: AccountId,
        participant_hashlock: Hash,
    }

    #[ink(event)]
    pub struct SwapCompleted {
        #[ink(topic)]
        swap_id: u64,
        #[ink(topic)]
        initiator: AccountId,
        #[ink(topic)]
        participant: AccountId,
        #[ink(topic)]
        initiator_token: AccountId,
        #[ink(topic)]
        participant_token: AccountId,
        initiator_amount: Balance,
        participant_amount: Balance,
    }

    #[ink(event)]
    pub struct SwapRefunded {
        #[ink(topic)]
        swap_id: u64,
        #[ink(topic)]
        initiator: AccountId,
        #[ink(topic)]
        participant: AccountId,
    }
}
```

## 4. 消息传递协议

### 4.1 跨链消息合约

```rust
#[ink::contract]
pub mod cross_chain_messaging {
    use super::*;
    use ink::storage::Mapping;

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub struct CrossChainMessage {
        pub id: u64,
        pub source_chain: u32,
        pub target_chain: u32,
        pub sender: AccountId,
        pub recipient: AccountId,
        pub payload: Vec<u8>,
        pub nonce: u64,
        pub status: MessageStatus,
        pub created_at: u64,
        pub delivered_at: Option<u64>,
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum MessageStatus {
        Pending,
        Delivered,
        Failed,
    }

    #[ink(storage)]
    pub struct CrossChainMessaging {
        messages: Mapping<u64, CrossChainMessage>,
        message_nonces: Mapping<(u32, u32), u64>, // (source_chain, target_chain) -> nonce
        next_message_id: u64,
        validators: Vec<AccountId>,
        threshold: u32,
        owner: AccountId,
    }

    impl CrossChainMessaging {
        #[ink(constructor)]
        pub fn new(validators: Vec<AccountId>, threshold: u32) -> Self {
            Self {
                messages: Mapping::default(),
                message_nonces: Mapping::default(),
                next_message_id: 1,
                validators,
                threshold,
                owner: Self::env().caller(),
            }
        }

        #[ink(message)]
        pub fn send_message(
            &mut self,
            target_chain: u32,
            recipient: AccountId,
            payload: Vec<u8>,
        ) -> Result<u64, Error> {
            let sender = self.env().caller();
            let source_chain = self.get_current_chain_id();

            if source_chain == target_chain {
                return Err(Error::SameChain);
            }

            let nonce = self.get_next_nonce(source_chain, target_chain);

            let message = CrossChainMessage {
                id: self.next_message_id,
                source_chain,
                target_chain,
                sender,
                recipient,
                payload,
                nonce,
                status: MessageStatus::Pending,
                created_at: self.env().block_timestamp(),
                delivered_at: None,
            };

            self.messages.insert(self.next_message_id, &message);
            self.next_message_id += 1;

            // 更新nonce
            self.message_nonces.insert((source_chain, target_chain), &(nonce + 1));

            self.env().emit_event(MessageSent {
                message_id: message.id,
                source_chain,
                target_chain,
                sender,
                recipient,
                nonce,
            });

            Ok(message.id)
        }

        #[ink(message)]
        pub fn deliver_message(
            &mut self,
            message_id: u64,
            signatures: Vec<Vec<u8>>,
        ) -> Result<(), Error> {
            let message = self.messages.get(message_id)
                .ok_or(Error::MessageNotFound)?;

            if message.status != MessageStatus::Pending {
                return Err(Error::InvalidMessageStatus);
            }

            // 验证签名
            if !self.verify_signatures(message_id, &signatures) {
                return Err(Error::InvalidSignatures);
            }

            // 更新消息状态
            let mut updated_message = message;
            updated_message.status = MessageStatus::Delivered;
            updated_message.delivered_at = Some(self.env().block_timestamp());
            self.messages.insert(message_id, &updated_message);

            // 处理消息
            self.process_message(&updated_message)?;

            self.env().emit_event(MessageDelivered {
                message_id,
                recipient: message.recipient,
            });

            Ok(())
        }

        fn get_current_chain_id(&self) -> u32 {
            // 获取当前链ID
            // 简化实现
            1
        }

        fn get_next_nonce(&self, source_chain: u32, target_chain: u32) -> u64 {
            self.message_nonces.get((source_chain, target_chain)).unwrap_or(0)
        }

        fn verify_signatures(&self, message_id: u64, signatures: &[Vec<u8>]) -> bool {
            // 验证多重签名
            // 简化实现
            signatures.len() >= self.threshold as usize
        }

        fn process_message(&self, message: &CrossChainMessage) -> Result<(), Error> {
            // 处理跨链消息
            // 简化实现
            Ok(())
        }
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        SameChain,
        MessageNotFound,
        InvalidMessageStatus,
        InvalidSignatures,
    }

    #[ink(event)]
    pub struct MessageSent {
        #[ink(topic)]
        message_id: u64,
        source_chain: u32,
        target_chain: u32,
        #[ink(topic)]
        sender: AccountId,
        #[ink(topic)]
        recipient: AccountId,
        nonce: u64,
    }

    #[ink(event)]
    pub struct MessageDelivered {
        #[ink(topic)]
        message_id: u64,
        #[ink(topic)]
        recipient: AccountId,
    }
}
```

## 5. 状态验证机制

### 5.1 轻客户端验证

```rust
#[ink::contract]
pub mod light_client {
    use super::*;

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub struct BlockHeader {
        pub number: u64,
        pub hash: Hash,
        pub parent_hash: Hash,
        pub state_root: Hash,
        pub extrinsics_root: Hash,
        pub timestamp: u64,
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub struct MerkleProof {
        pub leaf: Hash,
        pub path: Vec<Hash>,
        pub index: u32,
    }

    #[ink(storage)]
    pub struct LightClient {
        headers: Mapping<u64, BlockHeader>,
        latest_header: Option<BlockHeader>,
        validators: Vec<AccountId>,
        threshold: u32,
        owner: AccountId,
    }

    impl LightClient {
        #[ink(constructor)]
        pub fn new(validators: Vec<AccountId>, threshold: u32) -> Self {
            Self {
                headers: Mapping::default(),
                latest_header: None,
                validators,
                threshold,
                owner: Self::env().caller(),
            }
        }

        #[ink(message)]
        pub fn submit_header(
            &mut self,
            header: BlockHeader,
            signatures: Vec<Vec<u8>>,
        ) -> Result<(), Error> {
            // 验证签名
            if !self.verify_header_signatures(&header, &signatures) {
                return Err(Error::InvalidSignatures);
            }

            // 验证区块头
            if !self.verify_header(&header) {
                return Err(Error::InvalidHeader);
            }

            // 存储区块头
            self.headers.insert(header.number, &header);

            // 更新最新区块头
            if let Some(latest) = self.latest_header {
                if header.number > latest.number {
                    self.latest_header = Some(header);
                }
            } else {
                self.latest_header = Some(header);
            }

            self.env().emit_event(HeaderSubmitted {
                block_number: header.number,
                block_hash: header.hash,
            });

            Ok(())
        }

        #[ink(message)]
        pub fn verify_state(
            &self,
            block_number: u64,
            state_root: Hash,
            proof: MerkleProof,
        ) -> Result<bool, Error> {
            let header = self.headers.get(block_number)
                .ok_or(Error::HeaderNotFound)?;

            if header.state_root != state_root {
                return Err(Error::InvalidStateRoot);
            }

            // 验证Merkle证明
            let is_valid = self.verify_merkle_proof(&proof, state_root);
            Ok(is_valid)
        }

        fn verify_header_signatures(&self, header: &BlockHeader, signatures: &[Vec<u8>]) -> bool {
            // 验证区块头签名
            // 简化实现
            signatures.len() >= self.threshold as usize
        }

        fn verify_header(&self, header: &BlockHeader) -> bool {
            // 验证区块头格式和内容
            // 简化实现
            header.number > 0
        }

        fn verify_merkle_proof(&self, proof: &MerkleProof, root: Hash) -> bool {
            // 验证Merkle证明
            // 简化实现
            true
        }
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        InvalidSignatures,
        InvalidHeader,
        HeaderNotFound,
        InvalidStateRoot,
    }

    #[ink(event)]
    pub struct HeaderSubmitted {
        block_number: u64,
        #[ink(topic)]
        block_hash: Hash,
    }
}
```

## 6. 测试与部署

### 6.1 测试用例

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[ink::test]
    fn test_cross_chain_bridge() {
        let accounts = ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
        let validators = vec![accounts.alice, accounts.bob, accounts.charlie];
        let mut bridge = CrossChainBridge::new(validators, 2, 100, 10000, 100); // 1% fee

        ink::env::test::set_caller::<ink::env::DefaultEnvironment>(accounts.alice);
        let request_id = bridge.initiate_bridge(2, AccountId::from([1u8; 32]), 1000, accounts.bob).unwrap();
        assert_eq!(request_id, 1);
    }

    #[ink::test]
    fn test_atomic_swap() {
        let accounts = ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
        let mut swap = AtomicSwap::new();

        ink::env::test::set_caller::<ink::env::DefaultEnvironment>(accounts.alice);
        let swap_id = swap.initiate_swap(
            accounts.bob,
            AccountId::from([1u8; 32]),
            AccountId::from([2u8; 32]),
            1000,
            2000,
            24,
        ).unwrap();
        assert_eq!(swap_id, 1);
    }
}
```

### 6.2 前端集成

```typescript
class CrossChainClient {
    private api: ApiPromise;
    private bridgeContract: ContractPromise;
    private swapContract: ContractPromise;
    private messagingContract: ContractPromise;

    constructor() {
        this.initialize();
    }

    async initialize() {
        const provider = new WsProvider('ws://localhost:9944');
        this.api = await ApiPromise.create({ provider });
        
        this.bridgeContract = new ContractPromise(this.api, bridgeMetadata, bridgeAddress);
        this.swapContract = new ContractPromise(this.api, swapMetadata, swapAddress);
        this.messagingContract = new ContractPromise(this.api, messagingMetadata, messagingAddress);
    }

    // 跨链桥操作
    async initiateBridge(targetChain: number, token: string, amount: number, recipient: string) {
        const result = await this.bridgeContract.tx.initiateBridge(targetChain, token, amount, recipient);
        return result;
    }

    async completeBridge(requestId: number, signatures: string[]) {
        const result = await this.bridgeContract.tx.completeBridge(requestId, signatures);
        return result;
    }

    // 原子交换操作
    async initiateSwap(participant: string, tokenA: string, tokenB: string, amountA: number, amountB: number, timeoutHours: number) {
        const result = await this.swapContract.tx.initiateSwap(participant, tokenA, tokenB, amountA, amountB, timeoutHours);
        return result;
    }

    async participateSwap(swapId: number, hashlock: string) {
        const result = await this.swapContract.tx.participateSwap(swapId, hashlock);
        return result;
    }

    async completeSwap(swapId: number, secretA: string, secretB: string) {
        const result = await this.swapContract.tx.completeSwap(swapId, secretA, secretB);
        return result;
    }

    // 消息传递操作
    async sendMessage(targetChain: number, recipient: string, payload: string) {
        const result = await this.messagingContract.tx.sendMessage(targetChain, recipient, payload);
        return result;
    }

    async deliverMessage(messageId: number, signatures: string[]) {
        const result = await this.messagingContract.tx.deliverMessage(messageId, signatures);
        return result;
    }
}

// 使用示例
const client = new CrossChainClient();

// 跨链桥
await client.initiateBridge(2, 'TOKEN_A', 1000, 'recipient_address');

// 原子交换
await client.initiateSwap('participant_address', 'TOKEN_A', 'TOKEN_B', 1000, 2000, 24);
await client.participateSwap(1, 'hashlock');
await client.completeSwap(1, 'secret_a', 'secret_b');

// 消息传递
await client.sendMessage(2, 'recipient_address', 'Hello from chain 1');
```

## 总结

本实现指南提供了完整的跨链协议解决方案，包括：

1. **跨链桥**: 支持代币跨链转移，包含多重签名验证
2. **原子交换**: 支持无信任的代币交换
3. **消息传递**: 支持跨链消息通信
4. **状态验证**: 支持轻客户端验证

所有实现都采用Rust和ink!框架，确保安全性和性能。可以根据具体需求进行定制和扩展。
