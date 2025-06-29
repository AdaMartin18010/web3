# 智能合约语言 (Smart Contract Languages)

## 概述

智能合约语言是Web3技术的核心组件，用于编写在区块链上执行的程序。不同的智能合约语言具有不同的设计理念、安全特性和应用场景。本目录涵盖主流智能合约语言的设计原理、语法特性、安全机制和实际应用。

## 目录结构

### 1.1 Solidity语言 (Solidity)

- [**语言基础**](01_Solidity/01_Language_Basics/) - 语法、数据类型、函数、修饰符
- [**合约结构**](01_Solidity/02_Contract_Structure/) - 合约定义、继承、接口、库
- [**安全机制**](01_Solidity/03_Security_Mechanisms/) - 访问控制、重入攻击防护、整数溢出
- [**Gas优化**](01_Solidity/04_Gas_Optimization/) - Gas消耗分析、优化技巧、成本控制
- [**高级特性**](01_Solidity/05_Advanced_Features/) - 内联汇编、Yul、自定义错误

### 1.2 Rust智能合约 (Rust Contracts)

- [**Ink!框架**](02_Rust_Contracts/01_Ink_Framework/) - Ink!语法、宏、存储、事件
- [**Substrate集成**](02_Rust_Contracts/02_Substrate_Integration/) - 链上逻辑、链下工作机
- [**安全特性**](02_Rust_Contracts/03_Security_Features/) - 内存安全、类型安全、并发安全
- [**性能优化**](02_Rust_Contracts/04_Performance_Optimization/) - 编译优化、运行时优化
- [**工具链**](02_Rust_Contracts/05_Toolchain/) - cargo-contract、cargo-dylint、测试框架

### 1.3 Move语言 (Move)

- [**语言设计**](03_Move/01_Language_Design/) - 资源模型、线性类型、模块系统
- [**资源安全**](03_Move/02_Resource_Safety/) - 资源不变量、所有权、借用检查
- [**模块系统**](03_Move/03_Module_System/) - 模块定义、依赖管理、可见性
- [**标准库**](03_Move/04_Standard_Library/) - 内置类型、标准函数、常用模式
- [**开发工具**](03_Move/05_Development_Tools/) - Move CLI、Move Analyzer、测试框架

### 1.4 其他语言 (Other Languages)

- [**Vyper**](04_Other_Languages/01_Vyper/) - Python风格、安全性优先、可读性
- [**Scilla**](04_Other_Languages/02_Scilla/) - 形式化验证、函数式编程、安全证明
- [**Michelson**](04_Other_Languages/03_Michelson/) - 栈式语言、形式化语义、Tezos
- [**Plutus**](04_Other_Languages/04_Plutus/) - Haskell、函数式编程、Cardano
- [**语言比较**](04_Other_Languages/05_Language_Comparison/) - 特性对比、适用场景、选择指南

### 1.5 语言设计原理 (Language Design Principles)

- [**安全设计**](05_Language_Design_Principles/01_Security_Design/) - 安全原则、威胁模型、防护机制
- [**可验证性**](05_Language_Design_Principles/02_Verifiability/) - 形式化验证、静态分析、动态检查
- [**可扩展性**](05_Language_Design_Principles/03_Scalability/) - 模块化设计、组合性、升级机制
- [**开发者体验**](05_Language_Design_Principles/04_Developer_Experience/) - 工具链、调试、测试
- [**生态系统**](05_Language_Design_Principles/05_Ecosystem/) - 标准库、框架、最佳实践

## 核心概念

### 智能合约语言特性

智能合约语言需要具备以下关键特性：

**安全性**：

- 防止重入攻击
- 整数溢出保护
- 访问控制机制
- 资源管理安全

**可验证性**：

- 形式化语义
- 静态类型检查
- 运行时验证
- 安全证明

**可扩展性**：

- 模块化设计
- 升级机制
- 组合性
- 互操作性

### 在Web3中的应用

#### 1. 去中心化应用

- **DeFi协议**：借贷、交易、流动性管理
- **NFT市场**：铸造、交易、版税分配
- **DAO治理**：投票、提案、执行
- **游戏应用**：资产管理、游戏逻辑、经济系统

#### 2. 企业应用

- **供应链管理**：追踪、验证、自动化
- **身份管理**：认证、授权、凭证
- **金融应用**：支付、结算、合规
- **数据管理**：存储、访问、共享

## 实际项目案例

### 案例1：基于Ink!的DeFi借贷协议

#### 项目背景

使用Rust和Ink!框架实现一个去中心化借贷协议，支持多种资产的借贷和流动性管理。

#### 技术实现

```rust
#![cfg_attr(not(feature = "std"), no_std)]

use ink_lang as ink;

#[ink::contract]
mod lending_protocol {
    use ink_storage::{
        collections::HashMap as StorageHashMap,
        lazy::Lazy,
    };
    use ink_prelude::string::String;
    use ink_prelude::vec::Vec;

    #[ink(storage)]
    pub struct LendingProtocol {
        /// 协议管理员
        owner: AccountId,
        /// 支持的资产列表
        supported_assets: Vec<AccountId>,
        /// 用户存款余额
        deposits: StorageHashMap<(AccountId, AccountId), Balance>,
        /// 用户借款余额
        borrows: StorageHashMap<(AccountId, AccountId), Balance>,
        /// 资产总存款
        total_deposits: StorageHashMap<AccountId, Balance>,
        /// 资产总借款
        total_borrows: StorageHashMap<AccountId, Balance>,
        /// 资产利率
        interest_rates: StorageHashMap<AccountId, u32>,
        /// 清算阈值
        liquidation_threshold: u32,
        /// 协议费用
        protocol_fee: u32,
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        /// 资产不支持
        AssetNotSupported,
        /// 余额不足
        InsufficientBalance,
        /// 清算阈值未达到
        LiquidationThresholdNotMet,
        /// 只有管理员可以调用
        OnlyOwner,
        /// 借款超过限制
        BorrowLimitExceeded,
    }

    pub type Result<T> = core::result::Result<T, Error>;

    impl LendingProtocol {
        #[ink(constructor)]
        pub fn new() -> Self {
            Self {
                owner: Self::env().caller(),
                supported_assets: Vec::new(),
                deposits: StorageHashMap::new(),
                borrows: StorageHashMap::new(),
                total_deposits: StorageHashMap::new(),
                total_borrows: StorageHashMap::new(),
                interest_rates: StorageHashMap::new(),
                liquidation_threshold: 80, // 80%
                protocol_fee: 5, // 0.5%
            }
        }

        /// 添加支持的资产
        #[ink(message)]
        pub fn add_supported_asset(&mut self, asset: AccountId, interest_rate: u32) -> Result<()> {
            self.ensure_owner()?;
            
            if !self.supported_assets.contains(&asset) {
                self.supported_assets.push(asset);
                self.interest_rates.insert(asset, interest_rate);
            }
            
            Ok(())
        }

        /// 存款
        #[ink(message)]
        pub fn deposit(&mut self, asset: AccountId, amount: Balance) -> Result<()> {
            self.ensure_asset_supported(asset)?;
            
            let caller = self.env().caller();
            let current_deposit = self.deposits.get(&(caller, asset)).unwrap_or(&0);
            let new_deposit = current_deposit + amount;
            
            self.deposits.insert((caller, asset), new_deposit);
            
            let current_total = self.total_deposits.get(&asset).unwrap_or(&0);
            self.total_deposits.insert(asset, current_total + amount);
            
            self.env().emit_event(DepositEvent {
                user: caller,
                asset,
                amount,
            });
            
            Ok(())
        }

        /// 借款
        #[ink(message)]
        pub fn borrow(&mut self, asset: AccountId, amount: Balance) -> Result<()> {
            self.ensure_asset_supported(asset)?;
            
            let caller = self.env().caller();
            
            // 检查借款限制
            if !self.can_borrow(caller, asset, amount)? {
                return Err(Error::BorrowLimitExceeded);
            }
            
            let current_borrow = self.borrows.get(&(caller, asset)).unwrap_or(&0);
            let new_borrow = current_borrow + amount;
            
            self.borrows.insert((caller, asset), new_borrow);
            
            let current_total = self.total_borrows.get(&asset).unwrap_or(&0);
            self.total_borrows.insert(asset, current_total + amount);
            
            self.env().emit_event(BorrowEvent {
                user: caller,
                asset,
                amount,
            });
            
            Ok(())
        }

        /// 还款
        #[ink(message)]
        pub fn repay(&mut self, asset: AccountId, amount: Balance) -> Result<()> {
            self.ensure_asset_supported(asset)?;
            
            let caller = self.env().caller();
            let current_borrow = self.borrows.get(&(caller, asset)).unwrap_or(&0);
            
            if amount > *current_borrow {
                return Err(Error::InsufficientBalance);
            }
            
            let new_borrow = current_borrow - amount;
            self.borrows.insert((caller, asset), new_borrow);
            
            let current_total = self.total_borrows.get(&asset).unwrap_or(&0);
            self.total_borrows.insert(asset, current_total - amount);
            
            self.env().emit_event(RepayEvent {
                user: caller,
                asset,
                amount,
            });
            
            Ok(())
        }

        /// 清算
        #[ink(message)]
        pub fn liquidate(&mut self, user: AccountId, asset: AccountId) -> Result<()> {
            self.ensure_asset_supported(asset)?;
            
            if !self.is_liquidatable(user, asset)? {
                return Err(Error::LiquidationThresholdNotMet);
            }
            
            let borrow_amount = self.borrows.get(&(user, asset)).unwrap_or(&0);
            let liquidation_amount = borrow_amount * 50 / 100; // 清算50%
            
            self.borrows.insert((user, asset), borrow_amount - liquidation_amount);
            
            let current_total = self.total_borrows.get(&asset).unwrap_or(&0);
            self.total_borrows.insert(asset, current_total - liquidation_amount);
            
            self.env().emit_event(LiquidateEvent {
                user,
                asset,
                amount: liquidation_amount,
                liquidator: self.env().caller(),
            });
            
            Ok(())
        }

        /// 获取用户存款余额
        #[ink(message)]
        pub fn get_deposit(&self, user: AccountId, asset: AccountId) -> Balance {
            *self.deposits.get(&(user, asset)).unwrap_or(&0)
        }

        /// 获取用户借款余额
        #[ink(message)]
        pub fn get_borrow(&self, user: AccountId, asset: AccountId) -> Balance {
            *self.borrows.get(&(user, asset)).unwrap_or(&0)
        }

        /// 获取资产总存款
        #[ink(message)]
        pub fn get_total_deposits(&self, asset: AccountId) -> Balance {
            *self.total_deposits.get(&asset).unwrap_or(&0)
        }

        /// 获取资产总借款
        #[ink(message)]
        pub fn get_total_borrows(&self, asset: AccountId) -> Balance {
            *self.total_borrows.get(&asset).unwrap_or(&0)
        }

        /// 检查是否可以借款
        fn can_borrow(&self, user: AccountId, asset: AccountId, amount: Balance) -> Result<bool> {
            let total_deposits = self.get_total_deposits(asset);
            let total_borrows = self.get_total_borrows(asset);
            
            // 简单的借款限制：借款不能超过存款的80%
            let available_for_borrow = total_deposits * 80 / 100;
            let current_borrow = self.get_borrow(user, asset);
            
            Ok(total_borrows + amount <= available_for_borrow)
        }

        /// 检查是否可以清算
        fn is_liquidatable(&self, user: AccountId, asset: AccountId) -> Result<bool> {
            let borrow_amount = self.get_borrow(user, asset);
            let deposit_amount = self.get_deposit(user, asset);
            
            if deposit_amount == 0 {
                return Ok(false);
            }
            
            let health_factor = (deposit_amount * 100) / borrow_amount;
            Ok(health_factor < self.liquidation_threshold)
        }

        /// 确保调用者是管理员
        fn ensure_owner(&self) -> Result<()> {
            if self.env().caller() != self.owner {
                return Err(Error::OnlyOwner);
            }
            Ok(())
        }

        /// 确保资产被支持
        fn ensure_asset_supported(&self, asset: AccountId) -> Result<()> {
            if !self.supported_assets.contains(&asset) {
                return Err(Error::AssetNotSupported);
            }
            Ok(())
        }
    }

    #[ink(event)]
    pub struct DepositEvent {
        #[ink(topic)]
        user: AccountId,
        #[ink(topic)]
        asset: AccountId,
        amount: Balance,
    }

    #[ink(event)]
    pub struct BorrowEvent {
        #[ink(topic)]
        user: AccountId,
        #[ink(topic)]
        asset: AccountId,
        amount: Balance,
    }

    #[ink(event)]
    pub struct RepayEvent {
        #[ink(topic)]
        user: AccountId,
        #[ink(topic)]
        asset: AccountId,
        amount: Balance,
    }

    #[ink(event)]
    pub struct LiquidateEvent {
        #[ink(topic)]
        user: AccountId,
        #[ink(topic)]
        asset: AccountId,
        amount: Balance,
        #[ink(topic)]
        liquidator: AccountId,
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[ink::test]
        fn test_deposit_and_borrow() {
            let mut contract = LendingProtocol::new();
            let asset = AccountId::from([1u8; 32]);
            
            // 添加支持的资产
            contract.add_supported_asset(asset, 500).unwrap();
            
            // 存款
            contract.deposit(asset, 1000).unwrap();
            assert_eq!(contract.get_deposit(AccountId::from([0u8; 32]), asset), 1000);
            assert_eq!(contract.get_total_deposits(asset), 1000);
            
            // 借款
            contract.borrow(asset, 500).unwrap();
            assert_eq!(contract.get_borrow(AccountId::from([0u8; 32]), asset), 500);
            assert_eq!(contract.get_total_borrows(asset), 500);
        }

        #[ink::test]
        fn test_repay() {
            let mut contract = LendingProtocol::new();
            let asset = AccountId::from([1u8; 32]);
            
            contract.add_supported_asset(asset, 500).unwrap();
            contract.deposit(asset, 1000).unwrap();
            contract.borrow(asset, 500).unwrap();
            
            // 还款
            contract.repay(asset, 200).unwrap();
            assert_eq!(contract.get_borrow(AccountId::from([0u8; 32]), asset), 300);
            assert_eq!(contract.get_total_borrows(asset), 300);
        }
    }
}
```

#### 项目成果

- 实现了完整的DeFi借贷协议
- 支持存款、借款、还款、清算功能
- 包含健康因子和清算机制
- 提供了完整的测试用例

### 案例2：基于Move的NFT市场

#### 项目背景1

使用Move语言实现一个安全的NFT市场，支持NFT的铸造、交易和版税分配。

#### 技术实现1

```move
module nft_marketplace::nft_marketplace {
    use std::signer;
    use std::vector;
    use aptos_framework::account;
    use aptos_framework::coin::{Self, Coin};
    use aptos_framework::timestamp;
    use std::option::{Self, Option};

    /// NFT结构
    struct NFT has key, store {
        id: u64,
        name: vector<u8>,
        description: vector<u8>,
        uri: vector<u8>,
        creator: address,
        owner: address,
        price: Option<u64>,
        royalty_percentage: u64,
        created_at: u64,
    }

    /// 市场结构
    struct NFTMarketplace has key {
        nft_counter: u64,
        nfts: vector<NFT>,
        listed_nfts: vector<u64>,
        sales: vector<Sale>,
    }

    /// 销售记录
    struct Sale has store {
        nft_id: u64,
        seller: address,
        buyer: address,
        price: u64,
        timestamp: u64,
    }

    /// 错误码
    const ENOT_AUTHORIZED: u64 = 1;
    const ENFT_NOT_FOUND: u64 = 2;
    const ENFT_NOT_LISTED: u64 = 3;
    const EINSUFFICIENT_BALANCE: u64 = 4;
    const EINVALID_PRICE: u64 = 5;

    /// 初始化市场
    public entry fun initialize_marketplace(creator: &signer) {
        let creator_addr = signer::address_of(creator);
        
        move_to(creator, NFTMarketplace {
            nft_counter: 0,
            nfts: vector::empty(),
            listed_nfts: vector::empty(),
            sales: vector::empty(),
        });
    }

    /// 铸造NFT
    public entry fun mint_nft(
        creator: &signer,
        name: vector<u8>,
        description: vector<u8>,
        uri: vector<u8>,
        royalty_percentage: u64,
    ) acquires NFTMarketplace {
        let creator_addr = signer::address_of(creator);
        let marketplace = borrow_global_mut<NFTMarketplace>(creator_addr);
        
        let nft_id = marketplace.nft_counter + 1;
        marketplace.nft_counter = nft_id;
        
        let nft = NFT {
            id: nft_id,
            name,
            description,
            uri,
            creator: creator_addr,
            owner: creator_addr,
            price: option::none(),
            royalty_percentage,
            created_at: timestamp::now_seconds(),
        };
        
        vector::push_back(&mut marketplace.nfts, nft);
    }

    /// 列出NFT
    public entry fun list_nft(
        owner: &signer,
        nft_id: u64,
        price: u64,
    ) acquires NFTMarketplace {
        let owner_addr = signer::address_of(owner);
        let marketplace = borrow_global_mut<NFTMarketplace>(owner_addr);
        
        let nft_index = find_nft_index(marketplace, nft_id);
        assert!(nft_index < vector::length(&marketplace.nfts), ENFT_NOT_FOUND);
        
        let nft = vector::borrow_mut(&mut marketplace.nfts, nft_index);
        assert!(nft.owner == owner_addr, ENOT_AUTHORIZED);
        assert!(price > 0, EINVALID_PRICE);
        
        nft.price = option::some(price);
        
        if (!vector::contains(&marketplace.listed_nfts, &nft_id)) {
            vector::push_back(&mut marketplace.listed_nfts, nft_id);
        };
    }

    /// 购买NFT
    public entry fun buy_nft(
        buyer: &signer,
        nft_id: u64,
        payment: Coin<AptosCoin>,
    ) acquires NFTMarketplace {
        let buyer_addr = signer::address_of(buyer);
        let marketplace = borrow_global_mut<NFTMarketplace>(buyer_addr);
        
        let nft_index = find_nft_index(marketplace, nft_id);
        assert!(nft_index < vector::length(&marketplace.nfts), ENFT_NOT_FOUND);
        
        let nft = vector::borrow_mut(&mut marketplace.nfts, nft_index);
        assert!(option::is_some(&nft.price), ENFT_NOT_LISTED);
        
        let price = *option::borrow(&nft.price);
        let payment_value = coin::value(&payment);
        assert!(payment_value >= price, EINSUFFICIENT_BALANCE);
        
        let seller = nft.owner;
        let creator = nft.creator;
        let royalty_percentage = nft.royalty_percentage;
        
        // 转移NFT所有权
        nft.owner = buyer_addr;
        nft.price = option::none();
        
        // 从已列出列表中移除
        let listed_index = find_listed_index(marketplace, nft_id);
        if (listed_index < vector::length(&marketplace.listed_nfts)) {
            vector::remove(&mut marketplace.listed_nfts, listed_index);
        };
        
        // 计算版税
        let royalty_amount = (price * royalty_percentage) / 100;
        let seller_amount = price - royalty_amount;
        
        // 分配资金
        if (seller != creator) {
            // 给卖家
            let seller_coin = coin::extract(&mut payment, seller_amount);
            coin::deposit(seller, seller_coin);
            
            // 给创作者
            let creator_coin = coin::extract(&mut payment, royalty_amount);
            coin::deposit(creator, creator_coin);
        } else {
            // 卖家就是创作者
            coin::deposit(seller, payment);
        };
        
        // 记录销售
        let sale = Sale {
            nft_id,
            seller,
            buyer: buyer_addr,
            price,
            timestamp: timestamp::now_seconds(),
        };
        vector::push_back(&mut marketplace.sales, sale);
    }

    /// 取消列出
    public entry fun unlist_nft(
        owner: &signer,
        nft_id: u64,
    ) acquires NFTMarketplace {
        let owner_addr = signer::address_of(owner);
        let marketplace = borrow_global_mut<NFTMarketplace>(owner_addr);
        
        let nft_index = find_nft_index(marketplace, nft_id);
        assert!(nft_index < vector::length(&marketplace.nfts), ENFT_NOT_FOUND);
        
        let nft = vector::borrow_mut(&mut marketplace.nfts, nft_index);
        assert!(nft.owner == owner_addr, ENOT_AUTHORIZED);
        
        nft.price = option::none();
        
        let listed_index = find_listed_index(marketplace, nft_id);
        if (listed_index < vector::length(&marketplace.listed_nfts)) {
            vector::remove(&mut marketplace.listed_nfts, listed_index);
        };
    }

    /// 获取NFT信息
    public fun get_nft(marketplace_addr: address, nft_id: u64): Option<NFT> {
        let marketplace = borrow_global<NFTMarketplace>(marketplace_addr);
        let nft_index = find_nft_index(marketplace, nft_id);
        
        if (nft_index < vector::length(&marketplace.nfts)) {
            let nft = vector::borrow(&marketplace.nfts, nft_index);
            option::some(*nft)
        } else {
            option::none()
        }
    }

    /// 获取已列出的NFT列表
    public fun get_listed_nfts(marketplace_addr: address): vector<u64> {
        let marketplace = borrow_global<NFTMarketplace>(marketplace_addr);
        *&marketplace.listed_nfts
    }

    /// 获取销售历史
    public fun get_sales(marketplace_addr: address): vector<Sale> {
        let marketplace = borrow_global<NFTMarketplace>(marketplace_addr);
        *&marketplace.sales
    }

    /// 查找NFT索引
    fun find_nft_index(marketplace: &NFTMarketplace, nft_id: u64): u64 {
        let i = 0;
        let len = vector::length(&marketplace.nfts);
        
        while (i < len) {
            let nft = vector::borrow(&marketplace.nfts, i);
            if (nft.id == nft_id) {
                return i
            };
            i = i + 1;
        };
        
        len
    }

    /// 查找已列出NFT索引
    fun find_listed_index(marketplace: &NFTMarketplace, nft_id: u64): u64 {
        let i = 0;
        let len = vector::length(&marketplace.listed_nfts);
        
        while (i < len) {
            let listed_id = *vector::borrow(&marketplace.listed_nfts, i);
            if (listed_id == nft_id) {
                return i
            };
            i = i + 1;
        };
        
        len
    }
}
```

#### 项目成果2

- 实现了安全的NFT市场合约
- 支持NFT铸造、列出、购买、取消列出
- 包含版税分配机制
- 提供了完整的销售记录

### 案例3：基于Solidity的DAO治理合约

#### 项目背景2

使用Solidity实现一个去中心化自治组织(DAO)的治理合约，支持提案创建、投票和执行。

#### 技术实现2

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import "@openzeppelin/contracts/security/ReentrancyGuard.sol";
import "@openzeppelin/contracts/utils/Counters.sol";

contract DAOGovernance is ReentrancyGuard {
    using Counters for Counters.Counter;

    // 提案状态
    enum ProposalState {
        Active,
        Canceled,
        Defeated,
        Succeeded,
        Queued,
        Expired,
        Executed
    }

    // 投票选项
    enum VoteType {
        Against,
        For,
        Abstain
    }

    // 提案结构
    struct Proposal {
        uint256 id;
        address proposer;
        address[] targets;
        uint256[] values;
        string[] signatures;
        bytes[] calldatas;
        uint256 startTime;
        uint256 endTime;
        uint256 forVotes;
        uint256 againstVotes;
        uint256 abstainVotes;
        bool canceled;
        bool executed;
        string description;
    }

    // 投票结构
    struct Receipt {
        bool hasVoted;
        VoteType support;
        uint256 votes;
    }

    // 状态变量
    IERC20 public immutable governanceToken;
    uint256 public proposalThreshold;
    uint256 public votingDelay;
    uint256 public votingPeriod;
    uint256 public quorumVotes;
    uint256 public timelockDelay;

    Counters.Counter private _proposalIds;
    mapping(uint256 => Proposal) public proposals;
    mapping(uint256 => mapping(address => Receipt)) public proposalReceipts;
    mapping(address => uint256) public proposalCount;

    // 事件
    event ProposalCreated(
        uint256 indexed proposalId,
        address indexed proposer,
        address[] targets,
        uint256[] values,
        string[] signatures,
        bytes[] calldatas,
        uint256 startTime,
        uint256 endTime,
        string description
    );

    event VoteCast(
        address indexed voter,
        uint256 indexed proposalId,
        VoteType support,
        uint256 votes
    );

    event ProposalCanceled(uint256 indexed proposalId);
    event ProposalExecuted(uint256 indexed proposalId);
    event ProposalQueued(uint256 indexed proposalId, uint256 eta);

    // 修饰符
    modifier onlyTokenHolder() {
        require(
            governanceToken.balanceOf(msg.sender) > 0,
            "DAOGovernance: caller is not a token holder"
        );
        _;
    }

    modifier onlyProposer(uint256 proposalId) {
        require(
            proposals[proposalId].proposer == msg.sender,
            "DAOGovernance: caller is not the proposer"
        );
        _;
    }

    modifier onlyActiveProposal(uint256 proposalId) {
        require(
            state(proposalId) == ProposalState.Active,
            "DAOGovernance: proposal is not active"
        );
        _;
    }

    constructor(
        address _governanceToken,
        uint256 _proposalThreshold,
        uint256 _votingDelay,
        uint256 _votingPeriod,
        uint256 _quorumVotes,
        uint256 _timelockDelay
    ) {
        governanceToken = IERC20(_governanceToken);
        proposalThreshold = _proposalThreshold;
        votingDelay = _votingDelay;
        votingPeriod = _votingPeriod;
        quorumVotes = _quorumVotes;
        timelockDelay = _timelockDelay;
    }

    // 创建提案
    function propose(
        address[] memory targets,
        uint256[] memory values,
        string[] memory signatures,
        bytes[] memory calldatas,
        string memory description
    ) external onlyTokenHolder returns (uint256) {
        require(
            governanceToken.balanceOf(msg.sender) >= proposalThreshold,
            "DAOGovernance: proposer votes below proposal threshold"
        );
        require(
            targets.length == values.length &&
            targets.length == signatures.length &&
            targets.length == calldatas.length,
            "DAOGovernance: proposal function information arity mismatch"
        );
        require(targets.length > 0, "DAOGovernance: empty proposal");

        uint256 proposalId = _proposalIds.current();
        _proposalIds.increment();

        uint256 startTime = block.timestamp + votingDelay;
        uint256 endTime = startTime + votingPeriod;

        proposals[proposalId] = Proposal({
            id: proposalId,
            proposer: msg.sender,
            targets: targets,
            values: values,
            signatures: signatures,
            calldatas: calldatas,
            startTime: startTime,
            endTime: endTime,
            forVotes: 0,
            againstVotes: 0,
            abstainVotes: 0,
            canceled: false,
            executed: false,
            description: description
        });

        proposalCount[msg.sender]++;

        emit ProposalCreated(
            proposalId,
            msg.sender,
            targets,
            values,
            signatures,
            calldatas,
            startTime,
            endTime,
            description
        );

        return proposalId;
    }

    // 投票
    function castVote(uint256 proposalId, VoteType support)
        external
        onlyTokenHolder
        onlyActiveProposal(proposalId)
        returns (uint256)
    {
        require(
            !proposalReceipts[proposalId][msg.sender].hasVoted,
            "DAOGovernance: voter already voted"
        );

        uint256 votes = governanceToken.balanceOf(msg.sender);
        require(votes > 0, "DAOGovernance: voter has no voting power");

        proposalReceipts[proposalId][msg.sender] = Receipt({
            hasVoted: true,
            support: support,
            votes: votes
        });

        if (support == VoteType.For) {
            proposals[proposalId].forVotes += votes;
        } else if (support == VoteType.Against) {
            proposals[proposalId].againstVotes += votes;
        } else if (support == VoteType.Abstain) {
            proposals[proposalId].abstainVotes += votes;
        }

        emit VoteCast(msg.sender, proposalId, support, votes);

        return votes;
    }

    // 取消提案
    function cancel(uint256 proposalId)
        external
        onlyProposer(proposalId)
        onlyActiveProposal(proposalId)
    {
        proposals[proposalId].canceled = true;
        emit ProposalCanceled(proposalId);
    }

    // 执行提案
    function execute(uint256 proposalId)
        external
        nonReentrant
        returns (uint256)
    {
        require(
            state(proposalId) == ProposalState.Succeeded,
            "DAOGovernance: proposal not successful"
        );

        Proposal storage proposal = proposals[proposalId];
        proposal.executed = true;

        for (uint256 i = 0; i < proposal.targets.length; i++) {
            _executeTransaction(
                proposal.targets[i],
                proposal.values[i],
                proposal.signatures[i],
                proposal.calldatas[i]
            );
        }

        emit ProposalExecuted(proposalId);

        return proposalId;
    }

    // 获取提案状态
    function state(uint256 proposalId) public view returns (ProposalState) {
        require(
            proposalId < _proposalIds.current(),
            "DAOGovernance: invalid proposal id"
        );

        Proposal storage proposal = proposals[proposalId];

        if (proposal.canceled) {
            return ProposalState.Canceled;
        }

        if (proposal.executed) {
            return ProposalState.Executed;
        }

        if (block.timestamp <= proposal.startTime) {
            return ProposalState.Active;
        }

        if (block.timestamp <= proposal.endTime) {
            return ProposalState.Active;
        }

        if (proposal.forVotes <= proposal.againstVotes || 
            proposal.forVotes < quorumVotes) {
            return ProposalState.Defeated;
        }

        return ProposalState.Succeeded;
    }

    // 获取投票收据
    function getReceipt(uint256 proposalId, address voter)
        external
        view
        returns (Receipt memory)
    {
        return proposalReceipts[proposalId][voter];
    }

    // 内部函数：执行交易
    function _executeTransaction(
        address target,
        uint256 value,
        string memory signature,
        bytes memory data
    ) internal returns (bytes memory) {
        bytes memory callData;

        if (bytes(signature).length == 0) {
            callData = data;
        } else {
            callData = abi.encodePacked(
                bytes4(keccak256(bytes(signature))),
                data
            );
        }

        (bool success, bytes memory returnData) = target.call{value: value}(callData);
        require(success, "DAOGovernance: transaction execution reverted");

        return returnData;
    }

    // 获取提案信息
    function getProposal(uint256 proposalId)
        external
        view
        returns (
            uint256 id,
            address proposer,
            address[] memory targets,
            uint256[] memory values,
            string[] memory signatures,
            bytes[] memory calldatas,
            uint256 startTime,
            uint256 endTime,
            uint256 forVotes,
            uint256 againstVotes,
            uint256 abstainVotes,
            bool canceled,
            bool executed,
            string memory description
        )
    {
        Proposal storage proposal = proposals[proposalId];
        return (
            proposal.id,
            proposal.proposer,
            proposal.targets,
            proposal.values,
            proposal.signatures,
            proposal.calldatas,
            proposal.startTime,
            proposal.endTime,
            proposal.forVotes,
            proposal.againstVotes,
            proposal.abstainVotes,
            proposal.canceled,
            proposal.executed,
            proposal.description
        );
    }
}
```

#### 项目成果3

- 实现了完整的DAO治理合约
- 支持提案创建、投票、执行
- 包含投票权重和法定人数机制
- 提供了安全的交易执行功能

## 学习资源

### 推荐教材

1. **Solidity编程**：《Mastering Ethereum》- Andreas Antonopoulos
2. **Rust智能合约**：《Programming Rust》- Jim Blandy
3. **Move语言**：《Move Book》- Diem Association
4. **智能合约安全**：《Smart Contract Security》- ConsenSys

### 在线资源

- [Solidity文档](https://docs.soliditylang.org/)
- [Ink!文档](https://use.ink/)
- [Move文档](https://move-book.com/)
- [智能合约安全](https://consensys.net/diligence/)

## 贡献指南

欢迎对智能合约语言内容进行贡献。请确保：

1. 所有语言特性都有详细的说明
2. 包含在Web3中的具体应用场景
3. 提供完整的代码实现示例
4. 说明安全特性和最佳实践
5. 关注最新的语言发展动态
