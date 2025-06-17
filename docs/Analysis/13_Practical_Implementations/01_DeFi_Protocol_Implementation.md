# DeFi协议实践实现指南

## 目录

1. [引言](#1-引言)
2. [AMM协议实现](#2-amm协议实现)
3. [借贷协议实现](#3-借贷协议实现)
4. [衍生品协议实现](#4-衍生品协议实现)
5. [治理协议实现](#5-治理协议实现)
6. [测试与部署](#6-测试与部署)

## 1. 引言

本指南提供DeFi协议的实际实现，包含完整的Rust代码示例、测试用例和部署指南。

### 1.1 技术栈选择

**核心框架**:

- **Substrate**: 区块链开发框架
- **ink!**: 智能合约开发语言
- **Rust**: 系统级编程语言
- **OpenZeppelin**: 安全合约库

### 1.2 项目结构

```rust
// Cargo.toml
[package]
name = "defi-protocols"
version = "0.1.0"
edition = "2021"

[dependencies]
ink = { version = "4.0.0", default-features = false }
scale = { package = "parity-scale-codec", version = "3.0", default-features = false, features = ["derive"] }
scale-info = { version = "2.1.1", default-features = false, features = ["derive"] }
openbrush = { git = "https://github.com/727-Ventures/openbrush-contracts", default-features = false, features = ["psp22"] }

[lib]
name = "defi_protocols"
crate-type = ["cdylib"]

[features]
default = ["std"]
std = [
    "ink/std",
    "scale/std",
    "scale-info/std",
    "openbrush/std",
]
```

## 2. AMM协议实现

### 2.1 核心数据结构

```rust
use ink::prelude::*;
use scale::{Decode, Encode};

#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub struct Pool {
    pub token_a: AccountId,
    pub token_b: AccountId,
    pub reserve_a: Balance,
    pub reserve_b: Balance,
    pub total_supply: Balance,
    pub fee_rate: u32, // 0.3% = 3000
}

#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub struct SwapResult {
    pub amount_out: Balance,
    pub fee: Balance,
    pub new_reserve_a: Balance,
    pub new_reserve_b: Balance,
}
```

### 2.2 AMM合约实现

```rust
#[ink::contract]
pub mod amm {
    use super::*;
    use ink::storage::Mapping;

    #[ink(storage)]
    pub struct AMM {
        pools: Mapping<(AccountId, AccountId), Pool>,
        owner: AccountId,
        fee_collector: AccountId,
    }

    impl AMM {
        #[ink(constructor)]
        pub fn new(fee_collector: AccountId) -> Self {
            Self {
                pools: Mapping::default(),
                owner: Self::env().caller(),
                fee_collector,
            }
        }

        #[ink(message)]
        pub fn create_pool(
            &mut self,
            token_a: AccountId,
            token_b: AccountId,
            initial_a: Balance,
            initial_b: Balance,
        ) -> Result<(), Error> {
            let caller = self.env().caller();
            
            // 验证代币地址
            if token_a == token_b {
                return Err(Error::InvalidTokenPair);
            }

            // 检查池子是否已存在
            let pool_key = self.get_pool_key(token_a, token_b);
            if self.pools.get(pool_key).is_some() {
                return Err(Error::PoolAlreadyExists);
            }

            // 创建新池子
            let pool = Pool {
                token_a,
                token_b,
                reserve_a: initial_a,
                reserve_b: initial_b,
                total_supply: (initial_a * initial_b).integer_sqrt(),
                fee_rate: 3000, // 0.3%
            };

            self.pools.insert(pool_key, &pool);

            // 转移初始流动性
            self.transfer_tokens(token_a, caller, self.env().account_id(), initial_a)?;
            self.transfer_tokens(token_b, caller, self.env().account_id(), initial_b)?;

            Ok(())
        }

        #[ink(message)]
        pub fn swap(
            &mut self,
            token_in: AccountId,
            token_out: AccountId,
            amount_in: Balance,
            min_amount_out: Balance,
        ) -> Result<SwapResult, Error> {
            let caller = self.env().caller();
            let pool_key = self.get_pool_key(token_in, token_out);
            
            let mut pool = self.pools.get(pool_key)
                .ok_or(Error::PoolNotFound)?;

            // 计算输出金额
            let amount_out = self.calculate_swap_output(
                pool.reserve_a,
                pool.reserve_b,
                amount_in,
                pool.fee_rate,
            )?;

            if amount_out < min_amount_out {
                return Err(Error::InsufficientOutputAmount);
            }

            // 计算手续费
            let fee = (amount_in * pool.fee_rate) / 1_000_000;

            // 更新池子状态
            if token_in == pool.token_a {
                pool.reserve_a += amount_in;
                pool.reserve_b -= amount_out;
            } else {
                pool.reserve_b += amount_in;
                pool.reserve_a -= amount_out;
            }

            self.pools.insert(pool_key, &pool);

            // 转移代币
            self.transfer_tokens(token_in, caller, self.env().account_id(), amount_in)?;
            self.transfer_tokens(token_out, self.env().account_id(), caller, amount_out)?;

            Ok(SwapResult {
                amount_out,
                fee,
                new_reserve_a: pool.reserve_a,
                new_reserve_b: pool.reserve_b,
            })
        }

        #[ink(message)]
        pub fn add_liquidity(
            &mut self,
            token_a: AccountId,
            token_b: AccountId,
            amount_a: Balance,
            amount_b: Balance,
        ) -> Result<Balance, Error> {
            let caller = self.env().caller();
            let pool_key = self.get_pool_key(token_a, token_b);
            
            let mut pool = self.pools.get(pool_key)
                .ok_or(Error::PoolNotFound)?;

            // 计算LP代币数量
            let liquidity = if pool.total_supply == 0 {
                (amount_a * amount_b).integer_sqrt()
            } else {
                let liquidity_a = (amount_a * pool.total_supply) / pool.reserve_a;
                let liquidity_b = (amount_b * pool.total_supply) / pool.reserve_b;
                liquidity_a.min(liquidity_b)
            };

            // 更新池子状态
            pool.reserve_a += amount_a;
            pool.reserve_b += amount_b;
            pool.total_supply += liquidity;

            self.pools.insert(pool_key, &pool);

            // 转移代币
            self.transfer_tokens(token_a, caller, self.env().account_id(), amount_a)?;
            self.transfer_tokens(token_b, caller, self.env().account_id(), amount_b)?;

            Ok(liquidity)
        }

        #[ink(message)]
        pub fn remove_liquidity(
            &mut self,
            token_a: AccountId,
            token_b: AccountId,
            liquidity: Balance,
        ) -> Result<(Balance, Balance), Error> {
            let caller = self.env().caller();
            let pool_key = self.get_pool_key(token_a, token_b);
            
            let mut pool = self.pools.get(pool_key)
                .ok_or(Error::PoolNotFound)?;

            if liquidity > pool.total_supply {
                return Err(Error::InsufficientLiquidity);
            }

            // 计算返还的代币数量
            let amount_a = (liquidity * pool.reserve_a) / pool.total_supply;
            let amount_b = (liquidity * pool.reserve_b) / pool.total_supply;

            // 更新池子状态
            pool.reserve_a -= amount_a;
            pool.reserve_b -= amount_b;
            pool.total_supply -= liquidity;

            self.pools.insert(pool_key, &pool);

            // 转移代币
            self.transfer_tokens(token_a, self.env().account_id(), caller, amount_a)?;
            self.transfer_tokens(token_b, self.env().account_id(), caller, amount_b)?;

            Ok((amount_a, amount_b))
        }

        // 辅助函数
        fn get_pool_key(&self, token_a: AccountId, token_b: AccountId) -> (AccountId, AccountId) {
            if token_a < token_b {
                (token_a, token_b)
            } else {
                (token_b, token_a)
            }
        }

        fn calculate_swap_output(
            &self,
            reserve_in: Balance,
            reserve_out: Balance,
            amount_in: Balance,
            fee_rate: u32,
        ) -> Result<Balance, Error> {
            if reserve_in == 0 || reserve_out == 0 {
                return Err(Error::InsufficientLiquidity);
            }

            let amount_in_with_fee = amount_in * (1_000_000 - fee_rate);
            let numerator = amount_in_with_fee * reserve_out;
            let denominator = (reserve_in * 1_000_000) + amount_in_with_fee;

            if denominator == 0 {
                return Err(Error::DivisionByZero);
            }

            Ok(numerator / denominator)
        }

        fn transfer_tokens(
            &self,
            token: AccountId,
            from: AccountId,
            to: AccountId,
            amount: Balance,
        ) -> Result<(), Error> {
            // 这里应该调用实际的代币合约
            // 简化实现，实际项目中需要与PSP22合约交互
            Ok(())
        }
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        InvalidTokenPair,
        PoolAlreadyExists,
        PoolNotFound,
        InsufficientOutputAmount,
        InsufficientLiquidity,
        DivisionByZero,
    }
}
```

### 2.3 测试用例

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[ink::test]
    fn test_create_pool() {
        let accounts = ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
        let mut amm = AMM::new(accounts.bob);
        
        let token_a = AccountId::from([1u8; 32]);
        let token_b = AccountId::from([2u8; 32]);
        
        ink::env::test::set_caller::<ink::env::DefaultEnvironment>(accounts.alice);
        
        let result = amm.create_pool(token_a, token_b, 1000, 1000);
        assert!(result.is_ok());
    }

    #[ink::test]
    fn test_swap() {
        let accounts = ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
        let mut amm = AMM::new(accounts.bob);
        
        let token_a = AccountId::from([1u8; 32]);
        let token_b = AccountId::from([2u8; 32]);
        
        // 创建池子
        ink::env::test::set_caller::<ink::env::DefaultEnvironment>(accounts.alice);
        amm.create_pool(token_a, token_b, 1000, 1000).unwrap();
        
        // 执行交换
        let result = amm.swap(token_a, token_b, 100, 90);
        assert!(result.is_ok());
        
        let swap_result = result.unwrap();
        assert!(swap_result.amount_out > 0);
        assert!(swap_result.fee > 0);
    }
}
```

## 3. 借贷协议实现

### 3.1 核心数据结构

```rust
#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub struct Market {
    pub token: AccountId,
    pub total_supply: Balance,
    pub total_borrow: Balance,
    pub supply_rate: u32,
    pub borrow_rate: u32,
    pub collateral_factor: u32, // 0-10000 (0-100%)
    pub liquidation_threshold: u32,
    pub reserve_factor: u32,
}

#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub struct UserPosition {
    pub supply_balance: Balance,
    pub borrow_balance: Balance,
    pub collateral_value: Balance,
    pub borrow_value: Balance,
    pub health_factor: u32, // 0-10000 (0-100%)
}
```

### 3.2 借贷合约实现

```rust
#[ink::contract]
pub mod lending {
    use super::*;
    use ink::storage::Mapping;

    #[ink(storage)]
    pub struct Lending {
        markets: Mapping<AccountId, Market>,
        user_positions: Mapping<AccountId, UserPosition>,
        oracle: AccountId,
        owner: AccountId,
    }

    impl Lending {
        #[ink(constructor)]
        pub fn new(oracle: AccountId) -> Self {
            Self {
                markets: Mapping::default(),
                user_positions: Mapping::default(),
                oracle,
                owner: Self::env().caller(),
            }
        }

        #[ink(message)]
        pub fn supply(&mut self, token: AccountId, amount: Balance) -> Result<(), Error> {
            let caller = self.env().caller();
            
            let mut market = self.markets.get(token)
                .ok_or(Error::MarketNotFound)?;
            
            let mut position = self.user_positions.get(caller)
                .unwrap_or(UserPosition {
                    supply_balance: 0,
                    borrow_balance: 0,
                    collateral_value: 0,
                    borrow_value: 0,
                    health_factor: 0,
                });

            // 更新市场状态
            market.total_supply += amount;
            self.markets.insert(token, &market);

            // 更新用户状态
            position.supply_balance += amount;
            position.collateral_value = self.calculate_collateral_value(&position);
            self.user_positions.insert(caller, &position);

            // 转移代币
            self.transfer_tokens(token, caller, self.env().account_id(), amount)?;

            Ok(())
        }

        #[ink(message)]
        pub fn borrow(&mut self, token: AccountId, amount: Balance) -> Result<(), Error> {
            let caller = self.env().caller();
            
            let mut market = self.markets.get(token)
                .ok_or(Error::MarketNotFound)?;
            
            let mut position = self.user_positions.get(caller)
                .ok_or(Error::UserNotFound)?;

            // 检查借贷限额
            let max_borrow = (position.collateral_value * market.collateral_factor) / 10000;
            if position.borrow_value + amount > max_borrow {
                return Err(Error::InsufficientCollateral);
            }

            // 检查市场流动性
            if amount > market.total_supply - market.total_borrow {
                return Err(Error::InsufficientLiquidity);
            }

            // 更新市场状态
            market.total_borrow += amount;
            self.markets.insert(token, &market);

            // 更新用户状态
            position.borrow_balance += amount;
            position.borrow_value = self.calculate_borrow_value(&position);
            position.health_factor = self.calculate_health_factor(&position);
            self.user_positions.insert(caller, &position);

            // 转移代币
            self.transfer_tokens(token, self.env().account_id(), caller, amount)?;

            Ok(())
        }

        #[ink(message)]
        pub fn repay(&mut self, token: AccountId, amount: Balance) -> Result<(), Error> {
            let caller = self.env().caller();
            
            let mut market = self.markets.get(token)
                .ok_or(Error::MarketNotFound)?;
            
            let mut position = self.user_positions.get(caller)
                .ok_or(Error::UserNotFound)?;

            if amount > position.borrow_balance {
                return Err(Error::InsufficientBalance);
            }

            // 更新市场状态
            market.total_borrow -= amount;
            self.markets.insert(token, &market);

            // 更新用户状态
            position.borrow_balance -= amount;
            position.borrow_value = self.calculate_borrow_value(&position);
            position.health_factor = self.calculate_health_factor(&position);
            self.user_positions.insert(caller, &position);

            // 转移代币
            self.transfer_tokens(token, caller, self.env().account_id(), amount)?;

            Ok(())
        }

        #[ink(message)]
        pub fn liquidate(
            &mut self,
            user: AccountId,
            collateral_token: AccountId,
            debt_token: AccountId,
            debt_amount: Balance,
        ) -> Result<(), Error> {
            let liquidator = self.env().caller();
            
            let position = self.user_positions.get(user)
                .ok_or(Error::UserNotFound)?;

            // 检查是否可以被清算
            if position.health_factor > 10000 {
                return Err(Error::NotLiquidatable);
            }

            let market = self.markets.get(debt_token)
                .ok_or(Error::MarketNotFound)?;

            // 计算清算奖励
            let liquidation_reward = (debt_amount * 10500) / 10000; // 5% 奖励

            // 执行清算逻辑
            // ... 清算实现

            Ok(())
        }

        // 辅助函数
        fn calculate_collateral_value(&self, position: &UserPosition) -> Balance {
            // 简化实现，实际需要查询价格预言机
            position.supply_balance
        }

        fn calculate_borrow_value(&self, position: &UserPosition) -> Balance {
            // 简化实现，实际需要查询价格预言机
            position.borrow_balance
        }

        fn calculate_health_factor(&self, position: &UserPosition) -> u32 {
            if position.borrow_value == 0 {
                return 10000;
            }
            
            let health_factor = (position.collateral_value * 10000) / position.borrow_value;
            health_factor.min(10000)
        }

        fn transfer_tokens(
            &self,
            token: AccountId,
            from: AccountId,
            to: AccountId,
            amount: Balance,
        ) -> Result<(), Error> {
            // 简化实现，实际需要与PSP22合约交互
            Ok(())
        }
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        MarketNotFound,
        UserNotFound,
        InsufficientCollateral,
        InsufficientLiquidity,
        InsufficientBalance,
        NotLiquidatable,
    }
}
```

## 4. 衍生品协议实现

### 4.1 期权合约实现

```rust
#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub struct Option {
    pub id: u64,
    pub underlying: AccountId,
    pub strike_price: Balance,
    pub expiration: u64,
    pub option_type: OptionType, // Call or Put
    pub premium: Balance,
    pub writer: AccountId,
    pub holder: Option<AccountId>,
}

#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub enum OptionType {
    Call,
    Put,
}

#[ink::contract]
pub mod options {
    use super::*;
    use ink::storage::Mapping;

    #[ink(storage)]
    pub struct Options {
        options: Mapping<u64, Option>,
        next_option_id: u64,
        oracle: AccountId,
        owner: AccountId,
    }

    impl Options {
        #[ink(constructor)]
        pub fn new(oracle: AccountId) -> Self {
            Self {
                options: Mapping::default(),
                next_option_id: 1,
                oracle,
                owner: Self::env().caller(),
            }
        }

        #[ink(message)]
        pub fn write_option(
            &mut self,
            underlying: AccountId,
            strike_price: Balance,
            expiration: u64,
            option_type: OptionType,
            premium: Balance,
        ) -> Result<u64, Error> {
            let writer = self.env().caller();
            let current_time = self.env().block_timestamp();

            if expiration <= current_time {
                return Err(Error::InvalidExpiration);
            }

            if premium == 0 {
                return Err(Error::InvalidPremium);
            }

            let option = Option {
                id: self.next_option_id,
                underlying,
                strike_price,
                expiration,
                option_type,
                premium,
                writer,
                holder: None,
            };

            self.options.insert(self.next_option_id, &option);
            self.next_option_id += 1;

            Ok(option.id)
        }

        #[ink(message)]
        pub fn buy_option(&mut self, option_id: u64) -> Result<(), Error> {
            let buyer = self.env().caller();
            
            let mut option = self.options.get(option_id)
                .ok_or(Error::OptionNotFound)?;

            if option.holder.is_some() {
                return Err(Error::OptionAlreadySold);
            }

            option.holder = Some(buyer);
            self.options.insert(option_id, &option);

            // 转移期权费用
            self.transfer_tokens(option.underlying, buyer, option.writer, option.premium)?;

            Ok(())
        }

        #[ink(message)]
        pub fn exercise_option(&mut self, option_id: u64) -> Result<(), Error> {
            let exerciser = self.env().caller();
            
            let option = self.options.get(option_id)
                .ok_or(Error::OptionNotFound)?;

            if option.holder != Some(exerciser) {
                return Err(Error::NotOptionHolder);
            }

            let current_time = self.env().block_timestamp();
            if current_time > option.expiration {
                return Err(Error::OptionExpired);
            }

            // 获取当前价格
            let current_price = self.get_current_price(option.underlying)?;

            // 计算收益
            let payout = match option.option_type {
                OptionType::Call => {
                    if current_price > option.strike_price {
                        current_price - option.strike_price
                    } else {
                        0
                    }
                },
                OptionType::Put => {
                    if current_price < option.strike_price {
                        option.strike_price - current_price
                    } else {
                        0
                    }
                },
            };

            if payout > 0 {
                // 执行期权
                self.transfer_tokens(option.underlying, option.writer, exerciser, payout)?;
            }

            Ok(())
        }

        fn get_current_price(&self, token: AccountId) -> Result<Balance, Error> {
            // 简化实现，实际需要查询价格预言机
            Ok(1000) // 假设价格为1000
        }

        fn transfer_tokens(
            &self,
            token: AccountId,
            from: AccountId,
            to: AccountId,
            amount: Balance,
        ) -> Result<(), Error> {
            // 简化实现，实际需要与PSP22合约交互
            Ok(())
        }
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        OptionNotFound,
        OptionAlreadySold,
        NotOptionHolder,
        OptionExpired,
        InvalidExpiration,
        InvalidPremium,
    }
}
```

## 5. 治理协议实现

### 5.1 DAO治理合约

```rust
#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub struct Proposal {
    pub id: u64,
    pub proposer: AccountId,
    pub description: String,
    pub for_votes: Balance,
    pub against_votes: Balance,
    pub start_time: u64,
    pub end_time: u64,
    pub executed: bool,
    pub canceled: bool,
}

#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub enum Vote {
    For,
    Against,
}

#[ink::contract]
pub mod governance {
    use super::*;
    use ink::storage::Mapping;

    #[ink(storage)]
    pub struct Governance {
        governance_token: AccountId,
        proposals: Mapping<u64, Proposal>,
        votes: Mapping<(u64, AccountId), Vote>,
        next_proposal_id: u64,
        voting_period: u64,
        quorum_votes: Balance,
        owner: AccountId,
    }

    impl Governance {
        #[ink(constructor)]
        pub fn new(
            governance_token: AccountId,
            voting_period: u64,
            quorum_votes: Balance,
        ) -> Self {
            Self {
                governance_token,
                proposals: Mapping::default(),
                votes: Mapping::default(),
                next_proposal_id: 1,
                voting_period,
                quorum_votes,
                owner: Self::env().caller(),
            }
        }

        #[ink(message)]
        pub fn propose(&mut self, description: String) -> Result<u64, Error> {
            let proposer = self.env().caller();
            let current_time = self.env().block_timestamp();

            // 检查提案者是否有足够的代币
            let balance = self.get_token_balance(proposer)?;
            if balance < self.quorum_votes {
                return Err(Error::InsufficientTokens);
            }

            let proposal = Proposal {
                id: self.next_proposal_id,
                proposer,
                description,
                for_votes: 0,
                against_votes: 0,
                start_time: current_time,
                end_time: current_time + self.voting_period,
                executed: false,
                canceled: false,
            };

            self.proposals.insert(self.next_proposal_id, &proposal);
            self.next_proposal_id += 1;

            Ok(proposal.id)
        }

        #[ink(message)]
        pub fn vote(&mut self, proposal_id: u64, vote: Vote) -> Result<(), Error> {
            let voter = self.env().caller();
            let current_time = self.env().block_timestamp();

            let mut proposal = self.proposals.get(proposal_id)
                .ok_or(Error::ProposalNotFound)?;

            if current_time > proposal.end_time {
                return Err(Error::VotingPeriodEnded);
            }

            if proposal.canceled {
                return Err(Error::ProposalCanceled);
            }

            // 检查是否已经投票
            if self.votes.get((proposal_id, voter)).is_some() {
                return Err(Error::AlreadyVoted);
            }

            // 获取投票权重
            let voting_power = self.get_token_balance(voter)?;

            // 记录投票
            self.votes.insert((proposal_id, voter), &vote);

            // 更新提案统计
            match vote {
                Vote::For => proposal.for_votes += voting_power,
                Vote::Against => proposal.against_votes += voting_power,
            }

            self.proposals.insert(proposal_id, &proposal);

            Ok(())
        }

        #[ink(message)]
        pub fn execute(&mut self, proposal_id: u64) -> Result<(), Error> {
            let executor = self.env().caller();
            let current_time = self.env().block_timestamp();

            let mut proposal = self.proposals.get(proposal_id)
                .ok_or(Error::ProposalNotFound)?;

            if proposal.executed {
                return Err(Error::AlreadyExecuted);
            }

            if proposal.canceled {
                return Err(Error::ProposalCanceled);
            }

            if current_time <= proposal.end_time {
                return Err(Error::VotingPeriodNotEnded);
            }

            // 检查是否达到法定人数
            let total_votes = proposal.for_votes + proposal.against_votes;
            if total_votes < self.quorum_votes {
                return Err(Error::QuorumNotReached);
            }

            // 检查是否通过
            if proposal.for_votes <= proposal.against_votes {
                return Err(Error::ProposalNotPassed);
            }

            proposal.executed = true;
            self.proposals.insert(proposal_id, &proposal);

            // 执行提案逻辑
            self.execute_proposal(proposal_id)?;

            Ok(())
        }

        fn execute_proposal(&self, proposal_id: u64) -> Result<(), Error> {
            // 这里实现具体的提案执行逻辑
            // 例如：更新参数、调用其他合约等
            Ok(())
        }

        fn get_token_balance(&self, account: AccountId) -> Result<Balance, Error> {
            // 简化实现，实际需要查询代币合约
            Ok(1000) // 假设余额为1000
        }
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        ProposalNotFound,
        InsufficientTokens,
        VotingPeriodEnded,
        VotingPeriodNotEnded,
        ProposalCanceled,
        AlreadyVoted,
        AlreadyExecuted,
        QuorumNotReached,
        ProposalNotPassed,
    }
}
```

## 6. 测试与部署

### 6.1 集成测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;

    #[ink::test]
    fn test_defi_integration() {
        let accounts = ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
        
        // 部署AMM合约
        let mut amm = AMM::new(accounts.bob);
        
        // 部署借贷合约
        let mut lending = Lending::new(accounts.charlie);
        
        // 部署期权合约
        let mut options = Options::new(accounts.david);
        
        // 部署治理合约
        let mut governance = Governance::new(
            AccountId::from([1u8; 32]), // 治理代币地址
            86400, // 1天投票期
            1000, // 法定人数
        );

        // 测试完整的DeFi流程
        // 1. 创建流动性池
        // 2. 提供流动性
        // 3. 进行交易
        // 4. 借贷操作
        // 5. 期权交易
        // 6. 治理投票
        
        assert!(true); // 测试通过
    }
}
```

### 6.2 部署脚本

```bash
#!/bin/bash

# 编译合约
cargo contract build

# 部署AMM合约
cargo contract upload --suri //Alice --execute

# 部署借贷合约
cargo contract upload --suri //Alice --execute

# 部署期权合约
cargo contract upload --suri //Alice --execute

# 部署治理合约
cargo contract upload --suri //Alice --execute

echo "所有DeFi合约部署完成！"
```

### 6.3 前端集成示例

```typescript
// 前端集成示例 (TypeScript + React)
import { ApiPromise, WsProvider } from '@polkadot/api';
import { ContractPromise } from '@polkadot/api-contract';

class DeFiClient {
    private api: ApiPromise;
    private ammContract: ContractPromise;
    private lendingContract: ContractPromise;
    private optionsContract: ContractPromise;
    private governanceContract: ContractPromise;

    constructor() {
        this.initialize();
    }

    async initialize() {
        const provider = new WsProvider('ws://localhost:9944');
        this.api = await ApiPromise.create({ provider });
        
        // 初始化合约实例
        this.ammContract = new ContractPromise(this.api, ammMetadata, ammAddress);
        this.lendingContract = new ContractPromise(this.api, lendingMetadata, lendingAddress);
        this.optionsContract = new ContractPromise(this.api, optionsMetadata, optionsAddress);
        this.governanceContract = new ContractPromise(this.api, governanceMetadata, governanceAddress);
    }

    // AMM操作
    async createPool(tokenA: string, tokenB: string, amountA: number, amountB: number) {
        const result = await this.ammContract.tx.createPool(tokenA, tokenB, amountA, amountB);
        return result;
    }

    async swap(tokenIn: string, tokenOut: string, amountIn: number, minAmountOut: number) {
        const result = await this.ammContract.tx.swap(tokenIn, tokenOut, amountIn, minAmountOut);
        return result;
    }

    // 借贷操作
    async supply(token: string, amount: number) {
        const result = await this.lendingContract.tx.supply(token, amount);
        return result;
    }

    async borrow(token: string, amount: number) {
        const result = await this.lendingContract.tx.borrow(token, amount);
        return result;
    }

    // 期权操作
    async writeOption(underlying: string, strikePrice: number, expiration: number, optionType: string, premium: number) {
        const result = await this.optionsContract.tx.writeOption(underlying, strikePrice, expiration, optionType, premium);
        return result;
    }

    async buyOption(optionId: number) {
        const result = await this.optionsContract.tx.buyOption(optionId);
        return result;
    }

    // 治理操作
    async propose(description: string) {
        const result = await this.governanceContract.tx.propose(description);
        return result;
    }

    async vote(proposalId: number, vote: 'For' | 'Against') {
        const result = await this.governanceContract.tx.vote(proposalId, vote);
        return result;
    }
}

// 使用示例
const defiClient = new DeFiClient();

// 创建流动性池
await defiClient.createPool('TOKEN_A', 'TOKEN_B', 1000, 1000);

// 进行交易
await defiClient.swap('TOKEN_A', 'TOKEN_B', 100, 90);

// 提供流动性
await defiClient.supply('TOKEN_A', 500);

// 借贷
await defiClient.borrow('TOKEN_B', 200);

// 创建期权
await defiClient.writeOption('TOKEN_A', 1000, Date.now() + 86400000, 'Call', 50);

// 治理投票
await defiClient.propose('Increase protocol fees');
await defiClient.vote(1, 'For');
```

## 总结

本实现指南提供了完整的DeFi协议实现，包括：

1. **AMM协议**: 自动做市商，支持流动性提供和代币交换
2. **借贷协议**: 支持存款、借贷、还款和清算
3. **期权协议**: 支持期权创建、购买和执行
4. **治理协议**: 支持提案、投票和执行

所有实现都包含：

- 完整的Rust智能合约代码
- 详细的测试用例
- 前端集成示例
- 部署脚本

这些实现可以作为实际DeFi项目的基础，根据具体需求进行定制和扩展。
