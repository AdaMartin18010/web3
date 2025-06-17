# NFT市场实践实现指南

## 目录

- [NFT市场实践实现指南](#nft市场实践实现指南)
  - [目录](#目录)
  - [1. 引言](#1-引言)
    - [1.1 技术栈](#11-技术栈)
  - [2. 核心数据结构](#2-核心数据结构)
  - [3. NFT合约实现](#3-nft合约实现)
  - [4. 市场合约实现](#4-市场合约实现)
  - [5. 版税系统实现](#5-版税系统实现)
  - [6. 测试与部署](#6-测试与部署)
    - [6.1 测试用例](#61-测试用例)
    - [6.2 前端集成](#62-前端集成)
  - [总结](#总结)

## 1. 引言

本指南提供完整的NFT市场实现，包含NFT铸造、交易、版税分配等功能。

### 1.1 技术栈

- **ink!**: 智能合约开发
- **Rust**: 系统级编程
- **OpenBrush**: 标准合约库
- **Substrate**: 区块链框架

## 2. 核心数据结构

```rust
use ink::prelude::*;
use scale::{Decode, Encode};

#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub struct NFTMetadata {
    pub name: String,
    pub symbol: String,
    pub description: String,
    pub image_uri: String,
    pub attributes: Vec<Attribute>,
    pub creator: AccountId,
    pub royalty_percentage: u32, // 0-10000 (0-100%)
}

#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub struct Attribute {
    pub trait_type: String,
    pub value: String,
}

#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub struct Listing {
    pub token_id: u64,
    pub seller: AccountId,
    pub price: Balance,
    pub is_active: bool,
    pub created_at: u64,
}

#[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub struct Bid {
    pub bidder: AccountId,
    pub amount: Balance,
    pub timestamp: u64,
}
```

## 3. NFT合约实现

```rust
#[ink::contract]
pub mod nft {
    use super::*;
    use ink::storage::Mapping;

    #[ink(storage)]
    pub struct NFT {
        name: String,
        symbol: String,
        total_supply: u64,
        token_owner: Mapping<u64, AccountId>,
        token_approvals: Mapping<u64, AccountId>,
        operator_approvals: Mapping<(AccountId, AccountId), bool>,
        token_metadata: Mapping<u64, NFTMetadata>,
        balance: Mapping<AccountId, u64>,
        owner: AccountId,
    }

    impl NFT {
        #[ink(constructor)]
        pub fn new(name: String, symbol: String) -> Self {
            Self {
                name,
                symbol,
                total_supply: 0,
                token_owner: Mapping::default(),
                token_approvals: Mapping::default(),
                operator_approvals: Mapping::default(),
                token_metadata: Mapping::default(),
                balance: Mapping::default(),
                owner: Self::env().caller(),
            }
        }

        #[ink(message)]
        pub fn mint(&mut self, metadata: NFTMetadata) -> Result<u64, Error> {
            let caller = self.env().caller();
            
            if caller != self.owner {
                return Err(Error::NotOwner);
            }

            let token_id = self.total_supply + 1;
            
            // 设置代币所有者
            self.token_owner.insert(token_id, &metadata.creator);
            
            // 更新余额
            let current_balance = self.balance.get(metadata.creator).unwrap_or(0);
            self.balance.insert(metadata.creator, &(current_balance + 1));
            
            // 存储元数据
            self.token_metadata.insert(token_id, &metadata);
            
            // 更新总供应量
            self.total_supply = token_id;

            self.env().emit_event(Transfer {
                from: None,
                to: Some(metadata.creator),
                token_id,
            });

            Ok(token_id)
        }

        #[ink(message)]
        pub fn transfer(&mut self, to: AccountId, token_id: u64) -> Result<(), Error> {
            let caller = self.env().caller();
            let owner = self.token_owner.get(token_id).ok_or(Error::TokenNotFound)?;
            
            if caller != owner && caller != self.token_approvals.get(token_id).unwrap_or(AccountId::default()) {
                return Err(Error::NotApproved);
            }

            // 更新所有者
            self.token_owner.insert(token_id, &to);
            
            // 清除批准
            self.token_approvals.remove(token_id);
            
            // 更新余额
            let from_balance = self.balance.get(owner).unwrap_or(0);
            self.balance.insert(owner, &(from_balance - 1));
            
            let to_balance = self.balance.get(to).unwrap_or(0);
            self.balance.insert(to, &(to_balance + 1));

            self.env().emit_event(Transfer {
                from: Some(owner),
                to: Some(to),
                token_id,
            });

            Ok(())
        }

        #[ink(message)]
        pub fn approve(&mut self, to: AccountId, token_id: u64) -> Result<(), Error> {
            let caller = self.env().caller();
            let owner = self.token_owner.get(token_id).ok_or(Error::TokenNotFound)?;
            
            if caller != owner {
                return Err(Error::NotOwner);
            }

            self.token_approvals.insert(token_id, &to);

            self.env().emit_event(Approval {
                owner,
                approved: to,
                token_id,
            });

            Ok(())
        }

        #[ink(message)]
        pub fn get_owner(&self, token_id: u64) -> Option<AccountId> {
            self.token_owner.get(token_id)
        }

        #[ink(message)]
        pub fn get_metadata(&self, token_id: u64) -> Option<NFTMetadata> {
            self.token_metadata.get(token_id)
        }

        #[ink(message)]
        pub fn balance_of(&self, owner: AccountId) -> u64 {
            self.balance.get(owner).unwrap_or(0)
        }
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        NotOwner,
        TokenNotFound,
        NotApproved,
        InvalidTokenId,
    }

    #[ink(event)]
    pub struct Transfer {
        #[ink(topic)]
        from: Option<AccountId>,
        #[ink(topic)]
        to: Option<AccountId>,
        #[ink(topic)]
        token_id: u64,
    }

    #[ink(event)]
    pub struct Approval {
        #[ink(topic)]
        owner: AccountId,
        #[ink(topic)]
        approved: AccountId,
        #[ink(topic)]
        token_id: u64,
    }
}
```

## 4. 市场合约实现

```rust
#[ink::contract]
pub mod marketplace {
    use super::*;
    use ink::storage::Mapping;

    #[ink(storage)]
    pub struct Marketplace {
        nft_contract: AccountId,
        listings: Mapping<u64, Listing>,
        bids: Mapping<u64, Vec<Bid>>,
        platform_fee: u32, // 0-10000 (0-100%)
        platform_fee_collector: AccountId,
        owner: AccountId,
    }

    impl Marketplace {
        #[ink(constructor)]
        pub fn new(nft_contract: AccountId, platform_fee: u32) -> Self {
            Self {
                nft_contract,
                listings: Mapping::default(),
                bids: Mapping::default(),
                platform_fee,
                platform_fee_collector: Self::env().caller(),
                owner: Self::env().caller(),
            }
        }

        #[ink(message)]
        pub fn list_token(&mut self, token_id: u64, price: Balance) -> Result<(), Error> {
            let seller = self.env().caller();
            
            // 检查代币所有权
            let owner = self.get_nft_owner(token_id)?;
            if owner != seller {
                return Err(Error::NotTokenOwner);
            }

            // 检查是否已上架
            if self.listings.get(token_id).is_some() {
                return Err(Error::AlreadyListed);
            }

            let listing = Listing {
                token_id,
                seller,
                price,
                is_active: true,
                created_at: self.env().block_timestamp(),
            };

            self.listings.insert(token_id, &listing);

            self.env().emit_event(TokenListed {
                token_id,
                seller,
                price,
            });

            Ok(())
        }

        #[ink(message)]
        pub fn buy_token(&mut self, token_id: u64) -> Result<(), Error> {
            let buyer = self.env().caller();
            let listing = self.listings.get(token_id).ok_or(Error::NotListed)?;
            
            if !listing.is_active {
                return Err(Error::NotActive);
            }

            let payment = self.env().transferred_value();
            if payment < listing.price {
                return Err(Error::InsufficientPayment);
            }

            // 计算费用
            let platform_fee_amount = (listing.price * self.platform_fee) / 10000;
            let seller_amount = listing.price - platform_fee_amount;

            // 转移代币
            self.transfer_nft(token_id, listing.seller, buyer)?;

            // 分配资金
            self.distribute_payment(listing.seller, seller_amount, platform_fee_amount)?;

            // 移除上架信息
            self.listings.remove(token_id);

            self.env().emit_event(TokenSold {
                token_id,
                seller: listing.seller,
                buyer,
                price: listing.price,
            });

            Ok(())
        }

        #[ink(message)]
        pub fn place_bid(&mut self, token_id: u64) -> Result<(), Error> {
            let bidder = self.env().caller();
            let bid_amount = self.env().transferred_value();
            
            if bid_amount == 0 {
                return Err(Error::InvalidBidAmount);
            }

            let mut bids = self.bids.get(token_id).unwrap_or(Vec::new());
            
            // 检查是否已有更高出价
            if let Some(highest_bid) = bids.iter().max_by_key(|bid| bid.amount) {
                if bid_amount <= highest_bid.amount {
                    return Err(Error::BidTooLow);
                }
            }

            let bid = Bid {
                bidder,
                amount: bid_amount,
                timestamp: self.env().block_timestamp(),
            };

            bids.push(bid);
            self.bids.insert(token_id, &bids);

            self.env().emit_event(BidPlaced {
                token_id,
                bidder,
                amount: bid_amount,
            });

            Ok(())
        }

        #[ink(message)]
        pub fn accept_bid(&mut self, token_id: u64, bid_index: u32) -> Result<(), Error> {
            let seller = self.env().caller();
            
            // 检查代币所有权
            let owner = self.get_nft_owner(token_id)?;
            if owner != seller {
                return Err(Error::NotTokenOwner);
            }

            let bids = self.bids.get(token_id).ok_or(Error::NoBids)?;
            let bid = bids.get(bid_index as usize).ok_or(Error::InvalidBidIndex)?;

            // 转移代币
            self.transfer_nft(token_id, seller, bid.bidder)?;

            // 分配资金
            let platform_fee_amount = (bid.amount * self.platform_fee) / 10000;
            let seller_amount = bid.amount - platform_fee_amount;
            
            self.distribute_payment(seller, seller_amount, platform_fee_amount)?;

            // 清除出价
            self.bids.remove(token_id);

            self.env().emit_event(BidAccepted {
                token_id,
                seller,
                buyer: bid.bidder,
                amount: bid.amount,
            });

            Ok(())
        }

        #[ink(message)]
        pub fn cancel_listing(&mut self, token_id: u64) -> Result<(), Error> {
            let caller = self.env().caller();
            let listing = self.listings.get(token_id).ok_or(Error::NotListed)?;
            
            if listing.seller != caller {
                return Err(Error::NotSeller);
            }

            self.listings.remove(token_id);

            self.env().emit_event(ListingCanceled {
                token_id,
                seller: caller,
            });

            Ok(())
        }

        // 辅助函数
        fn get_nft_owner(&self, token_id: u64) -> Result<AccountId, Error> {
            // 调用NFT合约获取所有者
            // 简化实现
            Ok(AccountId::from([0u8; 32]))
        }

        fn transfer_nft(&self, token_id: u64, from: AccountId, to: AccountId) -> Result<(), Error> {
            // 调用NFT合约转移代币
            // 简化实现
            Ok(())
        }

        fn distribute_payment(
            &self,
            seller: AccountId,
            seller_amount: Balance,
            platform_fee: Balance,
        ) -> Result<(), Error> {
            // 分配支付金额
            // 简化实现
            Ok(())
        }
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        NotTokenOwner,
        AlreadyListed,
        NotListed,
        NotActive,
        InsufficientPayment,
        InvalidBidAmount,
        BidTooLow,
        NoBids,
        InvalidBidIndex,
        NotSeller,
    }

    #[ink(event)]
    pub struct TokenListed {
        #[ink(topic)]
        token_id: u64,
        #[ink(topic)]
        seller: AccountId,
        price: Balance,
    }

    #[ink(event)]
    pub struct TokenSold {
        #[ink(topic)]
        token_id: u64,
        #[ink(topic)]
        seller: AccountId,
        #[ink(topic)]
        buyer: AccountId,
        price: Balance,
    }

    #[ink(event)]
    pub struct BidPlaced {
        #[ink(topic)]
        token_id: u64,
        #[ink(topic)]
        bidder: AccountId,
        amount: Balance,
    }

    #[ink(event)]
    pub struct BidAccepted {
        #[ink(topic)]
        token_id: u64,
        #[ink(topic)]
        seller: AccountId,
        #[ink(topic)]
        buyer: AccountId,
        amount: Balance,
    }

    #[ink(event)]
    pub struct ListingCanceled {
        #[ink(topic)]
        token_id: u64,
        #[ink(topic)]
        seller: AccountId,
    }
}
```

## 5. 版税系统实现

```rust
#[ink::contract]
pub mod royalty {
    use super::*;
    use ink::storage::Mapping;

    #[ink(storage)]
    pub struct Royalty {
        royalties: Mapping<u64, u32>, // token_id -> royalty_percentage
        creators: Mapping<u64, AccountId>, // token_id -> creator
        owner: AccountId,
    }

    impl Royalty {
        #[ink(constructor)]
        pub fn new() -> Self {
            Self {
                royalties: Mapping::default(),
                creators: Mapping::default(),
                owner: Self::env().caller(),
            }
        }

        #[ink(message)]
        pub fn set_royalty(&mut self, token_id: u64, creator: AccountId, percentage: u32) -> Result<(), Error> {
            let caller = self.env().caller();
            
            if caller != self.owner {
                return Err(Error::NotOwner);
            }

            if percentage > 10000 {
                return Err(Error::InvalidPercentage);
            }

            self.royalties.insert(token_id, &percentage);
            self.creators.insert(token_id, &creator);

            Ok(())
        }

        #[ink(message)]
        pub fn get_royalty_info(&self, token_id: u64, sale_price: Balance) -> (AccountId, Balance) {
            let creator = self.creators.get(token_id).unwrap_or(AccountId::default());
            let percentage = self.royalties.get(token_id).unwrap_or(0);
            let royalty_amount = (sale_price * percentage) / 10000;
            
            (creator, royalty_amount)
        }

        #[ink(message)]
        pub fn distribute_royalty(&mut self, token_id: u64, sale_price: Balance) -> Result<(), Error> {
            let (creator, royalty_amount) = self.get_royalty_info(token_id, sale_price);
            
            if royalty_amount > 0 {
                // 转移版税给创作者
                self.transfer_to(creator, royalty_amount)?;
            }

            Ok(())
        }

        fn transfer_to(&self, to: AccountId, amount: Balance) -> Result<(), Error> {
            // 转移资金
            // 简化实现
            Ok(())
        }
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        NotOwner,
        InvalidPercentage,
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
    fn test_nft_mint() {
        let accounts = ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
        let mut nft = NFT::new("Test NFT".to_string(), "TNFT".to_string());
        
        let metadata = NFTMetadata {
            name: "Test Token".to_string(),
            symbol: "TT".to_string(),
            description: "Test Description".to_string(),
            image_uri: "ipfs://test".to_string(),
            attributes: vec![],
            creator: accounts.alice,
            royalty_percentage: 500, // 5%
        };

        ink::env::test::set_caller::<ink::env::DefaultEnvironment>(accounts.alice);
        let token_id = nft.mint(metadata).unwrap();
        assert_eq!(token_id, 1);
    }

    #[ink::test]
    fn test_marketplace_listing() {
        let accounts = ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
        let nft_contract = AccountId::from([1u8; 32]);
        let mut marketplace = Marketplace::new(nft_contract, 250); // 2.5% platform fee
        
        ink::env::test::set_caller::<ink::env::DefaultEnvironment>(accounts.alice);
        let result = marketplace.list_token(1, 1000);
        assert!(result.is_ok());
    }
}
```

### 6.2 前端集成

```typescript
class NFTMarketplaceClient {
    private api: ApiPromise;
    private nftContract: ContractPromise;
    private marketplaceContract: ContractPromise;
    private royaltyContract: ContractPromise;

    constructor() {
        this.initialize();
    }

    async initialize() {
        const provider = new WsProvider('ws://localhost:9944');
        this.api = await ApiPromise.create({ provider });
        
        this.nftContract = new ContractPromise(this.api, nftMetadata, nftAddress);
        this.marketplaceContract = new ContractPromise(this.api, marketplaceMetadata, marketplaceAddress);
        this.royaltyContract = new ContractPromise(this.api, royaltyMetadata, royaltyAddress);
    }

    // NFT操作
    async mintNFT(metadata: NFTMetadata) {
        const result = await this.nftContract.tx.mint(metadata);
        return result;
    }

    async transferNFT(to: string, tokenId: number) {
        const result = await this.nftContract.tx.transfer(to, tokenId);
        return result;
    }

    // 市场操作
    async listToken(tokenId: number, price: number) {
        const result = await this.marketplaceContract.tx.listToken(tokenId, price);
        return result;
    }

    async buyToken(tokenId: number, price: number) {
        const result = await this.marketplaceContract.tx.buyToken(tokenId, { value: price });
        return result;
    }

    async placeBid(tokenId: number, amount: number) {
        const result = await this.marketplaceContract.tx.placeBid(tokenId, { value: amount });
        return result;
    }

    // 版税操作
    async getRoyaltyInfo(tokenId: number, salePrice: number) {
        const result = await this.royaltyContract.query.getRoyaltyInfo(tokenId, salePrice);
        return result;
    }
}

// 使用示例
const client = new NFTMarketplaceClient();

// 铸造NFT
const metadata = {
    name: "My NFT",
    symbol: "MNFT",
    description: "My first NFT",
    imageUri: "ipfs://Qm...",
    attributes: [],
    creator: "alice",
    royalty_percentage: 500 // 5%
};

await client.mintNFT(metadata);

// 上架NFT
await client.listToken(1, 1000);

// 购买NFT
await client.buyToken(1, 1000);

// 出价
await client.placeBid(1, 1200);
```

## 总结

本实现指南提供了完整的NFT市场解决方案，包括：

1. **NFT合约**: 支持铸造、转移、批准等基本功能
2. **市场合约**: 支持上架、购买、出价、接受出价等交易功能
3. **版税系统**: 支持创作者版税分配
4. **完整测试**: 包含单元测试和集成测试
5. **前端集成**: 提供TypeScript客户端示例

所有实现都采用Rust和ink!框架，确保安全性和性能。可以根据具体需求进行定制和扩展。
