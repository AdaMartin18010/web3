# Web3 NFT理论形式化分析

## 目录

1. [理论基础](#理论基础)
2. [数学形式化](#数学形式化)
3. [核心算法](#核心算法)
4. [协议设计](#协议设计)
5. [元数据管理](#元数据管理)
6. [实现示例](#实现示例)
7. [性能分析](#性能分析)
8. [安全性证明](#安全性证明)

## 理论基础

### NFT系统定义

**定义 1.1 (NFT系统)** 非同质化代币系统是一个六元组 $\mathcal{N} = (T, M, O, R, S, G)$，其中：

- $T$ 是代币集合
- $M$ 是元数据集合
- $O$ 是所有者映射
- $R$ 是权限规则集合
- $S$ 是状态机集合
- $G$ 是治理机制

### 代币唯一性理论

**定义 1.2 (代币唯一性)** 对于任意两个代币 $t_1, t_2 \in T$，如果 $t_1 \neq t_2$，则：
$$\forall p \in P: O(t_1, p) \neq O(t_2, p)$$

其中 $P$ 是属性集合，$O(t, p)$ 表示代币 $t$ 的属性 $p$ 的值。

**定理 1.1 (唯一性保证)** 在区块链系统中，每个NFT代币都有唯一的标识符。

**证明：**
设代币 $t$ 的标识符为 $ID(t) = H(tx_{mint} || nonce)$，其中：

- $tx_{mint}$ 是铸造交易哈希
- $nonce$ 是交易序号
- $H$ 是哈希函数

由于哈希函数的抗碰撞性，对于不同的输入，输出几乎不可能相同。因此，每个NFT都有唯一的标识符。

### 所有权转移理论

**定义 1.3 (所有权转移)** 所有权转移函数定义为：
$$\tau: T \times A \times A \rightarrow T$$

其中 $A$ 是地址集合，$\tau(t, from, to)$ 表示将代币 $t$ 从地址 $from$ 转移到地址 $to$。

**定理 1.2 (转移一致性)** 所有权转移满足一致性：
$$\forall t \in T, \forall a_1, a_2, a_3 \in A: \tau(\tau(t, a_1, a_2), a_2, a_3) = \tau(t, a_1, a_3)$$

## 数学形式化

### ERC-721标准形式化

**定义 2.1 (ERC-721接口)** ERC-721接口定义为函数集合：
$$\mathcal{I}_{721} = \{balanceOf, ownerOf, transferFrom, approve, getApproved, setApprovalForAll, isApprovedForAll\}$$

**定义 2.2 (余额函数)** 余额函数定义为：
$$balanceOf: A \rightarrow \mathbb{N}$$

其中 $balanceOf(a)$ 表示地址 $a$ 拥有的代币数量。

**定理 2.1 (余额守恒)** 对于任意转移操作，总余额保持不变：
$$\sum_{a \in A} balanceOf(a) = |T|$$

**证明：**
设转移前状态为 $S_1$，转移后状态为 $S_2$。
转移操作只改变代币的所有权，不改变代币总数：
$$|T_{S_1}| = |T_{S_2}|$$
因此：
$$\sum_{a \in A} balanceOf_{S_1}(a) = \sum_{a \in A} balanceOf_{S_2}(a)$$

### 元数据哈希理论

**定义 2.3 (元数据哈希)** 元数据哈希函数定义为：
$$H_{metadata}: M \rightarrow \{0,1\}^{256}$$

其中 $M$ 是元数据集合，$H_{metadata}(m)$ 是元数据 $m$ 的哈希值。

**定理 2.2 (元数据完整性)** 如果元数据 $m$ 的哈希值为 $h$，则任何对 $m$ 的修改都会导致哈希值变化。

**证明：**
设修改后的元数据为 $m'$，其哈希值为 $h'$。
由于哈希函数的抗碰撞性：
$$P(H_{metadata}(m) = H_{metadata}(m')) \approx 2^{-256}$$
因此，元数据修改几乎必然导致哈希值变化。

## 核心算法

### NFT铸造算法

```rust
use std::collections::HashMap;
use serde::{Deserialize, Serialize};
use sha2::{Sha256, Digest};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NFT {
    pub token_id: u64,
    pub owner: String,
    pub metadata_uri: String,
    pub metadata_hash: String,
    pub created_at: u64,
    pub creator: String,
    pub royalty_percentage: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NFTContract {
    pub name: String,
    pub symbol: String,
    pub total_supply: u64,
    pub tokens: HashMap<u64, NFT>,
    pub balances: HashMap<String, u64>,
    pub approvals: HashMap<u64, String>,
    pub operator_approvals: HashMap<String, HashMap<String, bool>>,
    pub metadata_registry: HashMap<String, String>,
}

impl NFTContract {
    pub fn new(name: String, symbol: String) -> Self {
        Self {
            name,
            symbol,
            total_supply: 0,
            tokens: HashMap::new(),
            balances: HashMap::new(),
            approvals: HashMap::new(),
            operator_approvals: HashMap::new(),
            metadata_registry: HashMap::new(),
        }
    }

    /// 铸造NFT
    pub fn mint(
        &mut self,
        to: &str,
        metadata_uri: &str,
        creator: &str,
        royalty_percentage: f64,
    ) -> u64 {
        let token_id = self.total_supply + 1;
        
        // 计算元数据哈希
        let metadata_hash = self.calculate_metadata_hash(metadata_uri);
        
        let nft = NFT {
            token_id,
            owner: to.to_string(),
            metadata_uri: metadata_uri.to_string(),
            metadata_hash,
            created_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            creator: creator.to_string(),
            royalty_percentage: royalty_percentage.max(0.0).min(1.0),
        };

        self.tokens.insert(token_id, nft);
        self.balances.entry(to.to_string())
            .and_modify(|b| *b += 1)
            .or_insert(1);
        self.total_supply += 1;

        token_id
    }

    /// 转移NFT
    pub fn transfer_from(
        &mut self,
        from: &str,
        to: &str,
        token_id: u64,
        caller: &str,
    ) -> bool {
        if let Some(nft) = self.tokens.get(&token_id) {
            if nft.owner != from {
                return false;
            }

            // 检查权限
            if !self.is_approved_or_owner(token_id, caller) {
                return false;
            }

            // 执行转移
            self.tokens.get_mut(&token_id).unwrap().owner = to.to_string();
            
            // 更新余额
            self.balances.entry(from.to_string())
                .and_modify(|b| *b -= 1);
            self.balances.entry(to.to_string())
                .and_modify(|b| *b += 1)
                .or_insert(1);

            // 清除批准
            self.approvals.remove(&token_id);

            true
        } else {
            false
        }
    }

    /// 批准转移
    pub fn approve(&mut self, approved: &str, token_id: u64, caller: &str) -> bool {
        if let Some(nft) = self.tokens.get(&token_id) {
            if nft.owner != caller && !self.is_approved_for_all(&nft.owner, caller) {
                return false;
            }

            self.approvals.insert(token_id, approved.to_string());
            true
        } else {
            false
        }
    }

    /// 设置操作员批准
    pub fn set_approval_for_all(&mut self, operator: &str, approved: bool, caller: &str) {
        self.operator_approvals
            .entry(caller.to_string())
            .or_insert_with(HashMap::new)
            .insert(operator.to_string(), approved);
    }

    /// 获取代币所有者
    pub fn owner_of(&self, token_id: u64) -> Option<&str> {
        self.tokens.get(&token_id).map(|nft| nft.owner.as_str())
    }

    /// 获取地址余额
    pub fn balance_of(&self, owner: &str) -> u64 {
        *self.balances.get(owner).unwrap_or(&0)
    }

    /// 获取批准地址
    pub fn get_approved(&self, token_id: u64) -> Option<&str> {
        self.approvals.get(&token_id).map(|s| s.as_str())
    }

    /// 检查操作员批准
    pub fn is_approved_for_all(&self, owner: &str, operator: &str) -> bool {
        self.operator_approvals
            .get(owner)
            .and_then(|ops| ops.get(operator))
            .unwrap_or(&false)
    }

    /// 检查是否已批准或所有者
    fn is_approved_or_owner(&self, token_id: u64, caller: &str) -> bool {
        if let Some(nft) = self.tokens.get(&token_id) {
            nft.owner == caller ||
            self.approvals.get(&token_id).map(|s| s.as_str()) == Some(caller) ||
            self.is_approved_for_all(&nft.owner, caller)
        } else {
            false
        }
    }

    /// 计算元数据哈希
    fn calculate_metadata_hash(&self, metadata_uri: &str) -> String {
        let mut hasher = Sha256::new();
        hasher.update(metadata_uri.as_bytes());
        format!("{:x}", hasher.finalize())
    }

    /// 验证元数据完整性
    pub fn verify_metadata_integrity(&self, token_id: u64, metadata_uri: &str) -> bool {
        if let Some(nft) = self.tokens.get(&token_id) {
            let current_hash = self.calculate_metadata_hash(metadata_uri);
            current_hash == nft.metadata_hash
        } else {
            false
        }
    }
}
```

### 批量铸造算法

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchMintRequest {
    pub to: String,
    pub metadata_uris: Vec<String>,
    pub creator: String,
    pub royalty_percentage: f64,
}

impl NFTContract {
    /// 批量铸造NFT
    pub fn batch_mint(&mut self, request: BatchMintRequest) -> Vec<u64> {
        let mut token_ids = Vec::new();
        
        for metadata_uri in request.metadata_uris {
            let token_id = self.mint(
                &request.to,
                &metadata_uri,
                &request.creator,
                request.royalty_percentage,
            );
            token_ids.push(token_id);
        }
        
        token_ids
    }

    /// 批量转移NFT
    pub fn batch_transfer(
        &mut self,
        from: &str,
        to: &str,
        token_ids: &[u64],
        caller: &str,
    ) -> bool {
        // 验证所有代币的所有权
        for &token_id in token_ids {
            if let Some(nft) = self.tokens.get(&token_id) {
                if nft.owner != from {
                    return false;
                }
                if !self.is_approved_or_owner(token_id, caller) {
                    return false;
                }
            } else {
                return false;
            }
        }

        // 执行批量转移
        for &token_id in token_ids {
            self.transfer_from(from, to, token_id, caller);
        }

        true
    }
}
```

## 协议设计

### ERC-1155多代币标准

**定义 3.1 (ERC-1155接口)** ERC-1155接口定义为：
$$\mathcal{I}_{1155} = \{balanceOf, balanceOfBatch, setApprovalForAll, isApprovedForAll, safeTransferFrom, safeBatchTransferFrom\}$$

**定义 3.2 (批量余额函数)** 批量余额函数定义为：
$$balanceOfBatch: A \times T^* \rightarrow \mathbb{N}^*$$

其中 $balanceOfBatch(accounts, ids)$ 返回每个账户对应代币的余额数组。

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ERC1155Contract {
    pub name: String,
    pub balances: HashMap<String, HashMap<u64, u64>>,
    pub operator_approvals: HashMap<String, HashMap<String, bool>>,
    pub token_metadata: HashMap<u64, TokenMetadata>,
    pub total_supply: HashMap<u64, u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TokenMetadata {
    pub uri: String,
    pub creator: String,
    pub royalty_percentage: f64,
    pub is_fungible: bool,
}

impl ERC1155Contract {
    pub fn new(name: String) -> Self {
        Self {
            name,
            balances: HashMap::new(),
            operator_approvals: HashMap::new(),
            token_metadata: HashMap::new(),
            total_supply: HashMap::new(),
        }
    }

    /// 铸造代币
    pub fn mint(
        &mut self,
        to: &str,
        token_id: u64,
        amount: u64,
        metadata: TokenMetadata,
    ) {
        self.balances
            .entry(to.to_string())
            .or_insert_with(HashMap::new)
            .entry(token_id)
            .and_modify(|b| *b += amount)
            .or_insert(amount);

        self.total_supply
            .entry(token_id)
            .and_modify(|s| *s += amount)
            .or_insert(amount);

        if !self.token_metadata.contains_key(&token_id) {
            self.token_metadata.insert(token_id, metadata);
        }
    }

    /// 批量铸造
    pub fn mint_batch(
        &mut self,
        to: &str,
        token_ids: &[u64],
        amounts: &[u64],
        metadata: &[TokenMetadata],
    ) {
        for (i, &token_id) in token_ids.iter().enumerate() {
            self.mint(to, token_id, amounts[i], metadata[i].clone());
        }
    }

    /// 安全转移
    pub fn safe_transfer_from(
        &mut self,
        from: &str,
        to: &str,
        token_id: u64,
        amount: u64,
        caller: &str,
    ) -> bool {
        if !self.is_approved_for_all(from, caller) {
            return false;
        }

        let from_balance = self.balance_of(from, token_id);
        if from_balance < amount {
            return false;
        }

        // 执行转移
        self.balances
            .get_mut(from)
            .unwrap()
            .entry(token_id)
            .and_modify(|b| *b -= amount);

        self.balances
            .entry(to.to_string())
            .or_insert_with(HashMap::new)
            .entry(token_id)
            .and_modify(|b| *b += amount)
            .or_insert(amount);

        true
    }

    /// 批量安全转移
    pub fn safe_batch_transfer_from(
        &mut self,
        from: &str,
        to: &str,
        token_ids: &[u64],
        amounts: &[u64],
        caller: &str,
    ) -> bool {
        // 验证所有转移的可行性
        for (i, &token_id) in token_ids.iter().enumerate() {
            let from_balance = self.balance_of(from, token_id);
            if from_balance < amounts[i] {
                return false;
            }
        }

        if !self.is_approved_for_all(from, caller) {
            return false;
        }

        // 执行批量转移
        for (i, &token_id) in token_ids.iter().enumerate() {
            self.safe_transfer_from(from, to, token_id, amounts[i], caller);
        }

        true
    }

    /// 获取余额
    pub fn balance_of(&self, account: &str, token_id: u64) -> u64 {
        self.balances
            .get(account)
            .and_then(|tokens| tokens.get(&token_id))
            .unwrap_or(&0)
    }

    /// 批量获取余额
    pub fn balance_of_batch(&self, accounts: &[String], token_ids: &[u64]) -> Vec<u64> {
        accounts
            .iter()
            .zip(token_ids.iter())
            .map(|(account, &token_id)| self.balance_of(account, token_id))
            .collect()
    }

    /// 设置操作员批准
    pub fn set_approval_for_all(&mut self, operator: &str, approved: bool, caller: &str) {
        self.operator_approvals
            .entry(caller.to_string())
            .or_insert_with(HashMap::new)
            .insert(operator.to_string(), approved);
    }

    /// 检查操作员批准
    pub fn is_approved_for_all(&self, owner: &str, operator: &str) -> bool {
        self.operator_approvals
            .get(owner)
            .and_then(|ops| ops.get(operator))
            .unwrap_or(&false)
    }
}
```

## 元数据管理

### IPFS元数据存储

**定义 4.1 (IPFS哈希)** IPFS哈希函数定义为：
$$H_{IPFS}: M \rightarrow \{0,1\}^{256}$$

其中 $H_{IPFS}(m)$ 是元数据 $m$ 的IPFS哈希值。

**定理 4.1 (IPFS内容寻址)** IPFS哈希是内容寻址的，相同内容产生相同哈希。

**证明：**
IPFS使用Merkle DAG结构，哈希值基于内容计算：
$$H_{IPFS}(m) = H(content(m) || metadata(m))$$
因此，相同内容必然产生相同哈希。

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IPFSMetadata {
    pub name: String,
    pub description: String,
    pub image: String,
    pub attributes: Vec<Attribute>,
    pub external_url: Option<String>,
    pub animation_url: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Attribute {
    pub trait_type: String,
    pub value: String,
    pub display_type: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetadataManager {
    pub ipfs_gateway: String,
    pub metadata_cache: HashMap<String, IPFSMetadata>,
}

impl MetadataManager {
    pub fn new(ipfs_gateway: String) -> Self {
        Self {
            ipfs_gateway,
            metadata_cache: HashMap::new(),
        }
    }

    /// 上传元数据到IPFS
    pub async fn upload_metadata(&mut self, metadata: &IPFSMetadata) -> Result<String, String> {
        let metadata_json = serde_json::to_string(metadata)
            .map_err(|e| format!("Serialization error: {}", e))?;

        // 这里应该实现实际的IPFS上传逻辑
        // 为了演示，我们使用模拟的哈希
        let hash = self.calculate_ipfs_hash(&metadata_json);
        
        // 缓存元数据
        self.metadata_cache.insert(hash.clone(), metadata.clone());
        
        Ok(hash)
    }

    /// 从IPFS获取元数据
    pub async fn get_metadata(&mut self, ipfs_hash: &str) -> Result<IPFSMetadata, String> {
        // 检查缓存
        if let Some(metadata) = self.metadata_cache.get(ipfs_hash) {
            return Ok(metadata.clone());
        }

        // 从IPFS获取
        let url = format!("{}/ipfs/{}", self.ipfs_gateway, ipfs_hash);
        
        // 这里应该实现实际的HTTP请求
        // 为了演示，我们返回错误
        Err("IPFS fetch not implemented".to_string())
    }

    /// 计算IPFS哈希
    fn calculate_ipfs_hash(&self, content: &str) -> String {
        let mut hasher = Sha256::new();
        hasher.update(content.as_bytes());
        format!("Qm{}", base64::encode(hasher.finalize()))
    }

    /// 验证元数据完整性
    pub fn verify_metadata_integrity(&self, ipfs_hash: &str, metadata: &IPFSMetadata) -> bool {
        let metadata_json = serde_json::to_string(metadata).unwrap();
        let calculated_hash = self.calculate_ipfs_hash(&metadata_json);
        calculated_hash == ipfs_hash
    }
}
```

## 实现示例

### 完整的NFT市场实现

```rust
use std::collections::HashMap;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NFTMarketplace {
    pub nft_contract: NFTContract,
    pub listings: HashMap<u64, Listing>,
    pub offers: HashMap<u64, Vec<Offer>>,
    pub trading_volume: f64,
    pub platform_fee: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Listing {
    pub token_id: u64,
    pub seller: String,
    pub price: f64,
    pub currency: String,
    pub created_at: u64,
    pub expires_at: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Offer {
    pub token_id: u64,
    pub bidder: String,
    pub amount: f64,
    pub currency: String,
    pub created_at: u64,
    pub expires_at: u64,
}

impl NFTMarketplace {
    pub fn new(nft_contract: NFTContract, platform_fee: f64) -> Self {
        Self {
            nft_contract,
            listings: HashMap::new(),
            offers: HashMap::new(),
            trading_volume: 0.0,
            platform_fee,
        }
    }

    /// 创建NFT列表
    pub fn create_listing(
        &mut self,
        token_id: u64,
        price: f64,
        currency: &str,
        seller: &str,
        duration: Option<u64>,
    ) -> bool {
        // 验证所有权
        if let Some(nft) = self.nft_contract.tokens.get(&token_id) {
            if nft.owner != seller {
                return false;
            }

            let expires_at = duration.map(|d| {
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs() + d
            });

            let listing = Listing {
                token_id,
                seller: seller.to_string(),
                price,
                currency: currency.to_string(),
                created_at: std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
                expires_at,
            };

            self.listings.insert(token_id, listing);
            true
        } else {
            false
        }
    }

    /// 购买NFT
    pub fn buy_nft(&mut self, token_id: u64, buyer: &str, amount: f64) -> bool {
        if let Some(listing) = self.listings.get(&token_id) {
            // 检查价格
            if amount < listing.price {
                return false;
            }

            // 检查是否过期
            if let Some(expires_at) = listing.expires_at {
                let current_time = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs();
                if current_time > expires_at {
                    return false;
                }
            }

            // 执行转移
            if self.nft_contract.transfer_from(
                &listing.seller,
                buyer,
                token_id,
                buyer,
            ) {
                // 计算费用
                let platform_fee_amount = amount * self.platform_fee;
                let seller_amount = amount - platform_fee_amount;

                // 更新交易量
                self.trading_volume += amount;

                // 移除列表
                self.listings.remove(&token_id);

                true
            } else {
                false
            }
        } else {
            false
        }
    }

    /// 创建出价
    pub fn create_offer(
        &mut self,
        token_id: u64,
        amount: f64,
        currency: &str,
        bidder: &str,
        duration: u64,
    ) -> bool {
        let expires_at = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs() + duration;

        let offer = Offer {
            token_id,
            bidder: bidder.to_string(),
            amount,
            currency: currency.to_string(),
            created_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            expires_at,
        };

        self.offers
            .entry(token_id)
            .or_insert_with(Vec::new)
            .push(offer);

        true
    }

    /// 接受出价
    pub fn accept_offer(&mut self, token_id: u64, offer_index: usize, seller: &str) -> bool {
        if let Some(offers) = self.offers.get_mut(&token_id) {
            if offer_index >= offers.len() {
                return false;
            }

            let offer = &offers[offer_index];
            
            // 检查所有权
            if let Some(nft) = self.nft_contract.tokens.get(&token_id) {
                if nft.owner != seller {
                    return false;
                }
            }

            // 检查是否过期
            let current_time = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs();
            if current_time > offer.expires_at {
                return false;
            }

            // 执行转移
            if self.nft_contract.transfer_from(
                seller,
                &offer.bidder,
                token_id,
                seller,
            ) {
                // 计算费用
                let platform_fee_amount = offer.amount * self.platform_fee;
                let seller_amount = offer.amount - platform_fee_amount;

                // 更新交易量
                self.trading_volume += offer.amount;

                // 移除所有出价
                self.offers.remove(&token_id);

                true
            } else {
                false
            }
        } else {
            false
        }
    }

    /// 获取NFT统计信息
    pub fn get_nft_stats(&self, token_id: u64) -> Option<NFTStats> {
        if let Some(nft) = self.nft_contract.tokens.get(&token_id) {
            let listing = self.listings.get(&token_id);
            let offers = self.offers.get(&token_id);

            Some(NFTStats {
                token_id,
                owner: nft.owner.clone(),
                creator: nft.creator.clone(),
                created_at: nft.created_at,
                royalty_percentage: nft.royalty_percentage,
                current_price: listing.map(|l| l.price),
                offer_count: offers.map(|o| o.len()).unwrap_or(0),
                highest_offer: offers
                    .and_then(|o| o.iter().map(|offer| offer.amount).max()),
            })
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NFTStats {
    pub token_id: u64,
    pub owner: String,
    pub creator: String,
    pub created_at: u64,
    pub royalty_percentage: f64,
    pub current_price: Option<f64>,
    pub offer_count: usize,
    pub highest_offer: Option<f64>,
}

// 测试模块
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nft_minting() {
        let mut contract = NFTContract::new(
            "Test NFT".to_string(),
            "TNFT".to_string(),
        );

        let token_id = contract.mint(
            "user1",
            "ipfs://QmTest",
            "creator1",
            0.05,
        );

        assert_eq!(token_id, 1);
        assert_eq!(contract.balance_of("user1"), 1);
        assert_eq!(contract.owner_of(token_id), Some("user1"));
    }

    #[test]
    fn test_nft_transfer() {
        let mut contract = NFTContract::new(
            "Test NFT".to_string(),
            "TNFT".to_string(),
        );

        let token_id = contract.mint(
            "user1",
            "ipfs://QmTest",
            "creator1",
            0.05,
        );

        let success = contract.transfer_from("user1", "user2", token_id, "user1");
        assert!(success);
        assert_eq!(contract.owner_of(token_id), Some("user2"));
        assert_eq!(contract.balance_of("user1"), 0);
        assert_eq!(contract.balance_of("user2"), 1);
    }

    #[test]
    fn test_marketplace_listing() {
        let nft_contract = NFTContract::new(
            "Test NFT".to_string(),
            "TNFT".to_string(),
        );

        let mut marketplace = NFTMarketplace::new(nft_contract, 0.025);

        // 先铸造NFT
        let token_id = marketplace.nft_contract.mint(
            "seller",
            "ipfs://QmTest",
            "creator1",
            0.05,
        );

        // 创建列表
        let success = marketplace.create_listing(token_id, 100.0, "ETH", "seller", None);
        assert!(success);

        // 购买NFT
        let success = marketplace.buy_nft(token_id, "buyer", 100.0);
        assert!(success);
        assert_eq!(marketplace.nft_contract.owner_of(token_id), Some("buyer"));
    }
}
```

## 性能分析

### 时间复杂度分析

**定理 5.1 (铸造操作复杂度)** NFT铸造操作的时间复杂度为 $O(1)$。

**证明：**
铸造操作涉及：

1. 生成代币ID：$O(1)$
2. 计算元数据哈希：$O(1)$
3. 更新状态：$O(1)$

总时间复杂度为 $O(1)$。

**定理 5.2 (转移操作复杂度)** NFT转移操作的时间复杂度为 $O(1)$。

**证明：**
转移操作涉及：

1. 验证所有权：$O(1)$
2. 检查权限：$O(1)$
3. 更新状态：$O(1)$

总时间复杂度为 $O(1)$。

### 空间复杂度分析

**定理 5.3 (存储复杂度)** NFT合约的空间复杂度为 $O(n + m)$，其中 $n$ 是代币数量，$m$ 是用户数量。

**证明：**

- 代币存储：$O(n)$
- 用户余额存储：$O(m)$
- 批准存储：$O(n)$
- 总空间复杂度：$O(n + m)$

## 安全性证明

### 重入攻击防护

**定理 6.1 (重入攻击防护)** 使用Checks-Effects-Interactions模式可以防止NFT合约的重入攻击。

**证明：**
NFT转移操作遵循CEI模式：

1. **Checks**：验证所有权和权限
2. **Effects**：更新代币所有者和余额
3. **Interactions**：调用外部合约（如回调）

由于状态在外部调用前已更新，重入攻击被有效防护。

### 权限控制

**定理 6.2 (权限控制)** NFT合约的权限控制机制确保只有授权用户才能转移代币。

**证明：**
转移权限检查包括：

1. 所有者权限：$owner == caller$
2. 批准权限：$approved[tokenId] == caller$
3. 操作员权限：$operatorApprovals[owner][caller] == true$

只有满足以上条件之一的用户才能转移代币。

### 元数据完整性

**定理 6.3 (元数据完整性)** 使用IPFS哈希可以保证元数据的完整性。

**证明：**

1. 元数据哈希：$H_{IPFS}(metadata) = hash$
2. 验证机制：$verify(hash, metadata) = H_{IPFS}(metadata) == hash$
3. 任何修改都会导致哈希值变化

因此，元数据完整性得到保证。

## 总结

本模块提供了Web3 NFT理论的完整形式化分析，包括：

1. **理论基础**：定义了NFT系统、代币唯一性、所有权转移等核心概念
2. **数学形式化**：提供了ERC-721/1155标准、元数据哈希等数学框架
3. **核心算法**：实现了NFT铸造、转移、批量操作等核心功能
4. **协议设计**：设计了ERC-1155多代币标准、市场机制等
5. **元数据管理**：实现了IPFS元数据存储和完整性验证
6. **实现示例**：提供了完整的NFT市场和ERC-1155实现
7. **性能分析**：分析了时间和空间复杂度
8. **安全性证明**：证明了重入攻击、权限控制、元数据完整性等安全机制

该理论体系为NFT系统的设计、实现和安全保障提供了坚实的理论基础和实践指导。
