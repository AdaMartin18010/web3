# 自动做市商 (Automated Market Makers)

## 概述

自动做市商（AMM）是DeFi生态系统的核心组件，通过算法定价机制实现去中心化的流动性提供和资产交换。

## 1. 基本定义

**定义 1.1**（自动做市商）：
使用数学公式自动确定资产价格的去中心化交易协议。

**定义 1.2**（流动性池）：
由流动性提供者存入的资产对，用于支持自动化交易。

**定义 1.3**（恒定乘积公式）：
AMM的核心定价机制：$x \cdot y = k$，其中$x$、$y$为资产数量，$k$为常数。

## 2. 核心定理

**定理 2.1**（价格影响定理）：
在恒定乘积AMM中，交易规模越大，价格滑点越高，关系为：
$$\text{Price Impact} = \frac{\Delta x}{x + \Delta x}$$

**定理 2.2**（无常损失定理）：
当资产价格比率偏离初始比率时，流动性提供者面临的损失为：
$$IL = 2\sqrt{\frac{p}{p_0}} - \frac{p}{p_0} - 1$$

**定理 2.3**（套利平衡定理）：
AMM价格将通过套利者的行为收敛到外部市场价格。

## 3. 应用场景

- 去中心化交易所（DEX）
- 流动性挖矿协议
- 跨链资产交换

## 4. Rust代码示例

### AMM协议实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use serde::{Serialize, Deserialize};
use rust_decimal::Decimal;
use rust_decimal_macros::dec;

// 代币结构
#[derive(Debug, Clone, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub struct Token {
    pub symbol: String,
    pub address: String,
    pub decimals: u8,
}

impl Token {
    pub fn new(symbol: String, address: String, decimals: u8) -> Self {
        Token { symbol, address, decimals }
    }
}

// 流动性池
#[derive(Debug, Clone)]
pub struct LiquidityPool {
    pub token_a: Token,
    pub token_b: Token,
    pub reserve_a: Decimal,
    pub reserve_b: Decimal,
    pub total_supply: Decimal,
    pub fee_rate: Decimal, // 交易手续费率，如0.003 (0.3%)
    pub liquidity_providers: HashMap<String, Decimal>,
}

impl LiquidityPool {
    pub fn new(token_a: Token, token_b: Token, fee_rate: Decimal) -> Self {
        LiquidityPool {
            token_a,
            token_b,
            reserve_a: Decimal::ZERO,
            reserve_b: Decimal::ZERO,
            total_supply: Decimal::ZERO,
            fee_rate,
            liquidity_providers: HashMap::new(),
        }
    }
    
    // 获取当前价格（token_a相对于token_b的价格）
    pub fn get_price(&self) -> Option<Decimal> {
        if self.reserve_a.is_zero() {
            None
        } else {
            Some(self.reserve_b / self.reserve_a)
        }
    }
    
    // 添加流动性
    pub fn add_liquidity(
        &mut self,
        provider: String,
        amount_a: Decimal,
        amount_b: Decimal,
    ) -> Result<Decimal, String> {
        if amount_a.is_zero() || amount_b.is_zero() {
            return Err("流动性数量必须大于零".to_string());
        }
        
        let liquidity_tokens = if self.total_supply.is_zero() {
            // 初次添加流动性
            (amount_a * amount_b).sqrt().ok_or("计算流动性代币失败")?
        } else {
            // 计算应添加的流动性代币
            let liquidity_a = amount_a * self.total_supply / self.reserve_a;
            let liquidity_b = amount_b * self.total_supply / self.reserve_b;
            liquidity_a.min(liquidity_b)
        };
        
        // 更新储备
        self.reserve_a += amount_a;
        self.reserve_b += amount_b;
        self.total_supply += liquidity_tokens;
        
        // 记录流动性提供者的份额
        let provider_balance = self.liquidity_providers.get(&provider).unwrap_or(&Decimal::ZERO);
        self.liquidity_providers.insert(provider, provider_balance + liquidity_tokens);
        
        Ok(liquidity_tokens)
    }
    
    // 移除流动性
    pub fn remove_liquidity(
        &mut self,
        provider: String,
        liquidity_tokens: Decimal,
    ) -> Result<(Decimal, Decimal), String> {
        if liquidity_tokens.is_zero() {
            return Err("移除数量必须大于零".to_string());
        }
        
        let provider_balance = self.liquidity_providers.get(&provider)
            .ok_or("流动性提供者不存在")?;
        
        if *provider_balance < liquidity_tokens {
            return Err("流动性代币余额不足".to_string());
        }
        
        // 计算可提取的资产数量
        let amount_a = liquidity_tokens * self.reserve_a / self.total_supply;
        let amount_b = liquidity_tokens * self.reserve_b / self.total_supply;
        
        // 更新储备
        self.reserve_a -= amount_a;
        self.reserve_b -= amount_b;
        self.total_supply -= liquidity_tokens;
        
        // 更新提供者余额
        self.liquidity_providers.insert(provider, provider_balance - liquidity_tokens);
        
        Ok((amount_a, amount_b))
    }
    
    // 计算交换输出（给定输入数量）
    pub fn get_amount_out(&self, amount_in: Decimal, token_in: &Token) -> Result<Decimal, String> {
        if amount_in.is_zero() {
            return Err("输入数量必须大于零".to_string());
        }
        
        let (reserve_in, reserve_out) = if token_in == &self.token_a {
            (self.reserve_a, self.reserve_b)
        } else if token_in == &self.token_b {
            (self.reserve_b, self.reserve_a)
        } else {
            return Err("代币不在此流动性池中".to_string());
        };
        
        if reserve_in.is_zero() || reserve_out.is_zero() {
            return Err("流动性不足".to_string());
        }
        
        // 考虑手续费的输入数量
        let amount_in_with_fee = amount_in * (Decimal::ONE - self.fee_rate);
        
        // 恒定乘积公式：(x + Δx) * (y - Δy) = x * y
        // 解得：Δy = y * Δx / (x + Δx)
        let amount_out = reserve_out * amount_in_with_fee / (reserve_in + amount_in_with_fee);
        
        Ok(amount_out)
    }
    
    // 计算交换输入（给定输出数量）
    pub fn get_amount_in(&self, amount_out: Decimal, token_out: &Token) -> Result<Decimal, String> {
        if amount_out.is_zero() {
            return Err("输出数量必须大于零".to_string());
        }
        
        let (reserve_in, reserve_out) = if token_out == &self.token_a {
            (self.reserve_b, self.reserve_a)
        } else if token_out == &self.token_b {
            (self.reserve_a, self.reserve_b)
        } else {
            return Err("代币不在此流动性池中".to_string());
        };
        
        if reserve_out <= amount_out {
            return Err("输出数量超过储备".to_string());
        }
        
        // 恒定乘积公式逆推：Δx = x * Δy / (y - Δy)
        let amount_in_with_fee = reserve_in * amount_out / (reserve_out - amount_out);
        
        // 考虑手续费
        let amount_in = amount_in_with_fee / (Decimal::ONE - self.fee_rate);
        
        Ok(amount_in)
    }
    
    // 执行交换
    pub fn swap(
        &mut self,
        amount_in: Decimal,
        min_amount_out: Decimal,
        token_in: &Token,
        trader: String,
    ) -> Result<Decimal, String> {
        let amount_out = self.get_amount_out(amount_in, token_in)?;
        
        if amount_out < min_amount_out {
            return Err("滑点超过容忍范围".to_string());
        }
        
        // 更新储备
        if token_in == &self.token_a {
            self.reserve_a += amount_in;
            self.reserve_b -= amount_out;
        } else {
            self.reserve_b += amount_in;
            self.reserve_a -= amount_out;
        }
        
        println!("交易者 {} 用 {} {} 换取 {} {}", 
                trader, amount_in, token_in.symbol, amount_out, 
                if token_in == &self.token_a { &self.token_b.symbol } else { &self.token_a.symbol });
        
        Ok(amount_out)
    }
    
    // 计算无常损失
    pub fn calculate_impermanent_loss(&self, initial_price: Decimal) -> Option<Decimal> {
        let current_price = self.get_price()?;
        let price_ratio = current_price / initial_price;
        
        // IL = 2 * sqrt(price_ratio) - price_ratio - 1
        let sqrt_ratio = price_ratio.sqrt().ok()?;
        let il = dec!(2) * sqrt_ratio - price_ratio - Decimal::ONE;
        
        Some(il)
    }
    
    // 获取流动性提供者信息
    pub fn get_provider_info(&self, provider: &str) -> Option<ProviderInfo> {
        let liquidity_tokens = self.liquidity_providers.get(provider)?;
        let share_percentage = if self.total_supply.is_zero() {
            Decimal::ZERO
        } else {
            liquidity_tokens / self.total_supply * dec!(100)
        };
        
        let amount_a = liquidity_tokens * self.reserve_a / self.total_supply;
        let amount_b = liquidity_tokens * self.reserve_b / self.total_supply;
        
        Some(ProviderInfo {
            liquidity_tokens: *liquidity_tokens,
            share_percentage,
            amount_a,
            amount_b,
        })
    }
}

#[derive(Debug)]
pub struct ProviderInfo {
    pub liquidity_tokens: Decimal,
    pub share_percentage: Decimal,
    pub amount_a: Decimal,
    pub amount_b: Decimal,
}

// AMM工厂合约
pub struct AMMFactory {
    pools: Arc<Mutex<HashMap<(Token, Token), LiquidityPool>>>,
    default_fee_rate: Decimal,
}

impl AMMFactory {
    pub fn new(default_fee_rate: Decimal) -> Self {
        AMMFactory {
            pools: Arc::new(Mutex::new(HashMap::new())),
            default_fee_rate,
        }
    }
    
    pub fn create_pool(&self, token_a: Token, token_b: Token) -> Result<(), String> {
        let mut pools = self.pools.lock().unwrap();
        
        let pool_key = if token_a.address < token_b.address {
            (token_a.clone(), token_b.clone())
        } else {
            (token_b.clone(), token_a.clone())
        };
        
        if pools.contains_key(&pool_key) {
            return Err("流动性池已存在".to_string());
        }
        
        let pool = LiquidityPool::new(token_a, token_b, self.default_fee_rate);
        pools.insert(pool_key, pool);
        
        Ok(())
    }
    
    pub fn get_pool(&self, token_a: &Token, token_b: &Token) -> Option<LiquidityPool> {
        let pools = self.pools.lock().unwrap();
        
        let pool_key = if token_a.address < token_b.address {
            (token_a.clone(), token_b.clone())
        } else {
            (token_b.clone(), token_a.clone())
        };
        
        pools.get(&pool_key).cloned()
    }
    
    pub fn get_all_pools(&self) -> Vec<LiquidityPool> {
        let pools = self.pools.lock().unwrap();
        pools.values().cloned().collect()
    }
}

// 路由器 - 处理多跳交换
pub struct AMMRouter {
    factory: Arc<AMMFactory>,
}

impl AMMRouter {
    pub fn new(factory: Arc<AMMFactory>) -> Self {
        AMMRouter { factory }
    }
    
    // 查找最优交换路径
    pub fn find_best_path(&self, token_in: &Token, token_out: &Token, amount_in: Decimal) -> Option<Vec<Token>> {
        // 简化实现：直接交换或通过一个中间代币
        if let Some(_) = self.factory.get_pool(token_in, token_out) {
            return Some(vec![token_in.clone(), token_out.clone()]);
        }
        
        // 尝试通过其他代币作为中介
        let all_pools = self.factory.get_all_pools();
        for pool in all_pools {
            if (pool.token_a == *token_in || pool.token_b == *token_in) &&
               (pool.token_a == *token_out || pool.token_b == *token_out) {
                continue; // 跳过直接池
            }
            
            let intermediate = if pool.token_a == *token_in {
                &pool.token_b
            } else if pool.token_b == *token_in {
                &pool.token_a
            } else {
                continue;
            };
            
            if self.factory.get_pool(intermediate, token_out).is_some() {
                return Some(vec![token_in.clone(), intermediate.clone(), token_out.clone()]);
            }
        }
        
        None
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建代币
    let usdc = Token::new("USDC".to_string(), "0x1234...".to_string(), 6);
    let eth = Token::new("ETH".to_string(), "0x5678...".to_string(), 18);
    
    // 创建AMM工厂
    let factory = Arc::new(AMMFactory::new(dec!(0.003))); // 0.3% 手续费
    
    // 创建流动性池
    factory.create_pool(usdc.clone(), eth.clone())?;
    
    // 获取流动性池并添加初始流动性
    if let Some(mut pool) = factory.get_pool(&usdc, &eth) {
        // Alice 添加初始流动性：1000 USDC + 0.5 ETH （价格 1 ETH = 2000 USDC）
        let liquidity_tokens = pool.add_liquidity(
            "alice".to_string(),
            dec!(1000), // 1000 USDC
            dec!(0.5),  // 0.5 ETH
        )?;
        
        println!("Alice 获得流动性代币: {}", liquidity_tokens);
        println!("当前 ETH 价格: {} USDC", pool.get_price().unwrap());
        
        // Bob 进行交换：用 100 USDC 买 ETH
        let usdc_amount = dec!(100);
        let min_eth_out = dec!(0.045); // 最少期望得到的 ETH
        
        let eth_received = pool.swap(
            usdc_amount,
            min_eth_out,
            &usdc,
            "bob".to_string(),
        )?;
        
        println!("Bob 用 {} USDC 换取 {} ETH", usdc_amount, eth_received);
        println!("交换后 ETH 价格: {} USDC", pool.get_price().unwrap());
        
        // 计算 Alice 的无常损失
        let initial_price = dec!(2000); // 初始价格 1 ETH = 2000 USDC
        if let Some(il) = pool.calculate_impermanent_loss(initial_price) {
            println!("Alice 的无常损失: {:.4}%", il * dec!(100));
        }
        
        // 显示 Alice 的流动性信息
        if let Some(info) = pool.get_provider_info("alice") {
            println!("Alice 的流动性信息:");
            println!("  流动性代币: {}", info.liquidity_tokens);
            println!("  池子份额: {:.2}%", info.share_percentage);
            println!("  USDC 数量: {}", info.amount_a);
            println!("  ETH 数量: {}", info.amount_b);
        }
        
        // Carol 也添加流动性
        let carol_liquidity = pool.add_liquidity(
            "carol".to_string(),
            dec!(500), // 500 USDC
            dec!(0.24), // 约 0.24 ETH (按当前价格)
        )?;
        
        println!("Carol 获得流动性代币: {}", carol_liquidity);
        
        // 显示池子总体状态
        println!("\n池子状态:");
        println!("USDC 储备: {}", pool.reserve_a);
        println!("ETH 储备: {}", pool.reserve_b);
        println!("总流动性代币: {}", pool.total_supply);
        println!("当前价格: {} USDC per ETH", pool.get_price().unwrap());
    }
    
    Ok(())
}
```

## 相关链接

- [借贷协议](02_Lending_Protocols.md)
- [收益农场](03_Yield_Farming.md)
- [密码学基础](../../01_Theoretical_Foundations/02_Cryptographic_Foundations/)
- [智能合约](../../02_Core_Technologies/02_Smart_Contracts/)
- [DeFi总览](../)
- [应用生态总览](../../)

---

*自动做市商为DeFi生态提供高效、去中心化的流动性解决方案。*
