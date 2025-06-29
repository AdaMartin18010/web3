# 去中心化金融 (DeFi)

## 概述

去中心化金融（Decentralized Finance, DeFi）是基于区块链技术构建的开放式金融系统，通过智能合约实现传统金融服务的去中心化版本。DeFi协议具有无需许可、透明性、可组合性和全球可访问性等特点。

## 目录结构

### 1. [自动化做市商 (AMM)](01_Automated_Market_Makers.md)

流动性池、常数函数做市商、价格发现机制、无常损失分析

### 2. [借贷协议](02_Lending_Protocols.md)

抵押借贷、利率模型、流动性风险、清算机制

### 3. [去中心化交易所](03_DEX_Protocols.md)

订单簿模型、聚合器、MEV保护、跨链交易

### 4. [稳定币](04_Stablecoins.md)

算法稳定币、抵押稳定币、稳定机制、脱锚风险

### 5. [衍生品](05_Derivatives.md)

永续合约、期权定价、合成资产、风险管理

### 6. [资产管理](06_Asset_Management.md)

投资组合、收益聚合、自动化策略、风险平价

## 核心理论基础

### 自动化做市商理论

**定义 4.1.1** (常数函数做市商):
设流动性池包含两种代币 $x, y$，常数函数做市商满足不变量：
$$k = x \cdot y = \text{constant}$$

**定理 4.1.1** (价格发现):
在CFMM中，代币的边际价格为：
$$P_x = \frac{\partial y}{\partial x} = -\frac{y}{x}$$

**定理 4.1.2** (无常损失):
对于等权重池，当价格比率变化为 $r$ 时，无常损失为：
$$IL = 2\sqrt{r} - r - 1$$

### 借贷协议理论  

**定义 4.1.2** (利率模型):
利用率 $U = \frac{borrowed}{supplied}$，借贷利率为：
$$R = R_0 + \frac{U \cdot R_s}{U_{optimal}} \quad \text{当} \; U \leq U_{optimal}$$
$$R = R_0 + R_s + \frac{(U - U_{optimal}) \cdot R_{slope2}}{1 - U_{optimal}} \quad \text{当} \; U > U_{optimal}$$

**定理 4.1.3** (清算条件):
当健康因子 $HF < 1$ 时触发清算：
$$HF = \frac{\sum{Collateral_i \times LTV_i \times Price_i}}{\sum{Borrow_j \times Price_j}}$$

### 稳定币机制理论

**定义 4.1.3** (算法稳定币):
通过算法调节供应量维持锚定价格的代币，供应调节函数：
$$\Delta S = k \cdot (P_{target} - P_{market})$$

**定理 4.1.4** (稳定性条件):
系统稳定需满足：
$$\frac{d}{dt}(P - P_{target}) < 0 \quad \text{当} \; P > P_{target}$$

## 关键算法

### AMM交易算法

```rust
/// 计算AMM交易输出
pub fn calculate_swap_output(
    input_amount: u128,
    input_reserve: u128,
    output_reserve: u128,
    fee_rate: u128, // 基点，如30表示0.3%
) -> u128 {
    let input_with_fee = input_amount * (10000 - fee_rate);
    let numerator = input_with_fee * output_reserve;
    let denominator = input_reserve * 10000 + input_with_fee;
    numerator / denominator
}
```

### 利率计算算法

```rust
/// 计算分段利率
pub fn calculate_interest_rate(
    utilization: u128, // 基点表示
    base_rate: u128,
    multiplier: u128,
    jump_multiplier: u128,
    kink: u128,
) -> u128 {
    if utilization <= kink {
        base_rate + (utilization * multiplier) / 10000
    } else {
        base_rate + (kink * multiplier) / 10000 + 
        ((utilization - kink) * jump_multiplier) / 10000
    }
}
```

### 清算算法

```rust
/// 检查清算条件
pub fn check_liquidation(
    collateral_value: u128,
    borrow_value: u128,
    liquidation_threshold: u128, // 基点
) -> bool {
    let health_factor = (collateral_value * liquidation_threshold) / 
                       (borrow_value * 10000);
    health_factor < 10000 // 小于1.0
}
```

## Rust实现示例

### 完整AMM实现

```rust
use std::collections::HashMap;
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LiquidityPool {
    pub token_a: String,
    pub token_b: String,
    pub reserve_a: u128,
    pub reserve_b: u128,
    pub total_supply: u128,
    pub fee_rate: u128, // 基点
    pub k_last: u128,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LiquidityProvider {
    pub address: String,
    pub shares: u128,
}

pub struct AMM {
    pools: HashMap<String, LiquidityPool>,
    providers: HashMap<String, Vec<LiquidityProvider>>,
}

impl AMM {
    pub fn new() -> Self {
        AMM {
            pools: HashMap::new(),
            providers: HashMap::new(),
        }
    }
    
    /// 创建流动性池
    pub fn create_pool(
        &mut self,
        token_a: String,
        token_b: String,
        initial_a: u128,
        initial_b: u128,
        fee_rate: u128,
    ) -> Result<String, String> {
        let pool_id = format!("{}-{}", token_a, token_b);
        
        if self.pools.contains_key(&pool_id) {
            return Err("Pool already exists".to_string());
        }
        
        let k_last = initial_a * initial_b;
        let total_supply = (k_last as f64).sqrt() as u128;
        
        let pool = LiquidityPool {
            token_a: token_a.clone(),
            token_b: token_b.clone(),
            reserve_a: initial_a,
            reserve_b: initial_b,
            total_supply,
            fee_rate,
            k_last,
        };
        
        self.pools.insert(pool_id.clone(), pool);
        Ok(pool_id)
    }
    
    /// 执行交换
    pub fn swap(
        &mut self,
        pool_id: &str,
        token_in: &str,
        amount_in: u128,
    ) -> Result<u128, String> {
        let pool = self.pools.get_mut(pool_id)
            .ok_or("Pool not found")?;
            
        let (reserve_in, reserve_out) = if token_in == pool.token_a {
            (pool.reserve_a, pool.reserve_b)
        } else if token_in == pool.token_b {
            (pool.reserve_b, pool.reserve_a)
        } else {
            return Err("Invalid token".to_string());
        };
        
        let amount_out = calculate_swap_output(
            amount_in,
            reserve_in,
            reserve_out,
            pool.fee_rate,
        );
        
        if token_in == pool.token_a {
            pool.reserve_a += amount_in;
            pool.reserve_b -= amount_out;
        } else {
            pool.reserve_b += amount_in;
            pool.reserve_a -= amount_out;
        }
        
        pool.k_last = pool.reserve_a * pool.reserve_b;
        Ok(amount_out)
    }
}
```

## 与其他层的关系

### 理论基础依赖

- [数学基础](../../01_Theoretical_Foundations/01_Mathematical_Foundations/): 微积分、概率论、博弈论
- [密码学基础](../../01_Theoretical_Foundations/02_Cryptographic_Foundations/): 数字签名、哈希函数、零知识证明  
- [经济学理论](../../01_Theoretical_Foundations/06_Philosophical_Foundations/): 市场微观结构、拍卖理论、机制设计

### 技术实现依赖

- [智能合约](../../02_Core_Technologies/02_Smart_Contracts/): 自动执行金融逻辑
- [预言机技术](../../02_Core_Technologies/04_Cross_Chain_Technologies/): 获取外部价格数据
- [Layer2技术](../../02_Core_Technologies/03_Scalability_Technologies/): 降低交易成本和延迟

### 应用场景扩展

- [数字身份](../02_Digital_Identity/): KYC/AML合规
- [DAO治理](../03_Governance_Compliance/): 协议参数治理
- [跨链技术](../../02_Core_Technologies/04_Cross_Chain_Technologies/): 多链资产互操作

## 学习路径

### 基础阶段

1. 理解基本的金融概念和数学模型
2. 学习智能合约开发基础
3. 掌握AMM和借贷协议原理

### 进阶阶段  

1. 深入研究无常损失和MEV
2. 学习高级DeFi策略和组合
3. 理解跨链DeFi和Layer2集成

### 专家阶段

1. 设计新的DeFi协议和机制
2. 进行安全审计和形式化验证
3. 研究DeFi与传统金融的桥梁

## 参考资源

### 学术论文

- Uniswap v3 Core Paper
- Compound Protocol Whitepaper  
- MakerDAO Purple Paper
- Flash Loans: Why Flash Attacks Happen

### 开源项目

- [Uniswap Core](https://github.com/Uniswap/v3-core)
- [Compound Protocol](https://github.com/compound-finance/compound-protocol)
- [Aave Protocol](https://github.com/aave/aave-protocol)
- [OpenZeppelin Contracts](https://github.com/OpenZeppelin/openzeppelin-contracts)

---

*注：本文档遵循严格的数学标记规范，所有公式使用LaTeX格式，代码示例基于Rust语言，确保理论与实践的紧密结合。*
