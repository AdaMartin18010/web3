# DeFi架构：形式化金融协议与风险模型

## 目录

1. [引言：DeFi的形式化基础](#1-引言defi的形式化基础)
2. [借贷协议架构](#2-借贷协议架构)
3. [去中心化交易所](#3-去中心化交易所)
4. [流动性挖矿机制](#4-流动性挖矿机制)
5. [风险模型与定价](#5-风险模型与定价)
6. [治理机制](#6-治理机制)
7. [跨链DeFi](#7-跨链defi)
8. [收益优化策略](#8-收益优化策略)
9. [风险管理框架](#9-风险管理框架)
10. [实现架构](#10-实现架构)
11. [结论与展望](#11-结论与展望)

## 1. 引言：DeFi的形式化基础

### 1.1 DeFi系统定义

**定义 1.1.1** (DeFi系统) DeFi系统是一个六元组 $\mathcal{D} = (A, P, R, M, G, S)$，其中：

- $A$ 是资产集合，$A = \{a_1, a_2, \ldots, a_n\}$
- $P$ 是协议集合，$P = \{p_1, p_2, \ldots, p_m\}$
- $R$ 是风险模型，$R: A \times P \rightarrow \mathbb{R}^+$
- $M$ 是市场模型，$M: A \times A \rightarrow \mathbb{R}^+$
- $G$ 是治理机制，$G: U \times D \rightarrow \mathbb{B}$
- $S$ 是状态空间，$S = \mathbb{S}^n$

**定义 1.1.2** (DeFi协议) DeFi协议是一个四元组 $\mathcal{P} = (I, O, F, C)$，其中：

- $I$ 是输入接口
- $O$ 是输出接口
- $F$ 是功能函数，$F: I \rightarrow O$
- $C$ 是约束条件，$C: I \rightarrow \mathbb{B}$

**定理 1.1.1** (DeFi可组合性) DeFi协议的可组合性使得复杂金融产品可以通过简单协议组合构建。

**证明**：
通过函数组合：

1. 设协议 $P_1: I_1 \rightarrow O_1$ 和 $P_2: I_2 \rightarrow O_2$
2. 如果 $O_1 \subseteq I_2$，则可以组合为 $P_2 \circ P_1: I_1 \rightarrow O_2$
3. 因此可以构建复杂协议 ■

### 1.2 金融数学基础

**定义 1.2.1** (现值) 现值是未来现金流的当前价值：

```latex
\begin{align}
PV = \sum_{t=1}^{T} \frac{CF_t}{(1 + r)^t}
\end{align}
```

其中 $CF_t$ 是第 $t$ 期的现金流，$r$ 是折现率。

**定义 1.2.2** (收益率) 收益率是投资回报率：

```latex
\begin{align}
R = \frac{P_1 - P_0}{P_0}
\end{align}
```

其中 $P_0$ 是初始价格，$P_1$ 是最终价格。

**定理 1.2.1** (无套利原理) 在有效市场中，不存在无风险套利机会。

**证明**：
通过反证法：

1. 假设存在无风险套利机会
2. 市场参与者会利用此机会
3. 套利机会会迅速消失
4. 因此不存在无风险套利 ■

## 2. 借贷协议架构

### 2.1 借贷模型

**定义 2.1.1** (借贷协议) 借贷协议是一个五元组 $\mathcal{L} = (B, L, C, R, I)$，其中：

- $B$ 是借款人集合
- $L$ 是贷款人集合
- $C$ 是抵押品集合
- $R$ 是利率函数，$R: C \rightarrow \mathbb{R}^+$
- $I$ 是清算机制，$I: B \times C \rightarrow \mathbb{B}$

**定义 2.1.2** (抵押率) 抵押率是抵押品价值与贷款价值的比率：

```latex
\begin{align}
\text{Collateral Ratio} = \frac{\text{Collateral Value}}{\text{Loan Value}}
\end{align}
```

**定理 2.1.1** (清算条件) 当抵押率低于清算阈值时，贷款将被清算。

**证明**：
通过风险控制：

1. 抵押率反映借款人信用风险
2. 低抵押率增加违约风险
3. 清算机制保护贷款人利益
4. 因此需要清算机制 ■

### 2.2 利率模型

**定义 2.2.1** (利率函数) 利率函数基于供需关系：

```latex
\begin{align}
r = f(\text{utilization rate}) = r_0 + k \cdot u
\end{align}
```

其中 $r_0$ 是基础利率，$k$ 是利率系数，$u$ 是利用率。

**定义 2.2.2** (利用率) 利用率是已借出资金与总资金的比率：

```latex
\begin{align}
u = \frac{\text{Total Borrowed}}{\text{Total Supplied}}
\end{align}
```

**定理 2.2.1** (利率均衡) 在均衡状态下，借贷利率等于资金成本。

**证明**：
通过供需平衡：

1. 当利率高于资金成本时，供应增加
2. 当利率低于资金成本时，供应减少
3. 均衡时利率等于资金成本 ■

### 2.3 清算机制

**定义 2.3.1** (清算函数) 清算函数计算清算金额：

```latex
\begin{align}
\text{Liquidation Amount} = \min(\text{Debt}, \text{Collateral} \cdot \text{Liquidation Ratio})
\end{align}
```

**定义 2.3.2** (清算奖励) 清算奖励是清算人获得的激励：

```latex
\begin{align}
\text{Liquidation Bonus} = \text{Liquidation Amount} \cdot \text{Bonus Rate}
\end{align}
```

**定理 2.3.1** (清算激励相容性) 清算奖励确保清算机制的有效性。

**证明**：
通过激励分析：

1. 清算需要成本（Gas费用、时间）
2. 清算奖励补偿清算成本
3. 合理奖励确保清算发生
4. 因此清算机制有效 ■

## 3. 去中心化交易所

### 3.1 AMM模型

**定义 3.1.1** (自动做市商) AMM是一个三元组 $\mathcal{A} = (P, F, S)$，其中：

- $P$ 是价格函数，$P: \mathbb{R}^+ \times \mathbb{R}^+ \rightarrow \mathbb{R}^+$
- $F$ 是费用函数，$F: \mathbb{R}^+ \rightarrow \mathbb{R}^+$
- $S$ 是滑点函数，$S: \mathbb{R}^+ \rightarrow \mathbb{R}^+$

**定义 3.1.2** (恒定乘积公式) 恒定乘积公式：

```latex
\begin{align}
x \cdot y = k
\end{align}
```

其中 $x$ 和 $y$ 是池中资产数量，$k$ 是常数。

**定理 3.1.1** (价格影响) 交易规模越大，价格影响越大。

**证明**：
通过微分分析：

1. 价格 $p = \frac{y}{x}$
2. 交易 $\Delta x$ 后，新价格 $p' = \frac{y - \Delta y}{x + \Delta x}$
3. 价格变化 $\Delta p = p' - p = -\frac{\Delta y}{x + \Delta x}$
4. 因此价格影响与交易规模成正比 ■

### 3.2 流动性提供

**定义 3.2.1** (流动性提供) 流动性提供者向池子提供资产：

```latex
\begin{align}
\text{LP Shares} = \frac{\text{Provided Liquidity}}{\text{Total Liquidity}}
\end{align}
```

**定义 3.2.2** (无常损失) 无常损失是LP相对于持有资产的价值损失：

```latex
\begin{align}
\text{Impermanent Loss} = \frac{2\sqrt{p_1/p_0}}{1 + p_1/p_0} - 1
\end{align}
```

其中 $p_0$ 是初始价格比率，$p_1$ 是当前价格比率。

**定理 3.2.1** (无常损失性质) 无常损失在价格变化时总是负值。

**证明**：
通过数学分析：

1. 设 $r = p_1/p_0$
2. 无常损失函数 $f(r) = \frac{2\sqrt{r}}{1 + r} - 1$
3. 当 $r \neq 1$ 时，$f(r) < 0$
4. 因此无常损失为负值 ■

## 4. 流动性挖矿机制

### 4.1 挖矿模型

**定义 4.1.1** (流动性挖矿) 流动性挖矿是一个四元组 $\mathcal{M} = (P, R, T, V)$，其中：

- $P$ 是池子集合
- $R$ 是奖励函数，$R: P \times T \rightarrow \mathbb{R}^+$
- $T$ 是时间函数，$T: \mathbb{R}^+ \rightarrow \mathbb{R}^+$
- $V$ 是价值函数，$V: P \rightarrow \mathbb{R}^+$

**定义 4.1.2** (奖励分配) 奖励分配基于流动性提供：

```latex
\begin{align}
\text{Reward} = \frac{\text{User Liquidity}}{\text{Total Liquidity}} \cdot \text{Total Reward}
\end{align}
```

**定理 4.1.1** (挖矿激励) 流动性挖矿激励用户提供流动性。

**证明**：
通过激励分析：

1. 挖矿奖励提供额外收益
2. 奖励与流动性成正比
3. 用户有动力提供流动性
4. 因此挖矿激励有效 ■

### 4.2 收益优化

**定义 4.2.1** (收益函数) 总收益是交易费用和挖矿奖励之和：

```latex
\begin{align}
\text{Total Yield} = \text{Trading Fees} + \text{Mining Rewards} - \text{Impermanent Loss}
\end{align}
```

**定义 4.2.2** (年化收益率) 年化收益率：

```latex
\begin{align}
\text{APY} = \left(1 + \frac{\text{Total Yield}}{\text{Initial Investment}}\right)^{365/t} - 1
\end{align}
```

其中 $t$ 是投资天数。

**定理 4.2.1** (收益最大化) 在均衡状态下，所有池子的年化收益率相等。

**证明**：
通过套利分析：

1. 如果某个池子收益率更高
2. 资金会流向该池子
3. 收益率会下降
4. 最终达到均衡 ■

## 5. 风险模型与定价

### 5.1 风险度量

**定义 5.1.1** (风险度量) 风险度量是一个函数 $\mathcal{R}: A \rightarrow \mathbb{R}^+$，满足：

1. **单调性**: $A_1 \subseteq A_2 \implies \mathcal{R}(A_1) \leq \mathcal{R}(A_2)$
2. **次可加性**: $\mathcal{R}(A_1 + A_2) \leq \mathcal{R}(A_1) + \mathcal{R}(A_2)$
3. **正齐次性**: $\mathcal{R}(\lambda A) = \lambda \mathcal{R}(A)$
4. **平移不变性**: $\mathcal{R}(A + c) = \mathcal{R}(A)$

**定义 5.1.2** (VaR) 风险价值是在给定置信水平下的最大损失：

```latex
\begin{align}
\text{VaR}_\alpha = \inf\{l \in \mathbb{R}: P(L \leq l) \geq \alpha\}
\end{align}
```

其中 $L$ 是损失随机变量，$\alpha$ 是置信水平。

**定理 5.1.1** (VaR性质) VaR满足单调性和平移不变性。

**证明**：
通过概率论：

1. 单调性：损失增加时VaR增加
2. 平移不变性：常数偏移不影响VaR
3. 因此VaR满足这些性质 ■

### 5.2 定价模型

**定义 5.2.1** (期权定价) 期权价格基于风险中性定价：

```latex
\begin{align}
C = e^{-rT} \mathbb{E}^Q[\max(S_T - K, 0)]
\end{align}
```

其中 $C$ 是期权价格，$S_T$ 是标的资产价格，$K$ 是执行价格。

**定义 5.2.2** (DeFi期权) DeFi期权定价考虑流动性成本：

```latex
\begin{align}
C_{DeFi} = C + \text{Liquidity Cost} + \text{Impermanent Loss}
\end{align}
```

**定理 5.2.1** (定价一致性) 无套利定价确保价格一致性。

**证明**：
通过无套利原理：

1. 如果价格不一致
2. 存在套利机会
3. 套利行为使价格收敛
4. 因此价格一致 ■

## 6. 治理机制

### 6.1 治理模型

**定义 6.1.1** (治理系统) 治理系统是一个四元组 $\mathcal{G} = (T, V, P, E)$，其中：

- $T$ 是代币持有者集合
- $V$ 是投票权重函数，$V: T \rightarrow \mathbb{R}^+$
- $P$ 是提案集合
- $E$ 是执行机制，$E: P \times V \rightarrow \mathbb{B}$

**定义 6.1.2** (投票机制) 投票权重基于代币持有量：

```latex
\begin{align}
\text{Voting Power} = \text{Token Balance} \cdot \text{Lock Time Multiplier}
\end{align}
```

**定理 6.1.1** (治理有效性) 代币加权投票确保治理有效性。

**证明**：
通过激励分析：

1. 代币持有者有利益激励
2. 投票权重反映利益大小
3. 长期持有者更关心项目
4. 因此治理有效 ■

### 6.2 提案执行

**定义 6.2.1** (提案流程) 提案执行需要满足条件：

```latex
\begin{align}
\text{Execute} \iff \text{Quorum} \land \text{Majority} \land \text{Timelock}
\end{align}
```

**定义 6.2.2** (时间锁) 时间锁防止恶意提案：

```latex
\begin{align}
\text{Timelock} = \text{Proposal Time} + \text{Delay Period}
\end{align}
```

**定理 6.2.1** (时间锁安全性) 时间锁提供安全保护。

**证明**：
通过安全分析：

1. 时间锁给社区反应时间
2. 恶意提案可以被阻止
3. 紧急情况有快速通道
4. 因此提供安全保护 ■

## 7. 跨链DeFi

### 7.1 跨链架构

**定义 7.1.1** (跨链DeFi) 跨链DeFi是一个三元组 $\mathcal{X} = (C, B, P)$，其中：

- $C$ 是链集合
- $B$ 是桥接机制，$B: C \times C \rightarrow \text{Transfer}$
- $P$ 是协议集合，$P: C \rightarrow \text{Protocol}$

**定义 7.1.2** (跨链资产) 跨链资产在不同链上保持价值：

```latex
\begin{align}
\text{CrossChain Value} = \text{Original Value} - \text{Bridge Fee} - \text{Gas Cost}
\end{align}
```

**定理 7.1.1** (跨链效率) 跨链操作存在成本。

**证明**：
通过成本分析：

1. 桥接需要验证成本
2. 跨链需要Gas费用
3. 时间成本影响价值
4. 因此存在成本 ■

### 7.2 流动性聚合

**定义 7.2.1** (流动性聚合) 聚合器寻找最优路径：

```latex
\begin{align}
\text{Optimal Path} = \arg\min_{\text{path}} \sum_{i=1}^{n} \text{Cost}_i
\end{align}
```

**定义 7.2.2** (套利机会) 套利机会存在于价格差异：

```latex
\begin{align}
\text{Arbitrage} = \text{Price}_A - \text{Price}_B - \text{Transaction Cost}
\end{align}
```

**定理 7.2.1** (套利效率) 套利行为消除价格差异。

**证明**：
通过市场效率：

1. 套利者利用价格差异
2. 套利行为影响价格
3. 价格差异逐渐消失
4. 因此套利有效 ■

## 8. 收益优化策略

### 8.1 策略框架

**定义 8.1.1** (收益策略) 收益策略是一个四元组 $\mathcal{Y} = (A, R, C, O)$，其中：

- $A$ 是资产配置，$A: \text{Capital} \rightarrow \text{Allocation}$
- $R$ 是风险评估，$R: A \rightarrow \mathbb{R}^+$
- $C$ 是成本函数，$C: A \rightarrow \mathbb{R}^+$
- $O$ 是优化目标，$O: A \rightarrow \mathbb{R}$

**定义 8.1.2** (夏普比率) 风险调整后收益：

```latex
\begin{align}
\text{Sharpe Ratio} = \frac{\text{Expected Return} - \text{Risk Free Rate}}{\text{Volatility}}
\end{align}
```

**定理 8.1.1** (最优配置) 最优配置最大化夏普比率。

**证明**：
通过优化理论：

1. 夏普比率衡量风险调整收益
2. 最优配置在有效前沿上
3. 最大化夏普比率
4. 因此是最优的 ■

### 8.2 动态调整

**定义 8.2.1** (再平衡策略) 定期再平衡维持目标配置：

```latex
\begin{align}
\text{Rebalance} = \text{Target Allocation} - \text{Current Allocation}
\end{align}
```

**定义 8.2.2** (止损机制) 止损保护资本：

```latex
\begin{align}
\text{Stop Loss} = \text{Entry Price} \cdot (1 - \text{Loss Threshold})
\end{align}
```

**定理 8.2.1** (再平衡效果) 再平衡提高长期收益。

**证明**：
通过实证分析：

1. 再平衡控制风险
2. 定期调整优化配置
3. 长期收益更稳定
4. 因此提高收益 ■

## 9. 风险管理框架

### 9.1 风险分类

**定义 9.1.1** (风险类型) DeFi风险分类：

$$\text{RiskTypes} = \{\text{Smart Contract}, \text{Market}, \text{Liquidity}, \text{Governance}, \text{Regulatory}\}$$

**定义 9.1.2** (风险矩阵) 风险矩阵评估影响和概率：

```latex
\begin{align}
\text{Risk Score} = \text{Impact} \times \text{Probability}
\end{align}
```

**定理 9.1.1** (风险分散) 分散投资降低总风险。

**证明**：
通过投资组合理论：

1. 不同资产相关性低
2. 分散降低组合波动
3. 总风险小于单个风险
4. 因此降低风险 ■

### 9.2 风险监控

**定义 9.2.1** (监控指标) 关键风险指标：

1. **TVL变化**: $\text{TVL Change} = \frac{\text{TVL}_t - \text{TVL}_{t-1}}{\text{TVL}_{t-1}}$
2. **价格波动**: $\text{Volatility} = \sqrt{\frac{1}{n-1}\sum_{i=1}^{n}(r_i - \bar{r})^2}$
3. **流动性比率**: $\text{Liquidity Ratio} = \frac{\text{Liquid Assets}}{\text{Total Assets}}$

**定义 9.2.2** (预警机制) 风险预警触发条件：

```latex
\begin{align}
\text{Alert} = \text{Indicator} > \text{Threshold}
\end{align}
```

**定理 9.2.1** (监控有效性) 实时监控提高风险响应。

**证明**：
通过响应时间分析：

1. 实时监控快速发现问题
2. 早期预警提供反应时间
3. 快速响应减少损失
4. 因此提高有效性 ■

## 10. 实现架构

### 10.1 系统架构

**定义 10.1.1** (DeFi架构) DeFi系统架构是一个五元组 $\mathcal{A} = (L, P, S, M, I)$，其中：

- $L$ 是逻辑层 (Logic Layer)
- $P$ 是协议层 (Protocol Layer)
- $S$ 是存储层 (Storage Layer)
- $M$ 是监控层 (Monitoring Layer)
- $I$ 是接口层 (Interface Layer)

**DeFi系统实现**：

```rust
pub struct DeFiSystem {
    lending_protocol: Arc<LendingProtocol>,
    dex_protocol: Arc<DEXProtocol>,
    yield_farming: Arc<YieldFarming>,
    risk_manager: Arc<RiskManager>,
    governance: Arc<Governance>,
}

impl DeFiSystem {
    pub async fn execute_strategy(&self, strategy: &InvestmentStrategy) -> Result<StrategyResult, DeFiError> {
        // 风险评估
        let risk_assessment = self.risk_manager.assess_risk(&strategy).await?;
        
        if risk_assessment.risk_level > RiskLevel::High {
            return Err(DeFiError::RiskTooHigh);
        }
        
        // 执行策略
        let mut results = Vec::new();
        
        for action in &strategy.actions {
            let result = match action.action_type {
                ActionType::Lend => self.lending_protocol.lend(&action.params).await,
                ActionType::Swap => self.dex_protocol.swap(&action.params).await,
                ActionType::Farm => self.yield_farming.farm(&action.params).await,
                ActionType::Stake => self.governance.stake(&action.params).await,
            }?;
            
            results.push(result);
        }
        
        Ok(StrategyResult {
            actions: results,
            total_return: self.calculate_total_return(&results),
            risk_metrics: risk_assessment,
        })
    }
}

pub struct LendingProtocol {
    markets: HashMap<Asset, LendingMarket>,
    oracle: Arc<PriceOracle>,
    liquidation_engine: Arc<LiquidationEngine>,
}

impl LendingProtocol {
    pub async fn lend(&self, params: &LendParams) -> Result<LendResult, LendingError> {
        let market = self.markets.get(&params.asset)
            .ok_or(LendingError::MarketNotFound)?;
        
        // 检查抵押率
        let collateral_value = self.oracle.get_price(&params.collateral_asset) * params.collateral_amount;
        let loan_value = self.oracle.get_price(&params.asset) * params.loan_amount;
        let collateral_ratio = collateral_value / loan_value;
        
        if collateral_ratio < market.min_collateral_ratio {
            return Err(LendingError::InsufficientCollateral);
        }
        
        // 执行借贷
        let loan = Loan {
            borrower: params.borrower,
            asset: params.asset.clone(),
            amount: params.loan_amount,
            collateral_asset: params.collateral_asset.clone(),
            collateral_amount: params.collateral_amount,
            interest_rate: market.get_interest_rate().await?,
            timestamp: SystemTime::now(),
        };
        
        Ok(LendResult {
            loan,
            collateral_ratio,
            liquidation_price: self.calculate_liquidation_price(&loan),
        })
    }
}

pub struct DEXProtocol {
    pools: HashMap<AssetPair, LiquidityPool>,
    fee_collector: Arc<FeeCollector>,
    price_impact_calculator: Arc<PriceImpactCalculator>,
}

impl DEXProtocol {
    pub async fn swap(&self, params: &SwapParams) -> Result<SwapResult, DEXError> {
        let pool = self.pools.get(&params.pair)
            .ok_or(DEXError::PoolNotFound)?;
        
        // 计算价格影响
        let price_impact = self.price_impact_calculator.calculate(
            &pool,
            params.amount_in,
            params.amount_out_min,
        ).await?;
        
        if price_impact > params.max_price_impact {
            return Err(DEXError::PriceImpactTooHigh);
        }
        
        // 执行交换
        let swap_result = pool.swap(params.amount_in, params.amount_out_min).await?;
        
        // 收集费用
        self.fee_collector.collect_fees(&swap_result).await?;
        
        Ok(swap_result)
    }
}

pub struct YieldFarming {
    farms: HashMap<FarmId, Farm>,
    reward_distributor: Arc<RewardDistributor>,
    staking_manager: Arc<StakingManager>,
}

impl YieldFarming {
    pub async fn farm(&self, params: &FarmParams) -> Result<FarmResult, FarmingError> {
        let farm = self.farms.get(&params.farm_id)
            .ok_or(FarmingError::FarmNotFound)?;
        
        // 质押资产
        let staking_result = self.staking_manager.stake(
            &params.asset,
            params.amount,
            &params.farm_id,
        ).await?;
        
        // 开始挖矿
        let mining_result = farm.start_mining(&staking_result.staking_position).await?;
        
        // 计算预期收益
        let expected_rewards = self.calculate_expected_rewards(
            &farm,
            params.amount,
            params.duration,
        ).await?;
        
        Ok(FarmResult {
            staking_position: staking_result.staking_position,
            mining_position: mining_result.mining_position,
            expected_rewards,
            apy: farm.get_apy().await?,
        })
    }
}
```

**定理 10.1.1** (架构完整性) 完整DeFi架构提供全面功能。

**证明** 通过功能分析：

1. 逻辑层提供业务逻辑
2. 协议层提供标准接口
3. 存储层提供数据持久化
4. 监控层提供风险控制
5. 接口层提供用户交互
6. 因此提供全面功能

## 11. 结论与展望

### 11.1 DeFi发展总结

本文通过形式化方法分析了DeFi架构的各个方面，主要发现包括：

1. **可组合性**: DeFi协议的可组合性创造了无限可能
2. **风险复杂性**: DeFi风险需要多层次管理
3. **收益优化**: 动态策略优化提高收益
4. **治理重要性**: 有效治理确保协议发展
5. **跨链趋势**: 跨链DeFi是未来发展重点

### 11.2 技术趋势

当前DeFi技术发展趋势包括：

1. **Layer 2扩展**: 提高交易吞吐量和降低成本
2. **跨链互操作**: 实现资产和数据的跨链流动
3. **MEV保护**: 防止最大可提取价值攻击
4. **隐私增强**: 保护用户交易隐私
5. **AI集成**: 智能策略优化和风险管理

### 11.3 未来展望

DeFi的未来发展方向：

1. **机构采用**: 更多机构投资者进入DeFi
2. **监管合规**: 建立合规的DeFi生态系统
3. **用户体验**: 简化用户界面和操作流程
4. **安全性提升**: 更强的安全机制和保险
5. **可持续发展**: 长期可持续的经济模型

### 11.4 实践建议

基于本文分析，对DeFi参与者的建议：

1. **风险管理**: 建立完善的风险管理体系
2. **策略优化**: 根据市场变化调整策略
3. **技术理解**: 深入理解协议机制
4. **社区参与**: 积极参与治理和社区建设
5. **持续学习**: 保持对新技术的学习

---

**参考文献**:

1. Buterin, V. (2014). Ethereum: A next-generation smart contract and decentralized application platform.
2. Adams, H., et al. (2020). Uniswap v2 Core.
3. Leshner, R., & Hayes, G. (2019). Compound: The Money Market Protocol.
4. Aave Team. (2020). Aave: A Decentralized Non-Custodial Liquidity Protocol.
5. Curve Finance. (2020). Curve: AMM for Stablecoins.
6. Yearn Finance. (2020). Yearn: DeFi Yield Aggregator.
7. Balancer Labs. (2020). Balancer: A Non-Custodial Portfolio Manager.
8. Synthetix Team. (2019). Synthetix: Decentralized Synthetic Assets.
