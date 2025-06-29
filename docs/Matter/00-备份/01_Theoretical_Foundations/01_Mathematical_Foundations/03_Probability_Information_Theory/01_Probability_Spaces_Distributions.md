# 概率空间与分布 (Probability Spaces & Distributions)

## 概述

概率空间与分布是概率论的基础，为Web3系统中的安全性分析、共识机制、经济模型等提供理论支撑。

## 1. 概率空间定义

**定义 1.1**（概率空间）：
概率空间是三元组 $(\Omega, \mathcal{F}, P)$，其中：

- $\Omega$：样本空间，所有可能结果的集合
- $\mathcal{F}$：事件的σ-代数
- $P$：概率测度，$P: \mathcal{F} \to [0,1]$，满足 $P(\Omega) = 1$

**定义 1.2**（随机变量）：
随机变量是从样本空间到实数集的可测函数 $X: \Omega \to \mathbb{R}$。

**定义 1.3**（分布函数）：
$F_X(x) = P(X \leq x)$，描述随机变量的概率分布。

## 2. 常见概率分布

- **离散分布**：伯努利分布、二项分布、泊松分布
- **连续分布**：均匀分布、正态分布、指数分布

**定义 2.1**（伯努利分布）：
$P(X=1) = p,\ P(X=0) = 1-p$

**定义 2.2**（正态分布）：
$X \sim N(\mu, \sigma^2)$，概率密度 $f(x) = \frac{1}{\sqrt{2\pi\sigma^2}} e^{-\frac{(x-\mu)^2}{2\sigma^2}}$

## 3. 期望与方差

**定义 3.1**（期望）：
$E[X] = \sum_x xP(X=x)$（离散），$E[X] = \int x f(x) dx$（连续）

**定义 3.2**（方差）：
$Var(X) = E[(X-E[X])^2]$

## 4. 应用场景

- 区块链共识概率分析（如拜占庭容错概率）
- 随机数生成与安全协议
- 经济模型中的风险评估
- 区块链激励机制的期望收益分析

## 5. Rust代码示例

### 伯努利分布与采样

```rust
use rand::Rng;

fn bernoulli_trial(p: f64) -> u8 {
    let mut rng = rand::thread_rng();
    if rng.gen::<f64>() < p { 1 } else { 0 }
}

fn main() {
    let p = 0.7;
    let mut count = 0;
    for _ in 0..1000 {
        count += bernoulli_trial(p) as u32;
    }
    println!("1000次伯努利试验中1的次数: {}", count);
}
```

## 相关链接

- [熵与互信息](02_Entropy_Mutual_Information.md)
- [概率论与信息论总览](../03_Probability_Information_Theory/)
- [数学基础](../)

---

*概率空间与分布为Web3系统的安全性、激励机制和风险建模提供理论基础。*
