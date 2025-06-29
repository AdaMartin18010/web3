# 优化理论 (Optimization Theory)

## 概述

优化理论研究如何在约束条件下寻找最优解，是Web3系统中资源分配、经济激励、网络调度等问题的理论基础。

## 1. 优化问题定义

**定义 1.1**（优化问题）：
给定目标函数 $f(x)$ 和约束集合 $C$，求 $x^* = \arg\min_{x \in C} f(x)$。

- **无约束优化**：$C = \mathbb{R}^n$
- **有约束优化**：$C$ 由等式/不等式约束定义

**定义 1.2**（凸优化）：
若 $f(x)$ 为凸函数，$C$ 为凸集，则为凸优化问题。

## 2. 重要定理与方法

**定理 2.1**（KKT条件）：
若 $f(x)$ 和约束均可微，$x^*$ 为极值点，则存在拉格朗日乘子使得KKT条件成立。

**定理 2.2**（强对偶性）：
对于凸优化问题，原问题与对偶问题的最优值相等。

**方法 2.1**（梯度下降）：
$$x_{k+1} = x_k - \eta \nabla f(x_k)$$

- $\eta$ 为步长，$\nabla f(x_k)$ 为梯度

## 3. 应用场景

- 区块链网络的资源调度与负载均衡
- DeFi协议的最优资产配置
- 共识机制的激励参数优化
- 零知识证明电路的约束优化

## 4. Rust代码示例

### 梯度下降法求解二次函数最小值

```rust
fn gradient_descent<F, G>(mut x: f64, grad: G, lr: f64, tol: f64, max_iter: usize) -> f64
where
    G: Fn(f64) -> f64,
{
    for _ in 0..max_iter {
        let g = grad(x);
        if g.abs() < tol {
            break;
        }
        x -= lr * g;
    }
    x
}

fn main() {
    // 目标函数: f(x) = (x-3)^2
    let grad = |x: f64| 2.0 * (x - 3.0);
    let x_min = gradient_descent(0.0, grad, 0.1, 1e-6, 1000);
    println!("最小值点: {}", x_min);
}
```

## 相关链接

- [线性代数](../02_Linear_Algebra/)
- [概率论与信息论](../03_Probability_Information_Theory/)
- [数学基础总览](../)

---

*优化理论为Web3系统的资源分配、经济激励和协议设计提供理论工具。*
