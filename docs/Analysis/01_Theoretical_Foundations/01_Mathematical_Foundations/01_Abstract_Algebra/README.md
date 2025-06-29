# 抽象代数 (Abstract Algebra)

## 概述

抽象代数研究代数结构如群、环、域，是Web3密码学、分布式系统、零知识证明等理论的基础。

## 1. 群、环、域的定义

**定义 1.1**（群）：
集合 $G$ 配合二元运算 $\cdot$，满足封闭性、结合性、单位元、逆元。

**定义 1.2**（环）：
集合 $R$ 配合加法和乘法，满足加法为阿贝尔群，乘法结合律，分配律。

**定义 1.3**（域）：
环 $F$ 使得 $F^* = F \setminus \{0\}$ 在乘法下为群。

## 2. 同态与同构

**定义 2.1**（同态）：
$f: G \to H$，$f(xy) = f(x)f(y)$。

**定义 2.2**（同构）：
双射同态。

## 3. 多项式与有限域

**定义 3.1**（多项式环）：
$F[x]$ 为域 $F$ 上的多项式集合。

**定义 3.2**（有限域）：
元素个数为 $p^n$ 的域，$p$ 为素数。

**定理 3.1**（有限域存在唯一性）：
每个素数幂 $p^n$ 存在唯一有限域 $\mathbb{F}_{p^n}$。

## 4. 应用场景

- 椭圆曲线密码学（ECC）
- 区块链哈希函数与Merkle树
- 零知识证明中的多项式承诺
- 分布式系统的纠删码与容错

## 5. Rust代码示例

### 有限域上的加法与乘法

```rust
const P: u32 = 17; // 素数域 F_p

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Fp(u32);

impl Fp {
    fn new(x: u32) -> Self { Fp(x % P) }
    fn add(self, rhs: Fp) -> Fp { Fp::new((self.0 + rhs.0) % P) }
    fn mul(self, rhs: Fp) -> Fp { Fp::new((self.0 * rhs.0) % P) }
}

fn main() {
    let a = Fp::new(7);
    let b = Fp::new(13);
    println!("a + b = {:?}", a.add(b));
    println!("a * b = {:?}", a.mul(b));
}
```

## 相关链接

- [线性代数](../02_Linear_Algebra/)
- [概率论与信息论](../03_Probability_Information_Theory/)
- [优化理论](../04_Optimization_Theory/)
- [数学基础总览](../)

---

*抽象代数为Web3密码学、分布式系统和形式化理论提供坚实的代数基础。*
