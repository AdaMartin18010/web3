# 数学基础 (Mathematical Foundations)

## 概述

数学基础是Web3技术的理论基石，为密码学、分布式系统、形式化验证等提供严格的数学支撑。本目录包含Web3技术中最重要的数学理论分支。

## 目录结构

### 1.1 抽象代数与数论 (Abstract Algebra & Number Theory)

- [**群论基础**](01_Abstract_Algebra_Number_Theory/01_Group_Theory/) - 群的定义、子群、同态、循环群
- [**环论与域论**](01_Abstract_Algebra_Number_Theory/02_Ring_Field_Theory/) - 环、域、有限域、多项式环
- [**椭圆曲线理论**](01_Abstract_Algebra_Number_Theory/03_Elliptic_Curve_Theory/) - 椭圆曲线定义、点运算、离散对数问题
- [**素数理论**](01_Abstract_Algebra_Number_Theory/04_Prime_Number_Theory/) - 素数分布、素性测试、RSA安全性
- [**格理论**](01_Abstract_Algebra_Number_Theory/05_Lattice_Theory/) - 格的定义、最短向量问题、格密码学

### 1.2 线性代数与几何 (Linear Algebra & Geometry)

- [**向量空间理论**](02_Linear_Algebra_Geometry/01_Vector_Spaces/) - 向量空间、线性变换、特征值
- [**矩阵理论**](02_Linear_Algebra_Geometry/02_Matrix_Theory/) - 矩阵运算、特征分解、奇异值分解
- [**几何变换**](02_Linear_Algebra_Geometry/03_Geometric_Transformations/) - 仿射变换、投影变换、同构
- [**有限几何**](02_Linear_Algebra_Geometry/04_Finite_Geometry/) - 有限射影平面、有限几何在密码学中的应用

### 1.3 概率论与统计学 (Probability & Statistics)

- [**概率论基础**](03_Probability_Statistics/01_Probability_Theory/) - 概率空间、随机变量、期望方差
- [**随机过程**](03_Probability_Statistics/02_Stochastic_Processes/) - 马尔可夫链、随机游走、布朗运动
- [**统计推断**](03_Probability_Statistics/03_Statistical_Inference/) - 参数估计、假设检验、贝叶斯统计
- [**信息论基础**](03_Probability_Statistics/04_Information_Theory/) - 熵、互信息、信道容量

### 1.4 优化理论与复杂性 (Optimization & Complexity)

- [**凸优化理论**](04_Optimization_Complexity/01_Convex_Optimization/) - 凸集、凸函数、凸优化算法
- [**算法复杂度**](04_Optimization_Complexity/02_Algorithm_Complexity/) - 时间复杂度、空间复杂度、渐进分析
- [**NP完全性理论**](04_Optimization_Complexity/03_NP_Completeness/) - P类、NP类、NP完全问题
- [**近似算法**](04_Optimization_Complexity/04_Approximation_Algorithms/) - 近似比、随机化算法

### 1.5 信息论与编码理论 (Information Theory & Coding)

- [**信息熵理论**](05_Information_Theory_Coding/01_Information_Entropy/) - 香农熵、条件熵、相对熵
- [**信道编码**](05_Information_Theory_Coding/02_Channel_Coding/) - 纠错码、汉明码、Reed-Solomon码
- [**数据压缩**](05_Information_Theory_Coding/03_Data_Compression/) - 无损压缩、有损压缩、熵编码
- [**密码学中的信息论**](05_Information_Theory_Coding/04_Cryptographic_Information_Theory/) - 完美保密、信息泄露、侧信道攻击

## 核心概念

### 椭圆曲线密码学 (ECC)

椭圆曲线密码学是现代Web3技术的基础，其安全性基于椭圆曲线离散对数问题(ECDLP)的困难性。

**定义**：椭圆曲线是满足方程 $y^2 = x^3 + ax + b$ 的点集，其中 $4a^3 + 27b^2 \neq 0$。

**点运算**：

- 点加法：$P + Q = R$
- 标量乘法：$kP = P + P + ... + P$ (k次)

### 有限域理论

有限域在密码学中扮演重要角色，特别是素数域 $\mathbb{F}_p$ 和二元域 $\mathbb{F}_{2^n}$。

**性质**：

- 有限域的元素个数为 $p^n$，其中 $p$ 为素数
- 乘法群是循环群
- 存在本原元素

### 信息熵

信息熵是信息论的核心概念，用于量化信息的不确定性。

**定义**：$H(X) = -\sum_{i=1}^{n} p_i \log_2 p_i$

**性质**：

- $H(X) \geq 0$
- $H(X) \leq \log_2 n$ (等概率时取等号)
- 熵具有可加性

## 在Web3中的应用

### 1. 密码学应用

- **椭圆曲线数字签名算法(ECDSA)**：基于椭圆曲线离散对数问题
- **零知识证明**：利用有限域上的多项式运算
- **同态加密**：基于格理论和环论

### 2. 共识机制

- **工作量证明(PoW)**：基于哈希函数的计算复杂度
- **权益证明(PoS)**：基于概率论和博弈论
- **拜占庭容错**：基于图论和组合数学

### 3. 数据结构和算法

- **Merkle树**：基于哈希函数的树形结构
- **布隆过滤器**：基于概率论的近似数据结构
- **分布式哈希表(DHT)**：基于一致性哈希

## 学习资源

### 推荐教材

1. **抽象代数**：《Abstract Algebra》- David S. Dummit
2. **数论**：《A Course in Number Theory and Cryptography》- Neal Koblitz
3. **椭圆曲线**：《Elliptic Curves: Number Theory and Cryptography》- Lawrence C. Washington
4. **信息论**：《Elements of Information Theory》- Thomas M. Cover

### 在线资源

- [椭圆曲线密码学教程](https://cryptobook.nakov.com/asymmetric-key-ciphers/elliptic-curve-cryptography-ecc)
- [有限域计算器](https://www.wolframalpha.com/calculators/finite-field-calculator)
- [信息论可视化](https://setosa.io/ev/information-theory/)

## Rust实现示例

### 椭圆曲线点运算

```rust
use num_bigint::BigUint;
use num_traits::{One, Zero};

#[derive(Debug, Clone, PartialEq)]
pub struct ECPoint {
    pub x: BigUint,
    pub y: BigUint,
    pub is_infinity: bool,
}

impl ECPoint {
    pub fn new(x: BigUint, y: BigUint) -> Self {
        ECPoint {
            x,
            y,
            is_infinity: false,
        }
    }
    
    pub fn infinity() -> Self {
        ECPoint {
            x: BigUint::zero(),
            y: BigUint::zero(),
            is_infinity: true,
        }
    }
    
    pub fn add(&self, other: &ECPoint, p: &BigUint) -> ECPoint {
        if self.is_infinity {
            return other.clone();
        }
        if other.is_infinity {
            return self.clone();
        }
        
        // 点加法实现
        // ... 具体实现
        ECPoint::infinity() // 简化示例
    }
    
    pub fn scalar_multiply(&self, k: &BigUint, p: &BigUint) -> ECPoint {
        let mut result = ECPoint::infinity();
        let mut temp = self.clone();
        let mut k_copy = k.clone();
        
        while k_copy > BigUint::zero() {
            if &k_copy % BigUint::from(2u32) == BigUint::one() {
                result = result.add(&temp, p);
            }
            temp = temp.add(&temp, p);
            k_copy = k_copy >> 1;
        }
        
        result
    }
}
```

### 信息熵计算

```rust
pub fn calculate_entropy(probabilities: &[f64]) -> f64 {
    probabilities
        .iter()
        .filter(|&&p| p > 0.0)
        .map(|&p| -p * p.log2())
        .sum()
}

pub fn calculate_conditional_entropy(
    joint_prob: &[Vec<f64>],
    marginal_prob: &[f64],
) -> f64 {
    let mut entropy = 0.0;
    
    for (i, joint_row) in joint_prob.iter().enumerate() {
        for (j, &p_ij) in joint_row.iter().enumerate() {
            if p_ij > 0.0 && marginal_prob[i] > 0.0 {
                entropy -= p_ij * (p_ij / marginal_prob[i]).log2();
            }
        }
    }
    
    entropy
}
```

## 贡献指南

欢迎对数学基础内容进行贡献。请确保：

1. 所有数学定义都有严格的数学表述
2. 包含完整的定理和证明
3. 提供Rust代码实现
4. 说明在Web3中的具体应用场景
