# 抽象代数与数论 (Abstract Algebra & Number Theory)

## 概述

抽象代数与数论是Web3技术的数学基础，为密码学、区块链共识机制、零知识证明等提供严格的数学支撑。本目录涵盖群论、环论、域论、椭圆曲线理论、素数理论和格理论等关键数学分支。

## 目录结构

### 1.1 群论基础 (Group Theory)

- [**群的定义与性质**](01_Group_Theory/01_Group_Definition_Properties/) - 群的定义、子群、同态、循环群
- [**有限群**](01_Group_Theory/02_Finite_Groups/) - 有限群结构、拉格朗日定理、西罗定理
- [**置换群**](01_Group_Theory/03_Permutation_Groups/) - 对称群、交替群、置换表示
- [**阿贝尔群**](01_Group_Theory/04_Abelian_Groups/) - 阿贝尔群结构、有限生成阿贝尔群
- [**群表示论**](01_Group_Theory/05_Group_Representation_Theory/) - 线性表示、不可约表示、特征标

### 1.2 环论与域论 (Ring & Field Theory)

- [**环的定义与性质**](02_Ring_Field_Theory/01_Ring_Definition_Properties/) - 环的定义、理想、商环、环同态
- [**整环与域**](02_Ring_Field_Theory/02_Integral_Domains_Fields/) - 整环、域、特征、素域
- [**有限域**](02_Ring_Field_Theory/03_Finite_Fields/) - 有限域构造、本原元、有限域上的多项式
- [**多项式环**](02_Ring_Field_Theory/04_Polynomial_Rings/) - 多项式环、欧几里得算法、唯一分解
- [**代数数论**](02_Ring_Field_Theory/05_Algebraic_Number_Theory/) - 代数整数、理想类群、戴德金整环

### 1.3 椭圆曲线理论 (Elliptic Curve Theory)

- [**椭圆曲线基础**](03_Elliptic_Curve_Theory/01_Elliptic_Curve_Basics/) - 椭圆曲线定义、点运算、群结构
- [**有限域上的椭圆曲线**](03_Elliptic_Curve_Theory/02_Elliptic_Curves_over_Finite_Fields/) - 有限域上的椭圆曲线、点的阶
- [**椭圆曲线密码学**](03_Elliptic_Curve_Theory/03_Elliptic_Curve_Cryptography/) - ECDLP、椭圆曲线数字签名
- [**配对密码学**](03_Elliptic_Curve_Theory/04_Pairing_Cryptography/) - 双线性配对、Weil配对、Tate配对
- [**超奇异椭圆曲线**](03_Elliptic_Curve_Theory/05_Supersingular_Elliptic_Curves/) - 超奇异曲线、同源映射

### 1.4 素数理论 (Prime Number Theory)

- [**素数分布**](04_Prime_Number_Theory/01_Prime_Distribution/) - 素数定理、黎曼猜想、素数分布规律
- [**素性测试**](04_Prime_Number_Theory/02_Primality_Testing/) - 费马测试、米勒-拉宾测试、AKS算法
- [**RSA安全性**](04_Prime_Number_Theory/03_RSA_Security/) - RSA算法、大整数分解、RSA安全性分析
- [**素数生成**](04_Prime_Number_Theory/04_Prime_Generation/) - 安全素数生成、随机素数生成
- [**素数应用**](04_Prime_Number_Theory/05_Prime_Applications/) - 密码学应用、数论应用

### 1.5 格理论 (Lattice Theory)

- [**格的定义与性质**](05_Lattice_Theory/01_Lattice_Definition_Properties/) - 格的定义、格基、格的行列式
- [**最短向量问题**](05_Lattice_Theory/02_Shortest_Vector_Problem/) - SVP、LLL算法、格约简
- [**最近向量问题**](05_Lattice_Theory/03_Closest_Vector_Problem/) - CVP、Babai算法、格解码
- [**格密码学**](05_Lattice_Theory/04_Lattice_Cryptography/) - 格基密码、NTRU、格签名
- [**后量子密码学**](05_Lattice_Theory/05_Post_Quantum_Cryptography/) - 后量子密码学、格基后量子方案

## 核心概念

### 群论在Web3中的应用

群论为Web3技术提供了重要的数学基础：

**椭圆曲线群**：

- 椭圆曲线上的点形成阿贝尔群
- 为椭圆曲线密码学提供数学基础
- 支持双线性配对和同态加密

**置换群**：

- 在零知识证明中用于构造证明系统
- 支持匿名性和隐私保护
- 用于构造可验证随机函数

### 有限域的重要性

有限域是密码学的核心数学结构：

**有限域运算**：

- 支持高效的模运算
- 为密码学算法提供数学基础
- 支持多项式运算和编码理论

**有限域上的椭圆曲线**：

- 提供安全的密码学原语
- 支持高效的密钥生成和签名
- 为区块链共识提供数学基础

### 格理论的前沿应用

格理论是后量子密码学的基础：

**格基密码学**：

- 抵抗量子计算攻击
- 提供高效的加密和签名方案
- 支持同态加密和函数加密

**格约简算法**：

- LLL算法用于格基约简
- 支持格问题的求解
- 为格密码学提供算法基础

## 在Web3中的应用

### 1. 椭圆曲线密码学

- **密钥生成**：基于椭圆曲线离散对数问题
- **数字签名**：ECDSA、EdDSA、Schnorr签名
- **密钥交换**：ECDH、X25519、X448
- **零知识证明**：椭圆曲线上的零知识证明系统

### 2. 有限域密码学

- **RSA密码系统**：基于大整数分解问题
- **离散对数密码**：基于有限域上的离散对数
- **哈希函数**：基于有限域运算的哈希函数
- **伪随机数生成**：基于有限域的PRNG

### 3. 格密码学

- **后量子加密**：NTRU、LWE、RLWE
- **同态加密**：基于格的FHE方案
- **函数加密**：基于格的函数加密
- **格签名**：基于格的数字签名

### 4. 零知识证明

- **群论基础**：置换群、椭圆曲线群
- **证明系统**：基于群论的零知识证明
- **匿名性**：基于群论的匿名协议
- **隐私保护**：基于群论的隐私技术

## 学习资源

### 推荐教材

1. **抽象代数**：《Abstract Algebra》- David S. Dummit
2. **数论**：《A Classical Introduction to Modern Number Theory》- Kenneth Ireland
3. **椭圆曲线**：《The Arithmetic of Elliptic Curves》- Joseph H. Silverman
4. **格理论**：《An Introduction to Mathematical Cryptography》- Jeffrey Hoffstein

### 在线资源

- [抽象代数教程](https://abstract.ups.edu/)
- [椭圆曲线密码学](https://www.math.uwaterloo.ca/~ajmeneze/publications/papers/guide.pdf)
- [格密码学基础](https://cims.nyu.edu/~regev/papers/lwesurvey.pdf)

## Rust实现示例

### 椭圆曲线实现

```rust
use std::ops::{Add, Mul, Neg};
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct FieldElement {
    pub value: u64,
    pub modulus: u64,
}

impl FieldElement {
    pub fn new(value: u64, modulus: u64) -> Self {
        FieldElement {
            value: value % modulus,
            modulus,
        }
    }
    
    pub fn pow(&self, exponent: u64) -> Self {
        let mut result = FieldElement::new(1, self.modulus);
        let mut base = *self;
        let mut exp = exponent;
        
        while exp > 0 {
            if exp % 2 == 1 {
                result = result * base;
            }
            base = base * base;
            exp /= 2;
        }
        
        result
    }
    
    pub fn inverse(&self) -> Option<Self> {
        // 扩展欧几里得算法求逆元
        let mut a = self.value as i64;
        let mut b = self.modulus as i64;
        let mut x = 1i64;
        let mut y = 0i64;
        
        while b != 0 {
            let q = a / b;
            let temp = b;
            b = a % b;
            a = temp;
            let temp = y;
            y = x - q * y;
            x = temp;
        }
        
        if a == 1 {
            Some(FieldElement::new(
                ((x % self.modulus as i64) + self.modulus as i64) as u64 % self.modulus,
                self.modulus,
            ))
        } else {
            None
        }
    }
}

impl Add for FieldElement {
    type Output = Self;
    
    fn add(self, other: Self) -> Self {
        assert_eq!(self.modulus, other.modulus);
        FieldElement::new(self.value + other.value, self.modulus)
    }
}

impl Mul for FieldElement {
    type Output = Self;
    
    fn mul(self, other: Self) -> Self {
        assert_eq!(self.modulus, other.modulus);
        FieldElement::new(self.value * other.value, self.modulus)
    }
}

impl Neg for FieldElement {
    type Output = Self;
    
    fn neg(self) -> Self {
        FieldElement::new(self.modulus - self.value, self.modulus)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct EllipticCurvePoint {
    pub x: Option<FieldElement>,
    pub y: Option<FieldElement>,
    pub curve: EllipticCurve,
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct EllipticCurve {
    pub a: FieldElement,
    pub b: FieldElement,
}

impl EllipticCurve {
    pub fn new(a: FieldElement, b: FieldElement) -> Self {
        EllipticCurve { a, b }
    }
    
    pub fn infinity_point(&self) -> EllipticCurvePoint {
        EllipticCurvePoint {
            x: None,
            y: None,
            curve: *self,
        }
    }
    
    pub fn point(&self, x: FieldElement, y: FieldElement) -> Option<EllipticCurvePoint> {
        // 检查点是否在曲线上
        let left = y * y;
        let right = x * x * x + self.a * x + self.b;
        
        if left == right {
            Some(EllipticCurvePoint {
                x: Some(x),
                y: Some(y),
                curve: *self,
            })
        } else {
            None
        }
    }
}

impl Add for EllipticCurvePoint {
    type Output = Self;
    
    fn add(self, other: Self) -> Self {
        assert_eq!(self.curve, other.curve);
        
        // 无穷远点的情况
        if self.x.is_none() {
            return other;
        }
        if other.x.is_none() {
            return self;
        }
        
        let x1 = self.x.unwrap();
        let y1 = self.y.unwrap();
        let x2 = other.x.unwrap();
        let y2 = other.y.unwrap();
        
        // 相同点的情况
        if x1 == x2 {
            if y1 == -y2 {
                return self.curve.infinity_point();
            }
            
            // 切线斜率
            let slope = (FieldElement::new(3, x1.modulus) * x1 * x1 + self.curve.a) 
                * (FieldElement::new(2, y1.modulus) * y1).inverse().unwrap();
            
            let x3 = slope * slope - x1 - x2;
            let y3 = slope * (x1 - x3) - y1;
            
            EllipticCurvePoint {
                x: Some(x3),
                y: Some(y3),
                curve: self.curve,
            }
        } else {
            // 不同点的情况
            let slope = (y2 - y1) * (x2 - x1).inverse().unwrap();
            
            let x3 = slope * slope - x1 - x2;
            let y3 = slope * (x1 - x3) - y1;
            
            EllipticCurvePoint {
                x: Some(x3),
                y: Some(y3),
                curve: self.curve,
            }
        }
    }
}

impl Mul<u64> for EllipticCurvePoint {
    type Output = Self;
    
    fn mul(self, scalar: u64) -> Self {
        let mut result = self.curve.infinity_point();
        let mut point = self;
        let mut exp = scalar;
        
        while exp > 0 {
            if exp % 2 == 1 {
                result = result + point;
            }
            point = point + point;
            exp /= 2;
        }
        
        result
    }
}

pub struct EllipticCurveCrypto {
    curve: EllipticCurve,
    generator: EllipticCurvePoint,
    order: u64,
}

impl EllipticCurveCrypto {
    pub fn new(curve: EllipticCurve, generator: EllipticCurvePoint, order: u64) -> Self {
        EllipticCurveCrypto {
            curve,
            generator,
            order,
        }
    }
    
    pub fn generate_keypair(&self) -> (u64, EllipticCurvePoint) {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        let private_key = rng.gen_range(1..self.order);
        let public_key = self.generator * private_key;
        
        (private_key, public_key)
    }
    
    pub fn sign(&self, private_key: u64, message_hash: u64) -> (u64, u64) {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        loop {
            let k = rng.gen_range(1..self.order);
            let r_point = self.generator * k;
            
            if r_point.x.is_none() {
                continue;
            }
            
            let r = r_point.x.unwrap().value;
            if r == 0 {
                continue;
            }
            
            let k_inv = FieldElement::new(k, self.order).inverse().unwrap();
            let s = k_inv * FieldElement::new(message_hash + private_key * r, self.order);
            
            if s.value != 0 {
                return (r, s.value);
            }
        }
    }
    
    pub fn verify(&self, public_key: &EllipticCurvePoint, message_hash: u64, signature: (u64, u64)) -> bool {
        let (r, s) = signature;
        
        if r == 0 || s == 0 || r >= self.order || s >= self.order {
            return false;
        }
        
        let w = FieldElement::new(s, self.order).inverse().unwrap();
        let u1 = FieldElement::new(message_hash * w.value, self.order);
        let u2 = FieldElement::new(r * w.value, self.order);
        
        let point1 = self.generator * u1.value;
        let point2 = *public_key * u2.value;
        let sum_point = point1 + point2;
        
        if sum_point.x.is_none() {
            return false;
        }
        
        sum_point.x.unwrap().value == r
    }
}
```

### 有限域实现

```rust
use std::ops::{Add, Sub, Mul, Div, Neg};
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct FiniteField {
    pub value: u64,
    pub modulus: u64,
}

impl FiniteField {
    pub fn new(value: u64, modulus: u64) -> Self {
        FiniteField {
            value: value % modulus,
            modulus,
        }
    }
    
    pub fn pow(&self, exponent: u64) -> Self {
        let mut result = FiniteField::new(1, self.modulus);
        let mut base = *self;
        let mut exp = exponent;
        
        while exp > 0 {
            if exp % 2 == 1 {
                result = result * base;
            }
            base = base * base;
            exp /= 2;
        }
        
        result
    }
    
    pub fn inverse(&self) -> Option<Self> {
        if self.value == 0 {
            return None;
        }
        
        // 扩展欧几里得算法
        let mut a = self.value as i64;
        let mut b = self.modulus as i64;
        let mut x = 1i64;
        let mut y = 0i64;
        
        while b != 0 {
            let q = a / b;
            let temp = b;
            b = a % b;
            a = temp;
            let temp = y;
            y = x - q * y;
            x = temp;
        }
        
        if a == 1 {
            Some(FiniteField::new(
                ((x % self.modulus as i64) + self.modulus as i64) as u64 % self.modulus,
                self.modulus,
            ))
        } else {
            None
        }
    }
    
    pub fn is_primitive_root(&self) -> bool {
        if self.value == 0 {
            return false;
        }
        
        let phi = self.modulus - 1;
        let factors = self.prime_factors(phi);
        
        for factor in factors {
            if self.pow(phi / factor) == FiniteField::new(1, self.modulus) {
                return false;
            }
        }
        
        true
    }
    
    fn prime_factors(&self, n: u64) -> Vec<u64> {
        let mut factors = Vec::new();
        let mut n = n;
        let mut d = 2;
        
        while d * d <= n {
            while n % d == 0 {
                if !factors.contains(&d) {
                    factors.push(d);
                }
                n /= d;
            }
            d += 1;
        }
        
        if n > 1 && !factors.contains(&n) {
            factors.push(n);
        }
        
        factors
    }
}

impl Add for FiniteField {
    type Output = Self;
    
    fn add(self, other: Self) -> Self {
        assert_eq!(self.modulus, other.modulus);
        FiniteField::new(self.value + other.value, self.modulus)
    }
}

impl Sub for FiniteField {
    type Output = Self;
    
    fn sub(self, other: Self) -> Self {
        assert_eq!(self.modulus, other.modulus);
        FiniteField::new(
            if self.value >= other.value {
                self.value - other.value
            } else {
                self.modulus - (other.value - self.value)
            },
            self.modulus,
        )
    }
}

impl Mul for FiniteField {
    type Output = Self;
    
    fn mul(self, other: Self) -> Self {
        assert_eq!(self.modulus, other.modulus);
        FiniteField::new(self.value * other.value, self.modulus)
    }
}

impl Div for FiniteField {
    type Output = Self;
    
    fn div(self, other: Self) -> Self {
        assert_eq!(self.modulus, other.modulus);
        let other_inv = other.inverse().expect("Division by zero");
        self * other_inv
    }
}

impl Neg for FiniteField {
    type Output = Self;
    
    fn neg(self) -> Self {
        FiniteField::new(self.modulus - self.value, self.modulus)
    }
}

pub struct FiniteFieldCrypto {
    field: u64,
    generator: FiniteField,
}

impl FiniteFieldCrypto {
    pub fn new(field: u64, generator: FiniteField) -> Self {
        FiniteFieldCrypto { field, generator }
    }
    
    pub fn generate_keypair(&self) -> (u64, FiniteField) {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        let private_key = rng.gen_range(1..self.field);
        let public_key = self.generator.pow(private_key);
        
        (private_key, public_key)
    }
    
    pub fn diffie_hellman(&self, private_key: u64, public_key: FiniteField) -> FiniteField {
        public_key.pow(private_key)
    }
    
    pub fn elgamal_encrypt(&self, public_key: FiniteField, message: u64) -> (FiniteField, FiniteField) {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        let k = rng.gen_range(1..self.field);
        let c1 = self.generator.pow(k);
        let c2 = FiniteField::new(message, self.field) * public_key.pow(k);
        
        (c1, c2)
    }
    
    pub fn elgamal_decrypt(&self, private_key: u64, ciphertext: (FiniteField, FiniteField)) -> u64 {
        let (c1, c2) = ciphertext;
        let s = c1.pow(private_key);
        let s_inv = s.inverse().unwrap();
        let message = c2 * s_inv;
        
        message.value
    }
}
```

### 格理论实现

```rust
use std::ops::{Add, Sub, Mul};
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Lattice {
    pub basis: Vec<Vec<i64>>,
    pub dimension: usize,
}

impl Lattice {
    pub fn new(basis: Vec<Vec<i64>>) -> Self {
        let dimension = basis.len();
        assert!(dimension > 0);
        assert!(basis.iter().all(|row| row.len() == dimension));
        
        Lattice { basis, dimension }
    }
    
    pub fn determinant(&self) -> f64 {
        // 计算格的行列式
        let mut det = 1.0;
        let mut matrix = self.basis.clone();
        
        for i in 0..self.dimension {
            // 找到主元
            let mut max_row = i;
            for j in (i + 1)..self.dimension {
                if matrix[j][i].abs() > matrix[max_row][i].abs() {
                    max_row = j;
                }
            }
            
            if matrix[max_row][i] == 0 {
                return 0.0; // 奇异矩阵
            }
            
            // 交换行
            if max_row != i {
                matrix.swap(i, max_row);
                det = -det;
            }
            
            // 消元
            for j in (i + 1)..self.dimension {
                let factor = matrix[j][i] as f64 / matrix[i][i] as f64;
                for k in i..self.dimension {
                    matrix[j][k] -= (factor * matrix[i][k] as f64) as i64;
                }
            }
            
            det *= matrix[i][i] as f64;
        }
        
        det.abs()
    }
    
    pub fn shortest_vector(&self) -> Option<Vec<i64>> {
        // 简化的最短向量算法
        let mut shortest = None;
        let mut min_norm = f64::INFINITY;
        
        // 检查所有可能的短向量
        for i in 0..self.dimension {
            let norm = self.vector_norm(&self.basis[i]);
            if norm < min_norm {
                min_norm = norm;
                shortest = Some(self.basis[i].clone());
            }
        }
        
        shortest
    }
    
    pub fn vector_norm(&self, vector: &[i64]) -> f64 {
        vector.iter().map(|&x| (x * x) as f64).sum::<f64>().sqrt()
    }
    
    pub fn lll_reduction(&mut self, delta: f64) {
        // LLL格约简算法
        assert!(0.25 < delta && delta < 1.0);
        
        let mut k = 1;
        while k < self.dimension {
            // Gram-Schmidt正交化
            for j in (0..k).rev() {
                let mu = self.gram_schmidt_coefficient(k, j);
                if mu.abs() > 0.5 {
                    for i in 0..self.dimension {
                        self.basis[k][i] -= (mu * self.basis[j][i] as f64) as i64;
                    }
                }
            }
            
            // Lovász条件
            let norm_k = self.vector_norm(&self.basis[k]);
            let norm_k_minus_1 = self.vector_norm(&self.basis[k - 1]);
            
            if norm_k * norm_k >= (delta - self.gram_schmidt_coefficient(k, k - 1).powi(2)) * norm_k_minus_1 * norm_k_minus_1 {
                k += 1;
            } else {
                self.basis.swap(k, k - 1);
                k = (k - 1).max(1);
            }
        }
    }
    
    fn gram_schmidt_coefficient(&self, i: usize, j: usize) -> f64 {
        let mut numerator = 0.0;
        let mut denominator = 0.0;
        
        for k in 0..self.dimension {
            numerator += self.basis[i][k] as f64 * self.basis[j][k] as f64;
            denominator += self.basis[j][k] as f64 * self.basis[j][k] as f64;
        }
        
        if denominator == 0.0 {
            0.0
        } else {
            numerator / denominator
        }
    }
}

pub struct LatticeCrypto {
    lattice: Lattice,
    modulus: u64,
}

impl LatticeCrypto {
    pub fn new(lattice: Lattice, modulus: u64) -> Self {
        LatticeCrypto { lattice, modulus }
    }
    
    pub fn generate_keypair(&self) -> (Vec<i64>, Vec<i64>) {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        // 生成私钥（短向量）
        let mut private_key = vec![0i64; self.lattice.dimension];
        for i in 0..self.lattice.dimension {
            private_key[i] = rng.gen_range(-1..=1);
        }
        
        // 生成公钥（格上的点）
        let mut public_key = vec![0i64; self.lattice.dimension];
        for i in 0..self.lattice.dimension {
            for j in 0..self.lattice.dimension {
                public_key[i] += self.lattice.basis[j][i] * private_key[j];
            }
            public_key[i] = public_key[i].rem_euclid(self.modulus as i64);
        }
        
        (private_key, public_key)
    }
    
    pub fn encrypt(&self, public_key: &[i64], message: u64) -> (Vec<i64>, u64) {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        // 生成随机向量
        let mut r = vec![0i64; self.lattice.dimension];
        for i in 0..self.lattice.dimension {
            r[i] = rng.gen_range(-1..=1);
        }
        
        // 计算密文
        let mut c1 = vec![0i64; self.lattice.dimension];
        for i in 0..self.lattice.dimension {
            for j in 0..self.lattice.dimension {
                c1[i] += self.lattice.basis[j][i] * r[j];
            }
            c1[i] = c1[i].rem_euclid(self.modulus as i64);
        }
        
        let mut c2 = 0u64;
        for i in 0..self.lattice.dimension {
            c2 = (c2 + (public_key[i] as u64 * r[i] as u64)) % self.modulus;
        }
        c2 = (c2 + message) % self.modulus;
        
        (c1, c2)
    }
    
    pub fn decrypt(&self, private_key: &[i64], ciphertext: (Vec<i64>, u64)) -> u64 {
        let (c1, c2) = ciphertext;
        
        // 计算内积
        let mut inner_product = 0i64;
        for i in 0..self.lattice.dimension {
            inner_product += private_key[i] * c1[i];
        }
        inner_product = inner_product.rem_euclid(self.modulus as i64);
        
        // 解密
        let mut message = c2 as i64 - inner_product;
        message = message.rem_euclid(self.modulus as i64);
        
        message as u64
    }
}
```

## 贡献指南

欢迎对抽象代数与数论内容进行贡献。请确保：

1. 所有数学概念都有严格的数学定义
2. 包含在Web3中的具体应用场景
3. 提供Rust代码实现示例
4. 说明算法的复杂度和安全性
5. 关注最新的数学研究成果
