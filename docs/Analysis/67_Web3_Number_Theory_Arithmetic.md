# Web3数论与算术

## 概述

本文档建立Web3系统的数论与算术基础，从素数理论、同余理论、二次剩余、椭圆曲线、格理论等多个维度构建完整的理论体系。

## 1. 素数理论

### 1.1 素数基本性质

**定义 1.1.1 (素数)**
素数p是大于1的自然数，其正因子只有1和p。

**定义 1.1.2 (合数)**
合数是大于1的非素数自然数。

**算法 1.1.1 (素数判定算法)**

```rust
pub struct PrimeTheory {
    primes: Vec<u64>,
    max_checked: u64,
}

impl PrimeTheory {
    pub fn new() -> Self {
        PrimeTheory {
            primes: vec![2, 3, 5, 7],
            max_checked: 10,
        }
    }
    
    pub fn is_prime(&mut self, n: u64) -> bool {
        if n < 2 {
            return false;
        }
        if n == 2 {
            return true;
        }
        if n % 2 == 0 {
            return false;
        }
        
        // 确保已检查到足够大的素数
        self.sieve_up_to((n as f64).sqrt() as u64 + 1);
        
        // 检查n是否能被已知素数整除
        for &prime in &self.primes {
            if prime * prime > n {
                break;
            }
            if n % prime == 0 {
                return false;
            }
        }
        
        true
    }
    
    pub fn sieve_up_to(&mut self, limit: u64) {
        if limit <= self.max_checked {
            return;
        }
        
        let mut is_prime = vec![true; (limit + 1) as usize];
        is_prime[0] = false;
        is_prime[1] = false;
        
        for i in 2..=limit {
            if is_prime[i as usize] {
                // 标记i的倍数为合数
                for j in (i * i..=limit).step_by(i as usize) {
                    is_prime[j as usize] = false;
                }
            }
        }
        
        // 更新素数列表
        for i in (self.max_checked + 1)..=limit {
            if is_prime[i as usize] {
                self.primes.push(i);
            }
        }
        
        self.max_checked = limit;
    }
    
    pub fn prime_factors(&mut self, n: u64) -> Vec<(u64, u32)> {
        let mut factors = Vec::new();
        let mut n_mut = n;
        
        // 确保已检查到足够大的素数
        self.sieve_up_to((n as f64).sqrt() as u64 + 1);
        
        for &prime in &self.primes {
            if prime * prime > n_mut {
                break;
            }
            
            let mut exponent = 0;
            while n_mut % prime == 0 {
                exponent += 1;
                n_mut /= prime;
            }
            
            if exponent > 0 {
                factors.push((prime, exponent));
            }
        }
        
        if n_mut > 1 {
            factors.push((n_mut, 1));
        }
        
        factors
    }
    
    pub fn euler_totient(&mut self, n: u64) -> u64 {
        let factors = self.prime_factors(n);
        let mut result = n;
        
        for (prime, _) in factors {
            result = result / prime * (prime - 1);
        }
        
        result
    }
    
    pub fn prime_count(&mut self, n: u64) -> u64 {
        self.sieve_up_to(n);
        self.primes.iter().filter(|&&p| p <= n).count() as u64
    }
    
    pub fn nth_prime(&mut self, n: u32) -> Option<u64> {
        if n == 0 {
            return None;
        }
        
        // 估计第n个素数的大小
        let estimate = if n < 6 {
            n as u64 * 2
        } else {
            (n as f64 * (n as f64).ln() * 1.2) as u64
        };
        
        self.sieve_up_to(estimate);
        
        if n as usize <= self.primes.len() {
            Some(self.primes[n as usize - 1])
        } else {
            None
        }
    }
}
```

### 1.2 素数分布

**定义 1.2.1 (素数定理)**
$$\lim_{x \to \infty} \frac{\pi(x)}{x/\ln x} = 1$$

**算法 1.2.1 (素数分布算法)**

```rust
pub struct PrimeDistribution {
    prime_theory: PrimeTheory,
}

impl PrimeDistribution {
    pub fn new() -> Self {
        PrimeDistribution {
            prime_theory: PrimeTheory::new(),
        }
    }
    
    pub fn prime_count_approximation(&self, x: f64) -> f64 {
        x / x.ln()
    }
    
    pub fn li_function(&self, x: f64) -> f64 {
        // 对数积分函数的近似
        let mut result = 0.0;
        let step = 0.001;
        let mut t = 2.0;
        
        while t <= x {
            result += step / t.ln();
            t += step;
        }
        
        result
    }
    
    pub fn riemann_hypothesis_implication(&self, x: f64) -> f64 {
        // 黎曼假设下的素数计数函数
        let li_x = self.li_function(x);
        let sqrt_x = x.sqrt();
        let log_x = x.ln();
        
        // 主要项 + 误差项
        li_x + sqrt_x * log_x / (2.0 * std::f64::consts::PI)
    }
    
    pub fn twin_primes(&mut self, limit: u64) -> Vec<(u64, u64)> {
        let mut twin_primes = Vec::new();
        self.prime_theory.sieve_up_to(limit);
        
        for i in 0..self.prime_theory.primes.len() - 1 {
            let p1 = self.prime_theory.primes[i];
            let p2 = self.prime_theory.primes[i + 1];
            
            if p2 - p1 == 2 {
                twin_primes.push((p1, p2));
            }
        }
        
        twin_primes
    }
    
    pub fn goldbach_conjecture_verification(&mut self, even_number: u64) -> Option<(u64, u64)> {
        if even_number < 4 || even_number % 2 != 0 {
            return None;
        }
        
        self.prime_theory.sieve_up_to(even_number);
        
        for &prime in &self.prime_theory.primes {
            if prime > even_number / 2 {
                break;
            }
            
            let other = even_number - prime;
            if self.prime_theory.is_prime(other) {
                return Some((prime, other));
            }
        }
        
        None
    }
    
    pub fn mersenne_primes(&mut self, limit: u64) -> Vec<u64> {
        let mut mersenne_primes = Vec::new();
        
        for p in 2..=64 {
            let mersenne = (1u64 << p) - 1;
            if mersenne > limit {
                break;
            }
            
            if self.prime_theory.is_prime(mersenne) {
                mersenne_primes.push(mersenne);
            }
        }
        
        mersenne_primes
    }
}
```

## 2. 同余理论

### 2.1 同余基本概念

**定义 2.1.1 (同余)**
$a \equiv b \pmod{m}$ 当且仅当 $m | (a - b)$。

**算法 2.1.1 (同余算法)**

```rust
pub struct CongruenceTheory {
    modulus: u64,
}

impl CongruenceTheory {
    pub fn new(modulus: u64) -> Self {
        CongruenceTheory { modulus }
    }
    
    pub fn is_congruent(&self, a: i64, b: i64) -> bool {
        let m = self.modulus as i64;
        (a - b) % m == 0
    }
    
    pub fn reduce(&self, a: i64) -> u64 {
        let m = self.modulus as i64;
        let remainder = a % m;
        if remainder < 0 {
            (remainder + m) as u64
        } else {
            remainder as u64
        }
    }
    
    pub fn add(&self, a: u64, b: u64) -> u64 {
        (a + b) % self.modulus
    }
    
    pub fn subtract(&self, a: u64, b: u64) -> u64 {
        if a >= b {
            (a - b) % self.modulus
        } else {
            (self.modulus - (b - a) % self.modulus) % self.modulus
        }
    }
    
    pub fn multiply(&self, a: u64, b: u64) -> u64 {
        (a * b) % self.modulus
    }
    
    pub fn power(&self, base: u64, exponent: u64) -> u64 {
        if exponent == 0 {
            return 1;
        }
        
        let mut result = 1;
        let mut base_mut = base;
        let mut exp_mut = exponent;
        
        while exp_mut > 0 {
            if exp_mut % 2 == 1 {
                result = self.multiply(result, base_mut);
            }
            base_mut = self.multiply(base_mut, base_mut);
            exp_mut /= 2;
        }
        
        result
    }
    
    pub fn multiplicative_inverse(&self, a: u64) -> Option<u64> {
        let (gcd, x, _) = self.extended_gcd(a as i64, self.modulus as i64);
        
        if gcd == 1 {
            Some(self.reduce(x) as u64)
        } else {
            None
        }
    }
    
    pub fn extended_gcd(&self, a: i64, b: i64) -> (i64, i64, i64) {
        if b == 0 {
            (a, 1, 0)
        } else {
            let (gcd, x, y) = self.extended_gcd(b, a % b);
            (gcd, y, x - (a / b) * y)
        }
    }
    
    pub fn solve_linear_congruence(&self, a: u64, b: u64) -> Option<Vec<u64>> {
        let (gcd, x, _) = self.extended_gcd(a as i64, self.modulus as i64);
        
        if b % gcd as u64 != 0 {
            return None;
        }
        
        let mut solutions = Vec::new();
        let x0 = self.reduce(x * (b as i64 / gcd));
        let step = self.modulus / gcd as u64;
        
        for k in 0..gcd as u64 {
            solutions.push((x0 + k * step) % self.modulus);
        }
        
        Some(solutions)
    }
    
    pub fn chinese_remainder_theorem(&self, congruences: &[(u64, u64)]) -> Option<u64> {
        if congruences.is_empty() {
            return None;
        }
        
        let mut result = congruences[0].1;
        let mut modulus_product = congruences[0].0;
        
        for &(modulus, remainder) in &congruences[1..] {
            let (gcd, _, _) = self.extended_gcd(modulus_product as i64, modulus as i64);
            
            if gcd != 1 {
                return None; // 模数不互素
            }
            
            let m1_inv = self.extended_gcd(modulus_product as i64, modulus as i64).1;
            let m2_inv = self.extended_gcd(modulus as i64, modulus_product as i64).1;
            
            let new_result = (result as i64 * modulus as i64 * m2_inv + 
                             remainder as i64 * modulus_product as i64 * m1_inv) % 
                            (modulus_product as i64 * modulus as i64);
            
            result = new_result as u64;
            modulus_product *= modulus;
        }
        
        Some(result % modulus_product)
    }
}
```

### 2.2 欧拉函数与费马小定理

**定义 2.2.1 (欧拉函数)**
$\phi(n)$ 是与n互素且不超过n的正整数个数。

**算法 2.2.1 (欧拉函数算法)**

```rust
pub struct EulerFunction {
    prime_theory: PrimeTheory,
}

impl EulerFunction {
    pub fn new() -> Self {
        EulerFunction {
            prime_theory: PrimeTheory::new(),
        }
    }
    
    pub fn phi(&mut self, n: u64) -> u64 {
        if n == 1 {
            return 1;
        }
        
        let factors = self.prime_theory.prime_factors(n);
        let mut result = n;
        
        for (prime, _) in factors {
            result = result / prime * (prime - 1);
        }
        
        result
    }
    
    pub fn phi_up_to(&mut self, limit: u64) -> Vec<u64> {
        let mut phi_values = vec![0; (limit + 1) as usize];
        
        for i in 1..=limit {
            phi_values[i as usize] = i;
        }
        
        for p in 2..=limit {
            if phi_values[p as usize] == p {
                // p是素数
                for multiple in (p..=limit).step_by(p as usize) {
                    phi_values[multiple as usize] = phi_values[multiple as usize] / p * (p - 1);
                }
            }
        }
        
        phi_values
    }
    
    pub fn fermat_little_theorem(&self, a: u64, p: u64) -> bool {
        if !self.prime_theory.is_prime(p) {
            return false;
        }
        
        let congruence = CongruenceTheory::new(p);
        congruence.power(a, p - 1) == 1
    }
    
    pub fn euler_theorem(&mut self, a: u64, n: u64) -> bool {
        if self.gcd(a, n) != 1 {
            return false;
        }
        
        let phi_n = self.phi(n);
        let congruence = CongruenceTheory::new(n);
        congruence.power(a, phi_n) == 1
    }
    
    fn gcd(&self, a: u64, b: u64) -> u64 {
        if b == 0 {
            a
        } else {
            self.gcd(b, a % b)
        }
    }
    
    pub fn carmichael_function(&mut self, n: u64) -> u64 {
        let factors = self.prime_theory.prime_factors(n);
        let mut lambda = 1;
        
        for (prime, exponent) in factors {
            let phi_prime = self.phi(prime);
            let lambda_prime = if exponent == 1 {
                phi_prime
            } else {
                phi_prime * prime.pow(exponent - 1)
            };
            
            lambda = self.lcm(lambda, lambda_prime);
        }
        
        lambda
    }
    
    fn lcm(&self, a: u64, b: u64) -> u64 {
        a * b / self.gcd(a, b)
    }
}
```

## 3. 二次剩余

### 3.1 二次剩余基本概念

**定义 3.1.1 (二次剩余)**
a是模p的二次剩余，如果存在x使得 $x^2 \equiv a \pmod{p}$。

**算法 3.1.1 (二次剩余算法)**

```rust
pub struct QuadraticResidue {
    prime_theory: PrimeTheory,
}

impl QuadraticResidue {
    pub fn new() -> Self {
        QuadraticResidue {
            prime_theory: PrimeTheory::new(),
        }
    }
    
    pub fn legendre_symbol(&mut self, a: u64, p: u64) -> i32 {
        if !self.prime_theory.is_prime(p) {
            return 0;
        }
        
        if a % p == 0 {
            return 0;
        }
        
        if self.prime_theory.is_prime(a) && a % 4 == 3 && p % 4 == 3 {
            return -self.legendre_symbol(p, a);
        }
        
        if a % 2 == 0 {
            let exponent = (a / 2).trailing_zeros() as u32;
            let result = if exponent % 2 == 0 {
                1
            } else {
                if p % 8 == 1 || p % 8 == 7 {
                    1
                } else {
                    -1
                }
            };
            result * self.legendre_symbol(a / (1 << exponent), p)
        } else {
            if a % 4 == 1 || p % 4 == 1 {
                self.legendre_symbol(p % a, a)
            } else {
                -self.legendre_symbol(p % a, a)
            }
        }
    }
    
    pub fn is_quadratic_residue(&mut self, a: u64, p: u64) -> bool {
        self.legendre_symbol(a, p) == 1
    }
    
    pub fn tonelli_shanks(&mut self, n: u64, p: u64) -> Option<u64> {
        if !self.is_quadratic_residue(n, p) {
            return None;
        }
        
        if p == 2 {
            return Some(n);
        }
        
        if p % 4 == 3 {
            return Some(self.modular_pow(n, (p + 1) / 4, p));
        }
        
        // 找到二次非剩余
        let mut q = 2;
        while self.is_quadratic_residue(q, p) {
            q += 1;
        }
        
        let mut s = 0;
        let mut q_power = p - 1;
        while q_power % 2 == 0 {
            s += 1;
            q_power /= 2;
        }
        
        let mut m = s;
        let mut c = self.modular_pow(q, q_power, p);
        let mut t = self.modular_pow(n, q_power, p);
        let mut r = self.modular_pow(n, (q_power + 1) / 2, p);
        
        while t != 1 {
            let mut i = 0;
            let mut temp = t;
            while temp != 1 && i < m {
                temp = self.modular_pow(temp, 2, p);
                i += 1;
            }
            
            if i == 0 {
                return None;
            }
            
            let b = self.modular_pow(c, 1 << (m - i - 1), p);
            m = i;
            c = self.modular_pow(b, 2, p);
            t = self.modular_multiply(t, c, p);
            r = self.modular_multiply(r, b, p);
        }
        
        Some(r)
    }
    
    fn modular_pow(&self, base: u64, exponent: u64, modulus: u64) -> u64 {
        if modulus == 1 {
            return 0;
        }
        
        let mut result = 1;
        let mut base_mut = base % modulus;
        let mut exp_mut = exponent;
        
        while exp_mut > 0 {
            if exp_mut % 2 == 1 {
                result = self.modular_multiply(result, base_mut, modulus);
            }
            base_mut = self.modular_multiply(base_mut, base_mut, modulus);
            exp_mut /= 2;
        }
        
        result
    }
    
    fn modular_multiply(&self, a: u64, b: u64, modulus: u64) -> u64 {
        let mut result = 0;
        let mut a_mut = a;
        let mut b_mut = b;
        
        while b_mut > 0 {
            if b_mut % 2 == 1 {
                result = (result + a_mut) % modulus;
            }
            a_mut = (a_mut * 2) % modulus;
            b_mut /= 2;
        }
        
        result
    }
    
    pub fn quadratic_residues(&mut self, p: u64) -> Vec<u64> {
        let mut residues = Vec::new();
        
        for a in 1..p {
            if self.is_quadratic_residue(a, p) {
                residues.push(a);
            }
        }
        
        residues
    }
    
    pub fn quadratic_non_residues(&mut self, p: u64) -> Vec<u64> {
        let mut non_residues = Vec::new();
        
        for a in 1..p {
            if !self.is_quadratic_residue(a, p) {
                non_residues.push(a);
            }
        }
        
        non_residues
    }
}
```

## 4. 椭圆曲线

### 4.1 椭圆曲线基本概念

**定义 4.1.1 (椭圆曲线)**
椭圆曲线是方程 $y^2 = x^3 + ax + b$ 的解集。

**算法 4.1.1 (椭圆曲线算法)**

```rust
pub struct EllipticCurve {
    a: i64,
    b: i64,
    p: u64,
    point_at_infinity: EllipticPoint,
}

impl EllipticCurve {
    pub fn new(a: i64, b: i64, p: u64) -> Self {
        EllipticCurve {
            a,
            b,
            p,
            point_at_infinity: EllipticPoint::infinity(),
        }
    }
    
    pub fn is_valid(&self) -> bool {
        // 检查判别式不为零
        let discriminant = 4 * self.a * self.a * self.a + 27 * self.b * self.b;
        discriminant % self.p as i64 != 0
    }
    
    pub fn add_points(&self, p1: &EllipticPoint, p2: &EllipticPoint) -> EllipticPoint {
        if p1.is_infinity() {
            return p2.clone();
        }
        if p2.is_infinity() {
            return p1.clone();
        }
        
        if p1.x == p2.x && p1.y != p2.y {
            return self.point_at_infinity.clone();
        }
        
        let lambda = if p1.x == p2.x {
            // 点加法：计算切线斜率
            let numerator = 3 * p1.x * p1.x + self.a;
            let denominator = 2 * p1.y;
            self.modular_divide(numerator, denominator)
        } else {
            // 点加法：计算连线斜率
            let numerator = p2.y - p1.y;
            let denominator = p2.x - p1.x;
            self.modular_divide(numerator, denominator)
        };
        
        let x3 = (lambda * lambda - p1.x - p2.x) % self.p as i64;
        let y3 = (lambda * (p1.x - x3) - p1.y) % self.p as i64;
        
        EllipticPoint::new(self.reduce(x3), self.reduce(y3))
    }
    
    pub fn scalar_multiply(&self, point: &EllipticPoint, scalar: u64) -> EllipticPoint {
        let mut result = self.point_at_infinity.clone();
        let mut current = point.clone();
        let mut exp = scalar;
        
        while exp > 0 {
            if exp % 2 == 1 {
                result = self.add_points(&result, &current);
            }
            current = self.add_points(&current, &current);
            exp /= 2;
        }
        
        result
    }
    
    pub fn order(&self, point: &EllipticPoint) -> Option<u64> {
        if point.is_infinity() {
            return Some(1);
        }
        
        let mut current = point.clone();
        let mut order = 1;
        
        while !current.is_infinity() && order <= self.p + 1 {
            current = self.add_points(&current, point);
            order += 1;
        }
        
        if current.is_infinity() {
            Some(order)
        } else {
            None
        }
    }
    
    pub fn find_generator(&self) -> Option<EllipticPoint> {
        for x in 0..self.p {
            for y in 0..self.p {
                let point = EllipticPoint::new(x, y);
                if self.is_on_curve(&point) {
                    if let Some(order) = self.order(&point) {
                        if order == self.p + 1 {
                            return Some(point);
                        }
                    }
                }
            }
        }
        None
    }
    
    pub fn is_on_curve(&self, point: &EllipticPoint) -> bool {
        if point.is_infinity() {
            return true;
        }
        
        let x = point.x as i64;
        let y = point.y as i64;
        let left = (y * y) % self.p as i64;
        let right = (x * x * x + self.a * x + self.b) % self.p as i64;
        
        left == right
    }
    
    fn modular_divide(&self, numerator: i64, denominator: i64) -> i64 {
        let congruence = CongruenceTheory::new(self.p);
        let denom_inv = congruence.multiplicative_inverse(self.reduce(denominator))
            .expect("Denominator should be invertible");
        self.reduce(numerator * denom_inv as i64)
    }
    
    fn reduce(&self, value: i64) -> u64 {
        let m = self.p as i64;
        let remainder = value % m;
        if remainder < 0 {
            (remainder + m) as u64
        } else {
            remainder as u64
        }
    }
}

pub struct EllipticPoint {
    x: u64,
    y: u64,
    infinity: bool,
}

impl EllipticPoint {
    pub fn new(x: u64, y: u64) -> Self {
        EllipticPoint {
            x,
            y,
            infinity: false,
        }
    }
    
    pub fn infinity() -> Self {
        EllipticPoint {
            x: 0,
            y: 0,
            infinity: true,
        }
    }
    
    pub fn is_infinity(&self) -> bool {
        self.infinity
    }
    
    pub fn x(&self) -> u64 {
        self.x
    }
    
    pub fn y(&self) -> u64 {
        self.y
    }
}

impl Clone for EllipticPoint {
    fn clone(&self) -> Self {
        EllipticPoint {
            x: self.x,
            y: self.y,
            infinity: self.infinity,
        }
    }
}

impl PartialEq for EllipticPoint {
    fn eq(&self, other: &Self) -> bool {
        if self.infinity && other.infinity {
            true
        } else if self.infinity || other.infinity {
            false
        } else {
            self.x == other.x && self.y == other.y
        }
    }
}

impl Eq for EllipticPoint {}
```

### 4.2 椭圆曲线密码学

**定义 4.2.1 (椭圆曲线离散对数)**
给定点P和Q，找到k使得Q = kP。

**算法 4.2.1 (椭圆曲线密码学算法)**

```rust
pub struct EllipticCurveCrypto {
    curve: EllipticCurve,
    generator: EllipticPoint,
    order: u64,
}

impl EllipticCurveCrypto {
    pub fn new(curve: EllipticCurve, generator: EllipticPoint, order: u64) -> Self {
        EllipticCurveCrypto {
            curve,
            generator,
            order,
        }
    }
    
    pub fn generate_key_pair(&self) -> (u64, EllipticPoint) {
        let mut rng = rand::thread_rng();
        let private_key = rng.gen_range(1..self.order);
        let public_key = self.curve.scalar_multiply(&self.generator, private_key);
        
        (private_key, public_key)
    }
    
    pub fn ecdh(&self, private_key: u64, public_key: &EllipticPoint) -> EllipticPoint {
        self.curve.scalar_multiply(public_key, private_key)
    }
    
    pub fn ecdsa_sign(&self, message: &[u8], private_key: u64) -> (u64, u64) {
        let mut rng = rand::thread_rng();
        let message_hash = self.hash_message(message);
        
        loop {
            let k = rng.gen_range(1..self.order);
            let k_point = self.curve.scalar_multiply(&self.generator, k);
            
            if k_point.x() == 0 {
                continue;
            }
            
            let r = k_point.x() % self.order;
            if r == 0 {
                continue;
            }
            
            let k_inv = self.modular_inverse(k, self.order);
            let s = (k_inv * (message_hash + private_key * r)) % self.order;
            
            if s != 0 {
                return (r, s);
            }
        }
    }
    
    pub fn ecdsa_verify(&self, message: &[u8], signature: (u64, u64), public_key: &EllipticPoint) -> bool {
        let (r, s) = signature;
        
        if r == 0 || r >= self.order || s == 0 || s >= self.order {
            return false;
        }
        
        let message_hash = self.hash_message(message);
        let w = self.modular_inverse(s, self.order);
        let u1 = (message_hash * w) % self.order;
        let u2 = (r * w) % self.order;
        
        let point1 = self.curve.scalar_multiply(&self.generator, u1);
        let point2 = self.curve.scalar_multiply(public_key, u2);
        let sum = self.curve.add_points(&point1, &point2);
        
        if sum.is_infinity() {
            return false;
        }
        
        sum.x() % self.order == r
    }
    
    fn hash_message(&self, message: &[u8]) -> u64 {
        // 简化的哈希函数
        let mut hash = 0u64;
        for &byte in message {
            hash = hash.wrapping_add(byte as u64);
            hash = hash.wrapping_mul(31);
        }
        hash % self.order
    }
    
    fn modular_inverse(&self, a: u64, modulus: u64) -> u64 {
        let congruence = CongruenceTheory::new(modulus);
        congruence.multiplicative_inverse(a).unwrap()
    }
    
    pub fn baby_step_giant_step(&self, point: &EllipticPoint, target: &EllipticPoint) -> Option<u64> {
        let m = (self.order as f64).sqrt().ceil() as u64;
        
        // Baby steps
        let mut baby_steps = HashMap::new();
        let mut current = self.curve.point_at_infinity.clone();
        
        for j in 0..m {
            baby_steps.insert(current.clone(), j);
            current = self.curve.add_points(&current, point);
        }
        
        // Giant steps
        let factor = self.curve.scalar_multiply(point, m);
        let mut giant_step = target.clone();
        
        for i in 0..m {
            if let Some(&j) = baby_steps.get(&giant_step) {
                return Some(i * m + j);
            }
            giant_step = self.curve.add_points(&giant_step, &factor);
        }
        
        None
    }
}
```

## 5. 格理论

### 5.1 格基本概念

**定义 5.1.1 (格)**
格是ℝⁿ中的离散加法子群。

**算法 5.1.1 (格算法)**

```rust
pub struct Lattice {
    basis: Vec<Vector>,
    dimension: usize,
}

impl Lattice {
    pub fn new(basis: Vec<Vector>) -> Self {
        let dimension = if !basis.is_empty() { basis[0].dimension() } else { 0 };
        Lattice { basis, dimension }
    }
    
    pub fn dimension(&self) -> usize {
        self.dimension
    }
    
    pub fn rank(&self) -> usize {
        self.basis.len()
    }
    
    pub fn determinant(&self) -> f64 {
        if self.basis.is_empty() {
            return 0.0;
        }
        
        let matrix = self.gram_matrix();
        matrix.determinant().sqrt()
    }
    
    pub fn gram_matrix(&self) -> Matrix {
        let n = self.basis.len();
        let mut matrix = Matrix::new(n, n);
        
        for i in 0..n {
            for j in 0..n {
                matrix.set(i, j, self.basis[i].dot_product(&self.basis[j]));
            }
        }
        
        matrix
    }
    
    pub fn shortest_vector(&self) -> Option<Vector> {
        if self.basis.is_empty() {
            return None;
        }
        
        let mut shortest = self.basis[0].clone();
        let mut min_length = shortest.length_squared();
        
        for vector in &self.basis {
            let length = vector.length_squared();
            if length < min_length {
                min_length = length;
                shortest = vector.clone();
            }
        }
        
        Some(shortest)
    }
    
    pub fn lll_reduction(&mut self) {
        let mut basis = self.basis.clone();
        let n = basis.len();
        
        let mut k = 1;
        while k < n {
            // Gram-Schmidt orthogonalization
            for j in (0..k).rev() {
                let mu = basis[k].projection_coefficient(&basis[j]);
                if mu.abs() > 0.5 {
                    basis[k] = basis[k].subtract(&basis[j].scale(mu));
                }
            }
            
            // Lovász condition
            let k_minus_1 = if k > 0 { k - 1 } else { 0 };
            let projected_k = basis[k].projection(&basis[k_minus_1]);
            let projected_k_minus_1 = basis[k_minus_1].projection(&basis[k_minus_1]);
            
            if projected_k.length_squared() < (0.75 - 0.25) * projected_k_minus_1.length_squared() {
                // Swap basis vectors
                basis.swap(k, k - 1);
                k = if k > 1 { k - 1 } else { 1 };
            } else {
                k += 1;
            }
        }
        
        self.basis = basis;
    }
    
    pub fn closest_vector(&self, target: &Vector) -> Option<Vector> {
        if self.basis.is_empty() {
            return None;
        }
        
        // 使用Babai's nearest plane algorithm
        let mut reduced_basis = self.basis.clone();
        let mut lattice = Lattice::new(reduced_basis);
        lattice.lll_reduction();
        
        let mut closest = target.clone();
        
        for i in (0..lattice.basis.len()).rev() {
            let coefficient = closest.projection_coefficient(&lattice.basis[i]);
            let rounded = coefficient.round();
            closest = closest.subtract(&lattice.basis[i].scale(rounded));
        }
        
        Some(target.subtract(&closest))
    }
}

pub struct Vector {
    components: Vec<f64>,
}

impl Vector {
    pub fn new(components: Vec<f64>) -> Self {
        Vector { components }
    }
    
    pub fn dimension(&self) -> usize {
        self.components.len()
    }
    
    pub fn length_squared(&self) -> f64 {
        self.components.iter().map(|&x| x * x).sum()
    }
    
    pub fn length(&self) -> f64 {
        self.length_squared().sqrt()
    }
    
    pub fn dot_product(&self, other: &Vector) -> f64 {
        self.components.iter()
            .zip(other.components.iter())
            .map(|(&a, &b)| a * b)
            .sum()
    }
    
    pub fn add(&self, other: &Vector) -> Vector {
        let components: Vec<f64> = self.components.iter()
            .zip(other.components.iter())
            .map(|(&a, &b)| a + b)
            .collect();
        Vector::new(components)
    }
    
    pub fn subtract(&self, other: &Vector) -> Vector {
        let components: Vec<f64> = self.components.iter()
            .zip(other.components.iter())
            .map(|(&a, &b)| a - b)
            .collect();
        Vector::new(components)
    }
    
    pub fn scale(&self, scalar: f64) -> Vector {
        let components: Vec<f64> = self.components.iter()
            .map(|&x| x * scalar)
            .collect();
        Vector::new(components)
    }
    
    pub fn projection_coefficient(&self, other: &Vector) -> f64 {
        self.dot_product(other) / other.dot_product(other)
    }
    
    pub fn projection(&self, other: &Vector) -> Vector {
        let coefficient = self.projection_coefficient(other);
        other.scale(coefficient)
    }
}

impl Clone for Vector {
    fn clone(&self) -> Self {
        Vector::new(self.components.clone())
    }
}

pub struct Matrix {
    data: Vec<Vec<f64>>,
    rows: usize,
    cols: usize,
}

impl Matrix {
    pub fn new(rows: usize, cols: usize) -> Self {
        let data = vec![vec![0.0; cols]; rows];
        Matrix { data, rows, cols }
    }
    
    pub fn set(&mut self, row: usize, col: usize, value: f64) {
        if row < self.rows && col < self.cols {
            self.data[row][col] = value;
        }
    }
    
    pub fn get(&self, row: usize, col: usize) -> f64 {
        if row < self.rows && col < self.cols {
            self.data[row][col]
        } else {
            0.0
        }
    }
    
    pub fn determinant(&self) -> f64 {
        if self.rows != self.cols {
            return 0.0;
        }
        
        if self.rows == 1 {
            return self.data[0][0];
        }
        
        if self.rows == 2 {
            return self.data[0][0] * self.data[1][1] - self.data[0][1] * self.data[1][0];
        }
        
        // 递归计算行列式
        let mut det = 0.0;
        for j in 0..self.cols {
            let minor = self.minor(0, j);
            det += self.data[0][j] * minor.determinant() * if j % 2 == 0 { 1.0 } else { -1.0 };
        }
        
        det
    }
    
    fn minor(&self, row: usize, col: usize) -> Matrix {
        let mut minor = Matrix::new(self.rows - 1, self.cols - 1);
        let mut minor_row = 0;
        
        for i in 0..self.rows {
            if i == row {
                continue;
            }
            
            let mut minor_col = 0;
            for j in 0..self.cols {
                if j == col {
                    continue;
                }
                
                minor.set(minor_row, minor_col, self.data[i][j]);
                minor_col += 1;
            }
            minor_row += 1;
        }
        
        minor
    }
}
```

## 6. 未来发展方向

### 6.1 理论发展方向

1. **代数数论**：研究代数数论理论
2. **解析数论**：发展解析数论
3. **组合数论**：研究组合数论
4. **计算数论**：发展计算数论

### 6.2 技术发展方向

1. **后量子密码学**：开发后量子密码算法
2. **格密码学**：发展格密码学技术
3. **椭圆曲线密码学**：改进椭圆曲线算法
4. **同态加密**：研究同态加密技术

### 6.3 应用发展方向

1. **区块链密码学**：应用数论于区块链
2. **零知识证明**：应用数论于零知识证明
3. **多方计算**：应用数论于多方计算
4. **量子安全**：应用数论于量子安全

## 总结

本文档建立了完整的Web3数论与算术框架，包括：

1. **素数理论**：建立了素数基本性质和分布理论
2. **同余理论**：提供了同余基本概念和欧拉函数理论
3. **二次剩余**：构建了二次剩余和平方剩余理论
4. **椭圆曲线**：建立了椭圆曲线基本概念和密码学应用
5. **格理论**：提供了格基本概念和算法
6. **发展方向**：指明了理论、技术、应用发展方向

这个理论框架为Web3系统的密码学和数学基础提供了科学基础，有助于构建更加安全、高效的Web3系统。
