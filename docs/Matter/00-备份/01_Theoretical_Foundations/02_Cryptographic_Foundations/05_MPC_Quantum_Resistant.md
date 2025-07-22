# 多方安全计算与抗量子密码 (MPC & Quantum-Resistant Cryptography)

## 概述

多方安全计算（MPC）和抗量子密码学是Web3系统未来安全与隐私的关键方向。

## 1. 多方安全计算（MPC）

**定义 1.1**（MPC）：
多个参与方在不泄露各自输入的前提下，安全地联合计算函数$f(x_1, ..., x_n)$。

- 典型协议：Shamir秘密共享、Yao混淆电路、BGW协议
- 应用：链上隐私计算、去信任化协作、DAO机密投票

**定理 1.1**（安全性）：
若协议满足正确性和隐私性，则任何参与方无法获得除输出外的额外信息。

## 2. 抗量子密码学

**定义 2.1**（抗量子密码）：
在量子计算机下仍安全的密码算法。

- 典型算法：格密码（LWE/NTRU）、哈希签名（XMSS）、多变量密码、编码密码、同源性密码
- 应用：抗量子区块链、抗量子签名、抗量子密钥交换

**定理 2.2**（LWE难题）：
学习带误差问题（LWE）在经典和量子计算下都难以求解。

## 3. 应用场景

- 区块链跨链桥的安全多方签名
- 隐私DeFi协议的链下协作
- 抗量子钱包与签名
- 长期安全的数字身份与资产

## 4. Rust代码示例

### Shamir秘密共享（简化版）

```rust
fn shamir_split(secret: u8, n: u8, t: u8) -> Vec<(u8, u8)> {
    // 仅演示，实际应用需用大数和有限域
    let coeff = vec![secret, 123, 231]; // 随机系数
    (1..=n).map(|x| {
        let mut y = 0u8;
        let mut pow = 1u8;
        for &c in &coeff[..t as usize] {
            y = y.wrapping_add(c.wrapping_mul(pow));
            pow = pow.wrapping_mul(x);
        }
        (x, y)
    }).collect()
}

fn main() {
    let shares = shamir_split(42, 5, 3);
    println!("Shamir秘密共享份额: {:?}", shares);
}
```

## 相关链接

- [零知识证明与隐私保护](04_Zero_Knowledge_Privacy.md)
- [密码学基础总览](../)

---

*多方安全计算与抗量子密码为Web3系统的未来安全和隐私提供前沿保障。*
