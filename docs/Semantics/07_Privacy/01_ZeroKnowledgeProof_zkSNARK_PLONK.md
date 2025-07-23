# 7.1.1.2 PLONK

## 7.1.1.2.1 理论 Theoretical Foundation

- **定义 Definition**：
  - PLONK是一种通用、无需可信设置的zk-SNARK证明系统，支持高效证明聚合与递归。
  - PLONK is a universal, trustless-setup zk-SNARK proof system supporting efficient proof aggregation and recursion.
- **核心原理 Core Principles**：
  - 通用性、无需可信设置、证明聚合、递归证明、FFT优化、门多项式、约束系统
  - 证明系统、验证密钥、证明密钥、门电路建模

## 7.1.1.2 技术 Technology

- **代表技术 Representative Technologies**：
  - PLONK算法、门多项式、FFT、递归证明、证明聚合、通用电路、Halo2、以太坊隐私扩展
  - zk-SNARK电路、分布式证明生成、门电路优化

## 7.1.1.3 应用 Application

- **典型应用 Typical Applications**：
  - 区块链隐私协议、ZK Rollup、DeFi隐私、链上身份认证、DAO隐私投票、合规隐私证明

## 7.1.1.4 语义 Semantic Model

- **语义抽象 Semantic Abstraction**：
  - 证明（Proof）、电路（Circuit）、门（Gate）、验证密钥（Verification Key）、证明密钥（Proving Key）、门多项式（Gate Polynomial）
  - 语义映射：证明、电路、密钥、门为对象，约束、验证为态射，证明过程为对象间关系

## 7.1.1.5 关联 Interrelation/Mapping

- **与zk-SNARK其他子层的关联 Relation to Other Sub-layers**：
  - PLONK为zk-SNARK提供无需可信设置与高效聚合能力，与Groth16、Sonic等互补
  - 与加密理论、分布式账本等紧密结合，提升整体隐私性与可扩展性
- **与理论的递归关系 Recursive Theoretical Relation**：
  - PLONK理论递归嵌套于zk-SNARK与零知识证明理论，为Web3生态提供高效隐私与可验证性语义

---

> 说明：本节为zk-SNARK子主题PLONK的递归分析，后续可继续细分门多项式、递归证明等子主题，每层均采用五元结构与中英双语解释。
