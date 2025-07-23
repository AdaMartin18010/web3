# 7.1.1.1.2 R1CS（Rank-1 Constraint System）

## 7.1.1.1.2.1 理论 Theoretical Foundation

- **定义 Definition**：
  - R1CS是一种将计算电路建模为一组乘法和加法约束的数学结构，是zk-SNARK（如Groth16）证明系统的标准输入格式。
  - R1CS is a mathematical structure that models computational circuits as a set of multiplication and addition constraints, serving as the standard input format for zk-SNARK proof systems like Groth16.
- **核心原理 Core Principles**：
  - 乘法约束、加法约束、稀疏性、可组合性、可验证性、简洁性
  - 电路建模、输入分配、约束系统、零知识证明

## 7.1.1.1.2.2 技术 Technology

- **代表技术 Representative Technologies**：
  - R1CS建模、QAP转换、Groth16算法、约束系统优化、证明生成与验证
  - 多项式承诺、证明友好型电路、稀疏矩阵优化

## 7.1.1.1.2.3 应用 Application

- **典型应用 Typical Applications**：
  - zk-SNARK证明生成、Zcash匿名交易、区块链隐私协议、ZK Rollup、链上合规证明

## 7.1.1.1.2.4 语义 Semantic Model

- **语义抽象 Semantic Abstraction**：
  - 约束（Constraint）、电路（Circuit）、输入分配（Assignment）、验证（Verification）、矩阵（Matrix）
  - 语义映射：约束、电路、矩阵为对象，输入分配、验证为态射，约束系统为对象间关系

## 7.1.1.1.2.5 关联 Interrelation/Mapping

- **与Groth16其他子层的关联 Relation to Other Sub-layers**：
  - R1CS为Groth16和zk-SNARK提供电路建模与约束表达能力，与QAP等互补
  - 与多项式承诺、稀疏矩阵优化等技术紧密结合，提升证明效率
- **与理论的递归关系 Recursive Theoretical Relation**：
  - R1CS理论递归嵌套于Groth16与zk-SNARK证明系统，为Web3生态提供高效可验证性语义

---

> 说明：本节为Groth16子主题R1CS的递归分析，后续可继续细分约束系统、多项式承诺等子主题，每层均采用五元结构与中英双语解释。
