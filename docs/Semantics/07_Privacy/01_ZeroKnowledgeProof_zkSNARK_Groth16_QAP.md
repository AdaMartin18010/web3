# 7.1.1.1.1 QAP（Quadratic Arithmetic Programs）

## 7.1.1.1.1.1 理论 Theoretical Foundation

- **定义 Definition**：
  - QAP是一种用于将计算电路转换为多项式约束系统的数学工具，是zk-SNARK（如Groth16）证明系统的核心基础。
  - QAP is a mathematical tool for converting computational circuits into polynomial constraint systems, serving as the core foundation of zk-SNARK proof systems like Groth16.
- **核心原理 Core Principles**：
  - 多项式约束、算术电路、零知识证明、约束系统、可验证性、简洁性
  - 输入分配、约束多项式、验证多项式、根检测

## 7.1.1.1.1.2 技术 Technology

- **代表技术 Representative Technologies**：
  - QAP构造、R1CS到QAP转换、Groth16算法、约束系统优化、证明生成与验证
  - 多项式承诺、FFT优化、证明友好型电路

## 7.1.1.1.1.3 应用 Application

- **典型应用 Typical Applications**：
  - zk-SNARK证明生成、Zcash匿名交易、区块链隐私协议、ZK Rollup、链上合规证明

## 7.1.1.1.1.4 语义 Semantic Model

- **语义抽象 Semantic Abstraction**：
  - 多项式（Polynomial）、约束（Constraint）、电路（Circuit）、输入分配（Assignment）、验证（Verification）
  - 语义映射：多项式、约束、电路为对象，输入分配、验证为态射，约束系统为对象间关系

## 7.1.1.1.1.5 关联 Interrelation/Mapping

- **与Groth16其他子层的关联 Relation to Other Sub-layers**：
  - QAP为Groth16和zk-SNARK提供电路到证明的核心桥梁，与R1CS等互补
  - 与多项式承诺、FFT优化等技术紧密结合，提升证明效率
- **与理论的递归关系 Recursive Theoretical Relation**：
  - QAP理论递归嵌套于Groth16与zk-SNARK证明系统，为Web3生态提供高效可验证性语义

---

> 说明：本节为Groth16子主题QAP的递归分析，后续可继续细分R1CS、约束系统等子主题，每层均采用五元结构与中英双语解释。
