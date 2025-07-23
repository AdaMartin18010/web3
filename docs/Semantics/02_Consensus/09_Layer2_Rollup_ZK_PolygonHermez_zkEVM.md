# 2.9.1.2.3.1 zkEVM

## 2.9.1.2.3.1.1 理论 Theoretical Foundation

- **定义 Definition**：
  - zkEVM是一种兼容以太坊虚拟机（EVM）的零知识证明系统，实现EVM操作的可验证性与高效性。
  - zkEVM is a zero-knowledge proof system compatible with the Ethereum Virtual Machine (EVM), enabling verifiability and efficiency of EVM operations.
- **核心原理 Core Principles**：
  - 零知识证明、EVM兼容、有效性证明、链下执行、链上验证、数据可用性
  - 可扩展性、安全性、即时最终性、去信任性

## 2.9.1.2.3.1.2 技术 Technology

- **代表技术 Representative Technologies**：
  - Polygon zkEVM、zkEVM电路、有效性证明合约、链下执行引擎、数据可用性层
  - 验证合约、状态同步、链上验证、EVM兼容性

## 2.9.1.2.3.1.3 应用 Application

- **典型应用 Typical Applications**：
  - 以太坊Layer2、DeFi扩容、NFT高性能交易、链上游戏、支付通道、EVM兼容DApp

## 2.9.1.2.3.1.4 语义 Semantic Model

- **语义抽象 Semantic Abstraction**：
  - 程序（Program）、有效性证明（Validity Proof）、状态（State）、EVM、主链（Mainchain）、电路（Circuit）
  - 语义映射：程序、状态、EVM、主链为对象，有效性证明、执行为态射，电路为对象间关系

## 2.9.1.2.3.1.5 关联 Interrelation/Mapping

- **与Polygon Hermez其他子层的关联 Relation to Other Sub-layers**：
  - zkEVM为Polygon Hermez提供EVM兼容与高效证明能力，与ZK电路等互补
  - 与主链共识、数据可用性层等紧密结合，提升整体性能
- **与理论的递归关系 Recursive Theoretical Relation**：
  - zkEVM理论递归嵌套于Polygon Hermez与ZK Rollup证明系统，为Web3生态提供EVM兼容与高效证明语义

---

> 说明：本节为Polygon Hermez子主题zkEVM的递归分析，后续可继续细分zkEVM电路等子主题，每层均采用五元结构与中英双语解释。
