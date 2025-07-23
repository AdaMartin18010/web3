# 2.9.1.2.3.1.1 zkEVM电路（zkEVM Circuit）

## 2.9.1.2.3.1.1.1 理论 Theoretical Foundation

- **定义 Definition**：
  - zkEVM电路是将EVM操作映射为零知识证明友好型电路的设计，实现EVM兼容的高效证明。
  - zkEVM Circuit is the design that maps EVM operations into zero-knowledge proof-friendly circuits, enabling efficient EVM-compatible proofs.
- **核心原理 Core Principles**：
  - 零知识证明、EVM操作建模、有效性证明、分层电路、链下执行、链上验证
  - 可扩展性、安全性、即时最终性、去信任性

## 2.9.1.2.3.1.1.2 技术 Technology

- **代表技术 Representative Technologies**：
  - zkEVM电路、有效性证明合约、分层电路设计、链下执行引擎、数据可用性层
  - 验证合约、状态同步、链上验证、EVM兼容性

## 2.9.1.2.3.1.1.3 应用 Application

- **典型应用 Typical Applications**：
  - Polygon zkEVM、以太坊Layer2、DeFi扩容、NFT高性能交易、链上游戏、EVM兼容DApp

## 2.9.1.2.3.1.1.4 语义 Semantic Model

- **语义抽象 Semantic Abstraction**：
  - 电路（Circuit）、操作（Operation）、证明（Proof）、状态（State）、EVM、主链（Mainchain）
  - 语义映射：电路、状态、EVM、主链为对象，操作、证明为态射，电路为对象间关系

## 2.9.1.2.3.1.1.5 关联 Interrelation/Mapping

- **与zkEVM其他子层的关联 Relation to Other Sub-layers**：
  - zkEVM电路为zkEVM提供EVM操作的高效证明能力，与有效性证明等互补
  - 与主链共识、数据可用性层等紧密结合，提升整体性能
- **与理论的递归关系 Recursive Theoretical Relation**：
  - zkEVM电路理论递归嵌套于zkEVM与ZK Rollup证明系统，为Web3生态提供EVM操作的高效证明语义

---

> 说明：本节为zkEVM子主题zkEVM电路的递归分析，后续可继续细分分层电路、操作建模等子主题，每层均采用五元结构与中英双语解释。
