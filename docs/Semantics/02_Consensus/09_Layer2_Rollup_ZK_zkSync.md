# 2.9.1.2.1 zkSync

## 2.9.1.2.1.1 理论 Theoretical Foundation

- **定义 Definition**：
  - zkSync是一种基于ZK Rollup的以太坊Layer2扩容协议，采用零知识证明批量验证链下交易。
  - zkSync is an Ethereum Layer2 scaling protocol based on ZK Rollup, using zero-knowledge proofs to batch-verify off-chain transactions.
- **核心原理 Core Principles**：
  - 零知识证明、有效性证明、链下批量处理、链上验证、数据可用性、ZK电路
  - 可扩展性、安全性、即时最终性、去信任性

## 2.9.1.2.1.2 技术 Technology

- **代表技术 Representative Technologies**：
  - zkSync Rollup、zkEVM、有效性证明合约、ZK电路、链下执行引擎、数据可用性层
  - 验证合约、状态同步、链上验证、ZK SNARK/STARK

## 2.9.1.2.1.3 应用 Application

- **典型应用 Typical Applications**：
  - 以太坊Layer2、DeFi扩容、NFT高性能交易、链上游戏、支付通道

## 2.9.1.2.1.4 语义 Semantic Model

- **语义抽象 Semantic Abstraction**：
  - 批次（Batch）、有效性证明（Validity Proof）、状态（State）、主链（Mainchain）、ZK电路（ZK Circuit）
  - 语义映射：批次、状态、主链、ZK电路为对象，有效性证明为态射，ZK电路为对象间关系

## 2.9.1.2.1.5 关联 Interrelation/Mapping

- **与ZK Rollup其他子层的关联 Relation to Other Sub-layers**：
  - zkSync为ZK Rollup扩容提供高安全性与即时最终性，与StarkNet等互补
  - 与主链共识、数据可用性层等紧密结合，提升整体性能
- **与理论的递归关系 Recursive Theoretical Relation**：
  - zkSync理论递归嵌套于ZK Rollup与Layer2共识机制，为Web3生态提供高安全性与零知识语义

---

> 说明：本节为ZK Rollup子主题zkSync的递归分析，后续可继续细分zkEVM等子主题，每层均采用五元结构与中英双语解释。
