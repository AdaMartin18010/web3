# 2.9.1.1 Optimistic Rollup

## 2.9.1.1.1 理论 Theoretical Foundation

- **定义 Definition**：
  - Optimistic Rollup是一种假设链下交易有效、仅在有争议时才验证的Layer2扩容方案。
  - Optimistic Rollup is a Layer2 scaling solution that assumes off-chain transactions are valid and only verifies them in case of disputes.
- **核心原理 Core Principles**：
  - 乐观执行、欺诈证明、链下批量处理、链上验证、数据可用性、争议期
  - 可扩展性、安全性、最终性、去信任性

## 2.9.1.1.2 技术 Technology

- **代表技术 Representative Technologies**：
  - Arbitrum、Optimism、欺诈证明合约、争议期机制、链下执行引擎、数据可用性层
  - 验证合约、状态同步、链上挑战

## 2.9.1.1.3 应用 Application

- **典型应用 Typical Applications**：
  - 以太坊Layer2、DeFi扩容、NFT高性能交易、链上游戏、支付通道

## 2.9.1.1.4 语义 Semantic Model

- **语义抽象 Semantic Abstraction**：
  - 批次（Batch）、欺诈证明（Fraud Proof）、争议期（Challenge Period）、状态（State）、主链（Mainchain）
  - 语义映射：批次、状态、主链为对象，欺诈证明、争议为态射，争议期为对象间关系

## 2.9.1.1.5 关联 Interrelation/Mapping

- **与Rollup其他子层的关联 Relation to Other Sub-layers**：
  - Optimistic Rollup为Rollup扩容提供低成本高扩展性，与ZK Rollup等互补
  - 与主链共识、数据可用性层等紧密结合，提升整体性能
- **与理论的递归关系 Recursive Theoretical Relation**：
  - Optimistic Rollup理论递归嵌套于Rollup与Layer2共识机制，为Web3生态提供高扩展性与争议解决语义

---

> 说明：本节为Rollup子主题Optimistic Rollup的递归分析，后续可继续细分Arbitrum、Optimism等子主题，每层均采用五元结构与中英双语解释。
