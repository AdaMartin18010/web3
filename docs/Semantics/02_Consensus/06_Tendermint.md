# 2.6 Tendermint

## 2.6.1 理论 Theoretical Foundation

- **定义 Definition**：
  - Tendermint是一种基于BFT的高性能区块链共识算法，结合了投票机制与状态机复制。
  - Tendermint is a high-performance blockchain consensus algorithm based on BFT, combining voting mechanisms and state machine replication.
- **核心原理 Core Principles**：
  - BFT共识、投票轮次、区块提议、状态机复制、惩罚机制、主节点轮换
  - 确定性共识、分布式一致性、链上治理

## 2.6.2 技术 Technology

- **代表技术 Representative Technologies**：
  - Tendermint Core、Cosmos SDK、区块提议、投票轮次、状态同步、惩罚与奖励机制
  - 主节点轮换、链上治理、分布式签名

## 2.6.3 应用 Application

- **典型应用 Typical Applications**：
  - Cosmos、Binance Chain、IRISnet等高性能公链
  - DAO治理、DeFi协议、分布式数据库

## 2.6.4 语义 Semantic Model

- **语义抽象 Semantic Abstraction**：
  - 验证者（Validator）、区块（Block）、投票（Vote）、状态（State）、轮次（Round）、共识（Consensus）
  - 语义映射：验证者、区块、状态为对象，投票、轮次为态射，共识为对象间关系

## 2.6.5 关联 Interrelation/Mapping

- **与共识机制其他子层的关联 Relation to Other Sub-layers**：
  - Tendermint为Cosmos等高性能链提供核心共识基础
  - 与BFT、PoS、DPoS等机制互补，支撑多样化区块链架构
- **与理论的递归关系 Recursive Theoretical Relation**：
  - Tendermint理论递归嵌套于BFT与共识机制理论，为Web3生态提供高性能与确定性语义

---

> 说明：本节为共识机制子主题Tendermint的递归分析，后续可继续细分Cosmos、链上治理等子主题，每层均采用五元结构与中英双语解释。
