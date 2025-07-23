# 2.5 拜占庭容错（Byzantine Fault Tolerance, BFT）

## 2.5.1 理论 Theoretical Foundation

- **定义 Definition**：
  - 拜占庭容错是一类能够容忍部分节点作恶或失效的分布式共识理论基础。
  - Byzantine Fault Tolerance (BFT) is a class of distributed consensus theory that tolerates a fraction of faulty or malicious nodes.
- **核心原理 Core Principles**：
  - 拜占庭将军问题、容错阈值、消息签名、状态复制、投票机制、确定性共识
  - 节点身份、主节点轮换、分布式一致性

## 2.5.2 技术 Technology

- **代表技术 Representative Technologies**：
  - BFT协议、消息签名、状态机复制、分布式投票、主节点选举、容错机制
  - Tendermint、HotStuff、Zilliqa、Cosmos BFT

## 2.5.3 应用 Application

- **典型应用 Typical Applications**：
  - 联盟链、许可链、企业区块链、DAO治理、分布式数据库、DeFi高性能链

## 2.5.4 语义 Semantic Model

- **语义抽象 Semantic Abstraction**：
  - 节点（Node）、消息（Message）、投票（Vote）、状态（State）、共识（Consensus）、容错（Fault Tolerance）
  - 语义映射：节点、状态为对象，消息、投票为态射，共识、容错为对象间关系

## 2.5.5 关联 Interrelation/Mapping

- **与共识机制其他子层的关联 Relation to Other Sub-layers**：
  - BFT为PBFT、Tendermint等提供理论基础，支撑高安全性区块链架构
  - 与PoS、DPoS等机制互补，提升系统鲁棒性
- **与理论的递归关系 Recursive Theoretical Relation**：
  - BFT理论递归嵌套于共识机制与分布式系统理论，为Web3生态提供拜占庭容错与鲁棒性语义

---

> 说明：本节为共识机制子主题BFT的递归分析，后续可继续细分Tendermint、HotStuff等子主题，每层均采用五元结构与中英双语解释。
