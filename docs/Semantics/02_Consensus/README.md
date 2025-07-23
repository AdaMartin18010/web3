# 2. 共识机制（Consensus Mechanisms）

## 2.1 理论 Theoretical Foundation

- **定义 Definition**：
  - 共识机制是分布式系统中各节点在无信任环境下就系统状态达成一致的协议集合。
  - Consensus mechanisms are protocols that enable nodes in a distributed system to reach agreement on the system state in a trustless environment.
- **核心原理 Core Principles**：
  - 拜占庭容错（Byzantine Fault Tolerance, BFT）
  - 一致性、安全性、活性、容错性
  - 概率性与确定性共识

## 2.2 技术 Technology

- **代表技术 Representative Technologies**：
  - 工作量证明（Proof of Work, PoW）
  - 权益证明（Proof of Stake, PoS）
  - 委托权益证明（DPoS）、实用拜占庭容错（PBFT）、Raft、Tendermint
  - 混合共识、分片共识、Layer2共识

## 2.3 应用 Application

- **典型应用 Typical Applications**：
  - 区块链账本的安全写入与同步
  - DAO组织的链上投票与决策
  - 跨链桥的状态一致性
  - DeFi协议的去信任结算

## 2.4 语义 Semantic Model

- **语义抽象 Semantic Abstraction**：
  - 节点（Node）、提案（Proposal）、投票（Vote）、区块（Block）、状态转移（State Transition）
  - 一致性语义（如最终一致性、强一致性）、拜占庭节点、诚实节点
  - 语义映射：共识过程抽象为范畴论中的对象（状态）与态射（状态转移/投票）

## 2.5 关联 Interrelation/Mapping

- **与上下层技术的关联 Relation to Other Layers**：
  - 共识机制是区块链账本、智能合约、DAO等上层应用的安全与信任基础
  - 与分布式系统理论紧密耦合，直接影响系统的可扩展性与安全性
- **与理论的递归关系 Recursive Theoretical Relation**：
  - 共识机制理论递归嵌套于分布式系统理论之上，为Web3生态的信任与协作提供核心支撑

---

> 说明：本节为Web3技术栈递归分析的第二层，后续将继续递归展开加密理论、区块链账本、智能合约等上层技术，每层均严格采用五元结构与中英双语解释，并支持中断后持续递归扩展。
