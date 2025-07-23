# 1.2 分布式存储（Distributed Storage）

## 1.2.1 理论 Theoretical Foundation

- **定义 Definition**：
  - 分布式存储是将数据分散存储在多个节点上，通过冗余与分片实现高可用与容错。
  - Distributed storage refers to storing data across multiple nodes, achieving high availability and fault tolerance through redundancy and sharding.
- **核心原理 Core Principles**：
  - 数据分片、冗余备份、一致性哈希、数据可用性、容错性、可扩展性
  - 副本管理、数据同步、纠删码

## 1.2.2 技术 Technology

- **代表技术 Representative Technologies**：
  - IPFS、Filecoin、Storj、Arweave、Sia、Swarm
  - 分布式哈希表（DHT）、分布式文件系统（DFS）、纠删码存储

## 1.2.3 应用 Application

- **典型应用 Typical Applications**：
  - 区块链数据存储、去中心化内容分发、分布式备份、链上大文件存证、Web3数据市场

## 1.2.4 语义 Semantic Model

- **语义抽象 Semantic Abstraction**：
  - 数据块（Block）、分片（Shard）、副本（Replica）、节点（Node）、一致性（Consistency）
  - 语义映射：数据块与节点为对象，存储与同步为态射，冗余与分片为对象间关系

## 1.2.5 关联 Interrelation/Mapping

- **与分布式系统其他子层的关联 Relation to Other Sub-layers**：
  - 分布式存储为区块链账本、智能合约等提供底层数据支撑
  - 与P2P网络、分布式消息队列、共识机制等紧密结合
- **与理论的递归关系 Recursive Theoretical Relation**：
  - 分布式存储理论递归嵌套于分布式系统理论，为Web3生态提供高可用与弹性数据语义

---

> 说明：本节为分布式系统子主题分布式存储的递归分析，后续可继续细分分布式消息队列等子主题，每层均采用五元结构与中英双语解释。
