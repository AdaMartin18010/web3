# 1.2.1 IPFS（InterPlanetary File System）

## 1.2.1.1 理论 Theoretical Foundation

- **定义 Definition**：
  - IPFS是一种基于内容寻址、分布式哈希表和P2P网络的去中心化文件存储与分发协议。
  - IPFS is a decentralized file storage and distribution protocol based on content addressing, distributed hash tables, and P2P networks.
- **核心原理 Core Principles**：
  - 内容寻址、Merkle DAG、分布式哈希表（DHT）、P2P网络、版本控制、去中心化
  - 数据不可篡改性、冗余备份、可扩展性

## 1.2.1.2 技术 Technology

- **代表技术 Representative Technologies**：
  - IPFS协议、libp2p、Merkle DAG、IPNS、Bitswap、分布式节点发现
  - 数据块分片、内容寻址哈希、节点同步

## 1.2.1.3 应用 Application

- **典型应用 Typical Applications**：
  - 区块链数据存储、NFT内容分发、去中心化网站（dWeb）、分布式备份、链上大文件存证

## 1.2.1.4 语义 Semantic Model

- **语义抽象 Semantic Abstraction**：
  - 数据块（Block）、内容哈希（Content Hash）、节点（Node）、DAG、分片（Shard）、路径（Path）
  - 语义映射：数据块与节点为对象，内容寻址与同步为态射，DAG为对象间关系

## 1.2.1.5 关联 Interrelation/Mapping

- **与分布式存储其他子层的关联 Relation to Other Sub-layers**：
  - IPFS为分布式存储和区块链提供高效的内容寻址与分发能力
  - 与Filecoin、P2P网络、区块链账本等紧密结合
- **与理论的递归关系 Recursive Theoretical Relation**：
  - IPFS理论递归嵌套于分布式存储与分布式系统理论，为Web3生态提供高效内容分发语义

---

> 说明：本节为分布式存储子主题IPFS的递归分析，后续可继续细分Filecoin、Arweave等子主题，每层均采用五元结构与中英双语解释。
