# 2.9.3 数据可用性（Data Availability）

## 2.9.3.1 理论 Theoretical Foundation

- **定义 Definition**：
  - 数据可用性是指Layer2扩容方案中，链下数据能被主链或验证者完整获取和验证的能力。
  - Data availability refers to the ability in Layer2 scaling solutions for off-chain data to be fully accessible and verifiable by the main chain or validators.
- **核心原理 Core Principles**：
  - 数据分片、冗余存储、可用性证明、采样验证、欺诈证明、数据恢复
  - 安全性、可扩展性、去信任性、最终性

## 2.9.3.2 技术 Technology

- **代表技术 Representative Technologies**：
  - Celestia、EigenDA、DAS（Data Availability Sampling）、KZG承诺、冗余编码、分片存储
  - 数据可用性层、采样验证、欺诈证明、数据恢复协议

## 2.9.3.3 应用 Application

- **典型应用 Typical Applications**：
  - Rollup数据可用性、Layer2扩容、分片区块链、链下数据市场、DeFi高性能应用

## 2.9.3.4 语义 Semantic Model

- **语义抽象 Semantic Abstraction**：
  - 数据块（Data Block）、可用性证明（Availability Proof）、采样（Sampling）、验证者（Validator）、恢复（Recovery）、主链（Mainchain）
  - 语义映射：数据块、主链、验证者为对象，采样、证明、恢复为态射，可用性为对象间关系

## 2.9.3.5 关联 Interrelation/Mapping

- **与Layer2其他子层的关联 Relation to Other Sub-layers**：
  - 数据可用性为Rollup、状态通道等Layer2方案提供安全与可扩展性保障
  - 与主链共识、分布式存储等紧密结合，提升整体性能
- **与理论的递归关系 Recursive Theoretical Relation**：
  - 数据可用性理论递归嵌套于Layer2与主链共识机制，为Web3生态提供安全与高可用性语义

---

> 说明：本节为Layer2共识子主题数据可用性的递归分析，后续可继续细分Celestia、EigenDA等子主题，每层均采用五元结构与中英双语解释。
