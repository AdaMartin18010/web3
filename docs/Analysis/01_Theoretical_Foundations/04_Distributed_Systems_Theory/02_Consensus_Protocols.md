# 共识协议 (Consensus Protocols)

## 概述

共识协议是分布式系统的核心，确保多个节点在存在故障的情况下达成一致，是区块链和Web3的基础。

## 1. 基本定义

**定义 1.1**（共识）：
分布式系统中所有正确节点对某个值达成一致的过程。

**定义 1.2**（共识协议）：
实现共识的分布式算法，满足安全性、活性等性质。

**定义 1.3**（拜占庭容错）：
在存在拜占庭故障的情况下仍能达成共识。

## 2. 经典协议

### 2.1 Paxos协议

**定理 2.1**（Paxos安全性）：
一旦某个值被决定，后续所有决定都是该值。

**定理 2.2**（Paxos活性）：
在同步网络和多数节点正常时，协议能达成共识。

### 2.2 Raft协议

**定理 2.3**（Raft领导者完整性）：
如果某个日志条目在某个任期被提交，则该条目会出现在所有更高任期的领导者中。

## 3. 应用场景

- 区块链共识机制（PoW、PoS、DPoS）
- 分布式数据库一致性
- 微服务架构中的状态同步

## 4. Rust代码示例

### 简化Raft领导者选举

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
enum NodeState {
    Follower,
    Candidate,
    Leader,
}

struct RaftNode {
    id: u64,
    state: NodeState,
    term: u64,
    voted_for: Option<u64>,
    votes_received: u64,
}

impl RaftNode {
    fn new(id: u64) -> Self {
        RaftNode {
            id,
            state: NodeState::Follower,
            term: 0,
            voted_for: None,
            votes_received: 0,
        }
    }
    
    fn start_election(&mut self) {
        self.state = NodeState::Candidate;
        self.term += 1;
        self.voted_for = Some(self.id);
        self.votes_received = 1;
        println!("节点{}开始选举，任期{}", self.id, self.term);
    }
    
    fn receive_vote(&mut self, voter_id: u64) {
        if self.state == NodeState::Candidate {
            self.votes_received += 1;
            println!("节点{}获得来自节点{}的投票", self.id, voter_id);
        }
    }
    
    fn become_leader(&mut self) {
        if self.votes_received >= 3 { // 假设5个节点，需要3票
            self.state = NodeState::Leader;
            println!("节点{}成为领导者", self.id);
        }
    }
}

fn main() {
    let mut node = RaftNode::new(1);
    node.start_election();
    node.receive_vote(2);
    node.receive_vote(3);
    node.become_leader();
}
```

## 相关链接

- [分布式系统理论基础](README.md)
- [系统模型与故障理论](01_System_Models_And_Fault_Theory.md)
- [分布式算法](03_Distributed_Algorithms.md)
- [一致性理论](04_Consistency_Theory.md)
- [分布式系统理论总览](../)

---

*共识协议为分布式系统提供一致性和容错能力，是Web3和区块链的核心技术基础。*
