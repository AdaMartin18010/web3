# 系统模型与故障理论 (System Models and Fault Theory)

## 概述

分布式系统模型与故障理论研究节点行为、网络模型和故障类型，为共识协议和分布式算法提供理论基础。

## 1. 系统模型

**定义 1.1**（同步模型）：
消息传递有已知上界，节点时钟同步。

**定义 1.2**（异步模型）：
消息传递无上界，节点时钟可能不同步。

**定义 1.3**（部分同步模型）：
介于同步与异步之间，存在未知但有限的消息延迟。

## 2. 故障模型

**定义 2.1**（崩溃故障）：
节点停止响应，不再发送消息。

**定义 2.2**（拜占庭故障）：
节点可能发送任意错误消息，包括恶意行为。

**定义 2.3**（遗漏故障）：
节点可能丢失或延迟发送消息。

## 3. 主要定理

**定理 3.1**（FLP不可能性）：
在异步系统中，即使只有一个节点崩溃，也无法实现确定性共识。

**定理 3.2**（CAP定理）：
分布式系统最多只能同时满足一致性、可用性、分区容错性中的两个。

## 4. 应用场景

- 区块链网络模型设计
- 共识协议故障假设
- 分布式系统容错设计

## 5. Rust代码示例

### 简单故障检测器

```rust
use std::time::{Duration, Instant};
use std::collections::HashMap;

struct FailureDetector {
    nodes: HashMap<String, Instant>,
    timeout: Duration,
}

impl FailureDetector {
    fn new(timeout: Duration) -> Self {
        FailureDetector {
            nodes: HashMap::new(),
            timeout,
        }
    }
    
    fn heartbeat(&mut self, node_id: String) {
        self.nodes.insert(node_id, Instant::now());
    }
    
    fn is_suspected(&self, node_id: &str) -> bool {
        if let Some(last_heartbeat) = self.nodes.get(node_id) {
            last_heartbeat.elapsed() > self.timeout
        } else {
            true
        }
    }
}

fn main() {
    let mut detector = FailureDetector::new(Duration::from_secs(5));
    detector.heartbeat("node1".to_string());
    println!("节点1状态: {}", if detector.is_suspected("node1") { "可疑" } else { "正常" });
}
```

## 相关链接

- [分布式系统理论基础](README.md)
- [共识协议](02_Consensus_Protocols.md)
- [分布式算法](03_Distributed_Algorithms.md)
- [一致性理论](04_Consistency_Theory.md)
- [分布式系统理论总览](../)

---

*系统模型与故障理论为分布式共识和容错系统提供基础假设和理论框架。*
