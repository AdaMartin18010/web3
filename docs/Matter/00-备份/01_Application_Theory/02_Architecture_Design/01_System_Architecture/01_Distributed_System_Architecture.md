# 分布式系统架构 (Distributed System Architecture)

## 概述

分布式系统架构是Web3基础设施的核心设计模式，通过去中心化的节点网络实现高可用性、容错性和可扩展性。

## 1. 基本定义

**定义 1.1**（分布式系统）：
由多个自治计算节点通过网络连接协作完成任务的系统。

**定义 1.2**（节点）：
分布式系统中的独立计算单元，具有处理、存储和通信能力。

**定义 1.3**（去中心化架构）：
没有单点控制的系统架构，决策权分散在多个节点中。

## 2. 核心定理

**定理 2.1**（CAP定理）：
分布式系统最多只能同时保证一致性（Consistency）、可用性（Availability）、分区容错性（Partition tolerance）中的两个。

**定理 2.2**（拜占庭将军问题）：
在存在恶意节点的分布式系统中，需要超过2/3的诚实节点才能达成共识。

**定理 2.3**（端到端原理）：
网络应该只提供基本的传输服务，复杂功能应在端系统实现。

## 3. 应用场景

- 区块链网络架构设计
- P2P文件共享系统
- 去中心化应用（DApp）架构

## 4. Rust代码示例

### 分布式节点网络实现

```rust
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;
use serde::{Serialize, Deserialize};
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    pub id: String,
    pub from: String,
    pub to: Option<String>, // None表示广播
    pub message_type: MessageType,
    pub payload: String,
    pub timestamp: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MessageType {
    Ping,
    Pong,
    Data,
    Consensus,
    HeartBeat,
}

#[derive(Debug, Clone)]
pub struct NodeInfo {
    pub id: String,
    pub address: String,
    pub port: u16,
    pub status: NodeStatus,
    pub last_seen: u64,
}

#[derive(Debug, Clone)]
pub enum NodeStatus {
    Online,
    Offline,
    Suspected,
}

pub struct DistributedNode {
    pub id: String,
    pub address: String,
    pub port: u16,
    pub peers: Arc<Mutex<HashMap<String, NodeInfo>>>,
    pub message_history: Arc<Mutex<HashSet<String>>>,
    pub consensus_state: Arc<Mutex<ConsensusState>>,
    pub sender: mpsc::UnboundedSender<Message>,
    pub receiver: Arc<Mutex<mpsc::UnboundedReceiver<Message>>>,
}

#[derive(Debug, Clone)]
pub struct ConsensusState {
    pub current_round: u64,
    pub votes: HashMap<String, String>, // node_id -> vote
    pub proposal: Option<String>,
    pub committed_value: Option<String>,
}

impl DistributedNode {
    pub fn new(address: String, port: u16) -> Self {
        let id = Uuid::new_v4().to_string();
        let (sender, receiver) = mpsc::unbounded_channel();
        
        DistributedNode {
            id,
            address,
            port,
            peers: Arc::new(Mutex::new(HashMap::new())),
            message_history: Arc::new(Mutex::new(HashSet::new())),
            consensus_state: Arc::new(Mutex::new(ConsensusState {
                current_round: 0,
                votes: HashMap::new(),
                proposal: None,
                committed_value: None,
            })),
            sender,
            receiver: Arc::new(Mutex::new(receiver)),
        }
    }
    
    pub fn add_peer(&self, peer: NodeInfo) {
        let mut peers = self.peers.lock().unwrap();
        peers.insert(peer.id.clone(), peer);
    }
    
    pub fn broadcast_message(&self, message_type: MessageType, payload: String) {
        let message = Message {
            id: Uuid::new_v4().to_string(),
            from: self.id.clone(),
            to: None,
            message_type,
            payload,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        };
        
        // 记录消息历史
        {
            let mut history = self.message_history.lock().unwrap();
            history.insert(message.id.clone());
        }
        
        // 发送给所有在线节点
        let peers = self.peers.lock().unwrap();
        for (_, peer) in peers.iter() {
            if matches!(peer.status, NodeStatus::Online) {
                let _ = self.sender.send(message.clone());
            }
        }
    }
    
    pub fn send_direct_message(&self, to: String, message_type: MessageType, payload: String) {
        let message = Message {
            id: Uuid::new_v4().to_string(),
            from: self.id.clone(),
            to: Some(to),
            message_type,
            payload,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        };
        
        let _ = self.sender.send(message);
    }
    
    pub fn handle_message(&self, message: Message) -> Result<(), String> {
        // 检查消息重复
        {
            let mut history = self.message_history.lock().unwrap();
            if history.contains(&message.id) {
                return Ok(()); // 忽略重复消息
            }
            history.insert(message.id.clone());
        }
        
        match message.message_type {
            MessageType::Ping => {
                self.send_direct_message(
                    message.from,
                    MessageType::Pong,
                    "pong".to_string(),
                );
            }
            MessageType::Pong => {
                // 更新节点状态
                let mut peers = self.peers.lock().unwrap();
                if let Some(peer) = peers.get_mut(&message.from) {
                    peer.status = NodeStatus::Online;
                    peer.last_seen = message.timestamp;
                }
            }
            MessageType::Consensus => {
                self.handle_consensus_message(&message)?;
            }
            MessageType::Data => {
                println!("节点 {} 收到数据: {}", self.id, message.payload);
            }
            MessageType::HeartBeat => {
                // 更新心跳
                let mut peers = self.peers.lock().unwrap();
                if let Some(peer) = peers.get_mut(&message.from) {
                    peer.last_seen = message.timestamp;
                }
            }
        }
        
        Ok(())
    }
    
    fn handle_consensus_message(&self, message: &Message) -> Result<(), String> {
        let mut state = self.consensus_state.lock().unwrap();
        
        // 简化的共识协议实现
        if message.payload.starts_with("propose:") {
            let proposal = message.payload.strip_prefix("propose:").unwrap();
            state.proposal = Some(proposal.to_string());
            state.current_round += 1;
            
            // 投票支持提案
            state.votes.insert(self.id.clone(), proposal.to_string());
            
            // 广播投票
            drop(state);
            self.broadcast_message(
                MessageType::Consensus,
                format!("vote:{}", proposal),
            );
        } else if message.payload.starts_with("vote:") {
            let vote = message.payload.strip_prefix("vote:").unwrap();
            state.votes.insert(message.from.clone(), vote.to_string());
            
            // 检查是否达成共识（简化：超过一半节点同意）
            let peers_count = self.peers.lock().unwrap().len();
            let required_votes = (peers_count + 1) / 2 + 1;
            
            let vote_count = state.votes.values()
                .filter(|&v| v == vote)
                .count();
                
            if vote_count >= required_votes {
                state.committed_value = Some(vote.to_string());
                println!("节点 {} 达成共识: {}", self.id, vote);
            }
        }
        
        Ok(())
    }
    
    pub fn start_consensus(&self, proposal: String) {
        self.broadcast_message(
            MessageType::Consensus,
            format!("propose:{}", proposal),
        );
    }
    
    pub fn get_consensus_result(&self) -> Option<String> {
        let state = self.consensus_state.lock().unwrap();
        state.committed_value.clone()
    }
}

// 网络拓扑管理
pub struct NetworkTopology {
    nodes: HashMap<String, DistributedNode>,
    connections: HashMap<String, HashSet<String>>,
}

impl NetworkTopology {
    pub fn new() -> Self {
        NetworkTopology {
            nodes: HashMap::new(),
            connections: HashMap::new(),
        }
    }
    
    pub fn add_node(&mut self, node: DistributedNode) {
        let node_id = node.id.clone();
        self.nodes.insert(node_id.clone(), node);
        self.connections.insert(node_id, HashSet::new());
    }
    
    pub fn connect_nodes(&mut self, node1_id: &str, node2_id: &str) -> Result<(), String> {
        if !self.nodes.contains_key(node1_id) || !self.nodes.contains_key(node2_id) {
            return Err("节点不存在".to_string());
        }
        
        // 建立双向连接
        self.connections.get_mut(node1_id).unwrap().insert(node2_id.to_string());
        self.connections.get_mut(node2_id).unwrap().insert(node1_id.to_string());
        
        // 更新节点的peer列表
        if let (Some(node1), Some(node2)) = (
            self.nodes.get(node1_id),
            self.nodes.get(node2_id)
        ) {
            let peer1 = NodeInfo {
                id: node2.id.clone(),
                address: node2.address.clone(),
                port: node2.port,
                status: NodeStatus::Online,
                last_seen: std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
            };
            
            let peer2 = NodeInfo {
                id: node1.id.clone(),
                address: node1.address.clone(),
                port: node1.port,
                status: NodeStatus::Online,
                last_seen: std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
            };
            
            node1.add_peer(peer2);
            node2.add_peer(peer1);
        }
        
        Ok(())
    }
    
    pub fn simulate_network_partition(&mut self, partition1: Vec<String>, partition2: Vec<String>) {
        // 断开两个分区之间的连接
        for node1 in &partition1 {
            for node2 in &partition2 {
                if let Some(connections) = self.connections.get_mut(node1) {
                    connections.remove(node2);
                }
                if let Some(connections) = self.connections.get_mut(node2) {
                    connections.remove(node1);
                }
            }
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut network = NetworkTopology::new();
    
    // 创建节点
    let node1 = DistributedNode::new("127.0.0.1".to_string(), 8001);
    let node2 = DistributedNode::new("127.0.0.1".to_string(), 8002);
    let node3 = DistributedNode::new("127.0.0.1".to_string(), 8003);
    
    let node1_id = node1.id.clone();
    let node2_id = node2.id.clone();
    let node3_id = node3.id.clone();
    
    network.add_node(node1);
    network.add_node(node2);
    network.add_node(node3);
    
    // 建立连接
    network.connect_nodes(&node1_id, &node2_id)?;
    network.connect_nodes(&node2_id, &node3_id)?;
    network.connect_nodes(&node1_id, &node3_id)?;
    
    println!("分布式网络初始化完成");
    println!("节点1: {}", node1_id);
    println!("节点2: {}", node2_id);
    println!("节点3: {}", node3_id);
    
    // 模拟共识过程
    if let Some(node1) = network.nodes.get(&node1_id) {
        node1.start_consensus("proposal_value_123".to_string());
        
        // 等待共识结果
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        
        if let Some(result) = node1.get_consensus_result() {
            println!("共识结果: {}", result);
        }
    }
    
    Ok(())
}
```

## 相关链接

- [微服务架构](02_Microservices_Architecture.md)
- [云原生架构](03_Cloud_Native_Architecture.md)
- [分布式系统理论](../../01_Theoretical_Foundations/04_Distributed_Systems_Theory/)
- [共识机制](../../02_Core_Technologies/01_Blockchain_Fundamentals/02_Consensus_Mechanisms.md)
- [系统架构总览](../)
- [架构设计总览](../../)

---

*分布式系统架构为Web3提供去中心化、高可用的基础设施设计模式。*
