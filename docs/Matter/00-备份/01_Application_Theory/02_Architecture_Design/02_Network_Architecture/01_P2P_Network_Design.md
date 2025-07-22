# P2P网络设计 (P2P Network Design)

## 概述

P2P（点对点）网络设计是Web3基础设施的核心，通过去中心化的网络拓扑实现节点间的直接通信和资源共享。

## 1. 基本定义

**定义 1.1**（P2P网络）：
每个节点既是客户端又是服务器的分布式网络架构。

**定义 1.2**（DHT）：
分布式哈希表，用于在P2P网络中存储和查找键值对。

**定义 1.3**（Kademlia协议）：
基于异或距离度量的结构化P2P网络协议。

## 2. 核心定理

**定理 2.1**（网络直径定理）：
在Kademlia网络中，任意两个节点之间的最大跳数为$O(\log n)$，其中$n$是网络节点数。

**定理 2.2**（查找复杂度）：
DHT中查找操作的时间复杂度为$O(\log n)$。

**定理 2.3**（故障容忍性）：
P2P网络能够容忍$k$个节点的同时故障，其中$k$取决于复制因子。

## 3. 应用场景

- 区块链P2P网络层
- 分布式文件存储系统
- 去中心化内容分发网络

## 4. Rust代码示例

### Kademlia P2P网络实现

```rust
use std::collections::{HashMap, BTreeMap};
use std::net::SocketAddr;
use sha2::{Sha256, Digest};
use tokio::net::UdpSocket;
use serde::{Serialize, Deserialize};
use std::sync::{Arc, Mutex};

// 节点ID类型
pub type NodeId = [u8; 20]; // 160位节点ID

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KademliaNode {
    pub id: NodeId,
    pub address: SocketAddr,
    pub last_seen: u64,
}

impl KademliaNode {
    pub fn new(address: SocketAddr) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(address.to_string().as_bytes());
        let hash = hasher.finalize();
        
        let mut id = [0u8; 20];
        id.copy_from_slice(&hash[..20]);
        
        KademliaNode {
            id,
            address,
            last_seen: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        }
    }
    
    pub fn distance(&self, other_id: &NodeId) -> NodeId {
        let mut result = [0u8; 20];
        for i in 0..20 {
            result[i] = self.id[i] ^ other_id[i];
        }
        result
    }
}

// K-桶结构
pub struct KBucket {
    nodes: Vec<KademliaNode>,
    capacity: usize,
}

impl KBucket {
    pub fn new(capacity: usize) -> Self {
        KBucket {
            nodes: Vec::new(),
            capacity,
        }
    }
    
    pub fn add_node(&mut self, node: KademliaNode) -> bool {
        // 检查节点是否已存在
        if let Some(pos) = self.nodes.iter().position(|n| n.id == node.id) {
            // 更新现有节点
            self.nodes[pos] = node;
            return true;
        }
        
        if self.nodes.len() < self.capacity {
            self.nodes.push(node);
            true
        } else {
            // K-桶已满，可以实现替换策略
            false
        }
    }
    
    pub fn get_closest_nodes(&self, target_id: &NodeId, count: usize) -> Vec<KademliaNode> {
        let mut nodes_with_distance: Vec<_> = self.nodes.iter()
            .map(|node| (node.clone(), node.distance(target_id)))
            .collect();
        
        nodes_with_distance.sort_by(|a, b| a.1.cmp(&b.1));
        nodes_with_distance.into_iter()
            .take(count)
            .map(|(node, _)| node)
            .collect()
    }
}

// 路由表
pub struct RoutingTable {
    local_id: NodeId,
    buckets: Vec<KBucket>,
    k: usize, // K-桶容量
}

impl RoutingTable {
    pub fn new(local_id: NodeId, k: usize) -> Self {
        let mut buckets = Vec::new();
        for _ in 0..160 { // 160位ID空间
            buckets.push(KBucket::new(k));
        }
        
        RoutingTable {
            local_id,
            buckets,
            k,
        }
    }
    
    fn bucket_index(&self, node_id: &NodeId) -> usize {
        let distance = self.distance_to(node_id);
        let mut index = 0;
        
        for byte in distance.iter() {
            if *byte == 0 {
                index += 8;
            } else {
                index += byte.leading_zeros() as usize;
                break;
            }
        }
        
        std::cmp::min(index, 159)
    }
    
    fn distance_to(&self, node_id: &NodeId) -> NodeId {
        let mut result = [0u8; 20];
        for i in 0..20 {
            result[i] = self.local_id[i] ^ node_id[i];
        }
        result
    }
    
    pub fn add_node(&mut self, node: KademliaNode) -> bool {
        if node.id == self.local_id {
            return false; // 不添加自己
        }
        
        let bucket_index = self.bucket_index(&node.id);
        self.buckets[bucket_index].add_node(node)
    }
    
    pub fn find_closest_nodes(&self, target_id: &NodeId, count: usize) -> Vec<KademliaNode> {
        let mut all_nodes = Vec::new();
        
        // 从最接近的桶开始收集节点
        let target_bucket = self.bucket_index(target_id);
        
        for i in 0..160 {
            let bucket_idx = if i % 2 == 0 {
                target_bucket + i / 2
            } else {
                target_bucket.saturating_sub(i / 2)
            };
            
            if bucket_idx < 160 {
                let closest = self.buckets[bucket_idx].get_closest_nodes(target_id, count);
                all_nodes.extend(closest);
                
                if all_nodes.len() >= count {
                    break;
                }
            }
        }
        
        // 排序并取前count个
        all_nodes.sort_by(|a, b| {
            a.distance(target_id).cmp(&b.distance(target_id))
        });
        
        all_nodes.into_iter().take(count).collect()
    }
}

// P2P消息类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum KademliaMessage {
    Ping {
        sender: KademliaNode,
    },
    Pong {
        sender: KademliaNode,
    },
    FindNode {
        sender: KademliaNode,
        target_id: NodeId,
    },
    FindNodeResponse {
        sender: KademliaNode,
        nodes: Vec<KademliaNode>,
    },
    Store {
        sender: KademliaNode,
        key: Vec<u8>,
        value: Vec<u8>,
    },
    FindValue {
        sender: KademliaNode,
        key: Vec<u8>,
    },
    FindValueResponse {
        sender: KademliaNode,
        value: Option<Vec<u8>>,
        nodes: Vec<KademliaNode>,
    },
}

// DHT存储
#[derive(Debug, Clone)]
pub struct DHTStorage {
    data: HashMap<Vec<u8>, Vec<u8>>,
}

impl DHTStorage {
    pub fn new() -> Self {
        DHTStorage {
            data: HashMap::new(),
        }
    }
    
    pub fn store(&mut self, key: Vec<u8>, value: Vec<u8>) {
        self.data.insert(key, value);
    }
    
    pub fn get(&self, key: &[u8]) -> Option<&Vec<u8>> {
        self.data.get(key)
    }
}

// Kademlia P2P节点
pub struct KademliaP2P {
    local_node: KademliaNode,
    routing_table: Arc<Mutex<RoutingTable>>,
    storage: Arc<Mutex<DHTStorage>>,
    socket: Arc<UdpSocket>,
}

impl KademliaP2P {
    pub async fn new(address: SocketAddr) -> Result<Self, Box<dyn std::error::Error>> {
        let socket = UdpSocket::bind(address).await?;
        let local_node = KademliaNode::new(address);
        let routing_table = Arc::new(Mutex::new(RoutingTable::new(local_node.id, 20)));
        let storage = Arc::new(Mutex::new(DHTStorage::new()));
        
        Ok(KademliaP2P {
            local_node,
            routing_table,
            storage,
            socket: Arc::new(socket),
        })
    }
    
    pub async fn bootstrap(&self, bootstrap_nodes: Vec<SocketAddr>) -> Result<(), Box<dyn std::error::Error>> {
        for addr in bootstrap_nodes {
            let bootstrap_node = KademliaNode::new(addr);
            
            // 发送PING消息
            let ping_msg = KademliaMessage::Ping {
                sender: self.local_node.clone(),
            };
            
            self.send_message(&bootstrap_node.address, ping_msg).await?;
            
            // 添加到路由表
            {
                let mut routing_table = self.routing_table.lock().unwrap();
                routing_table.add_node(bootstrap_node);
            }
            
            // 查找自己的ID来填充路由表
            self.find_node(&self.local_node.id).await?;
        }
        
        Ok(())
    }
    
    pub async fn find_node(&self, target_id: &NodeId) -> Result<Vec<KademliaNode>, Box<dyn std::error::Error>> {
        let closest_nodes = {
            let routing_table = self.routing_table.lock().unwrap();
            routing_table.find_closest_nodes(target_id, 3)
        };
        
        let mut result_nodes = Vec::new();
        
        for node in closest_nodes {
            let find_msg = KademliaMessage::FindNode {
                sender: self.local_node.clone(),
                target_id: *target_id,
            };
            
            self.send_message(&node.address, find_msg).await?;
            // 在实际实现中，这里需要等待响应
        }
        
        Ok(result_nodes)
    }
    
    pub async fn store(&self, key: Vec<u8>, value: Vec<u8>) -> Result<(), Box<dyn std::error::Error>> {
        // 计算key的哈希作为目标ID
        let mut hasher = Sha256::new();
        hasher.update(&key);
        let hash = hasher.finalize();
        
        let mut target_id = [0u8; 20];
        target_id.copy_from_slice(&hash[..20]);
        
        // 找到最接近的节点
        let closest_nodes = {
            let routing_table = self.routing_table.lock().unwrap();
            routing_table.find_closest_nodes(&target_id, 3)
        };
        
        // 存储到本地
        {
            let mut storage = self.storage.lock().unwrap();
            storage.store(key.clone(), value.clone());
        }
        
        // 复制到其他节点
        for node in closest_nodes {
            let store_msg = KademliaMessage::Store {
                sender: self.local_node.clone(),
                key: key.clone(),
                value: value.clone(),
            };
            
            self.send_message(&node.address, store_msg).await?;
        }
        
        Ok(())
    }
    
    async fn send_message(
        &self,
        address: &SocketAddr,
        message: KademliaMessage,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let serialized = bincode::serialize(&message)?;
        self.socket.send_to(&serialized, address).await?;
        Ok(())
    }
    
    pub async fn handle_message(&self, message: KademliaMessage, from: SocketAddr) -> Result<(), Box<dyn std::error::Error>> {
        match message {
            KademliaMessage::Ping { sender } => {
                // 添加发送者到路由表
                {
                    let mut routing_table = self.routing_table.lock().unwrap();
                    routing_table.add_node(sender.clone());
                }
                
                // 发送PONG响应
                let pong_msg = KademliaMessage::Pong {
                    sender: self.local_node.clone(),
                };
                self.send_message(&from, pong_msg).await?;
            }
            
            KademliaMessage::FindNode { sender, target_id } => {
                // 添加发送者到路由表
                {
                    let mut routing_table = self.routing_table.lock().unwrap();
                    routing_table.add_node(sender.clone());
                }
                
                // 查找最接近的节点
                let closest_nodes = {
                    let routing_table = self.routing_table.lock().unwrap();
                    routing_table.find_closest_nodes(&target_id, 20)
                };
                
                // 发送响应
                let response_msg = KademliaMessage::FindNodeResponse {
                    sender: self.local_node.clone(),
                    nodes: closest_nodes,
                };
                self.send_message(&from, response_msg).await?;
            }
            
            KademliaMessage::Store { sender, key, value } => {
                // 添加发送者到路由表
                {
                    let mut routing_table = self.routing_table.lock().unwrap();
                    routing_table.add_node(sender);
                }
                
                // 存储键值对
                {
                    let mut storage = self.storage.lock().unwrap();
                    storage.store(key, value);
                }
            }
            
            _ => {
                // 处理其他消息类型
            }
        }
        
        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建P2P节点
    let node1 = KademliaP2P::new("127.0.0.1:8001".parse()?).await?;
    let node2 = KademliaP2P::new("127.0.0.1:8002".parse()?).await?;
    
    println!("P2P节点启动完成");
    println!("节点1: {:?}", node1.local_node.address);
    println!("节点2: {:?}", node2.local_node.address);
    
    // 节点2连接到节点1
    let bootstrap_nodes = vec!["127.0.0.1:8001".parse()?];
    node2.bootstrap(bootstrap_nodes).await?;
    
    println!("P2P网络初始化完成");
    
    // 存储数据
    let key = b"test_key".to_vec();
    let value = b"test_value".to_vec();
    node1.store(key, value).await?;
    
    println!("数据存储完成");
    
    Ok(())
}
```

## 相关链接

- [网络协议栈](02_Network_Protocol_Stack.md)
- [负载均衡技术](03_Load_Balancing.md)
- [分布式系统架构](../01_System_Architecture/01_Distributed_System_Architecture.md)
- [网络架构总览](../)
- [架构设计总览](../../)

---

*P2P网络设计为Web3提供去中心化的网络通信和资源共享基础。*
