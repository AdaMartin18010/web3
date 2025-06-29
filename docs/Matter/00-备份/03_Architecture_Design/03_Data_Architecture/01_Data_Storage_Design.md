# 数据存储设计 (Data Storage Design)

## 概述

数据存储设计是Web3架构的核心组件，通过分布式、去中心化的存储模式实现数据的持久化、一致性和可用性。

## 1. 基本定义

**定义 1.1**（分布式存储）：
数据分散存储在多个节点上的存储架构，提供高可用性和容错性。

**定义 1.2**（内容寻址存储）：
基于数据内容的哈希值进行寻址的存储方式。

**定义 1.3**（最终一致性）：
在没有新更新的情况下，系统最终会达到一致状态的一致性模型。

## 2. 核心定理

**定理 2.1**（存储可用性）：
在有$n$个副本的分布式存储中，系统可用性为$1-(1-p)^n$，其中$p$为单节点可用性。

**定理 2.2**（数据持久性）：
数据持久性概率随副本数量指数增长：$P_{durability} = 1 - \prod_{i=1}^{n}(1-p_i)$。

**定理 2.3**（CAP权衡）：
分布式存储系统在网络分区时只能在一致性和可用性中选择一个。

## 3. 应用场景

- 区块链状态存储
- IPFS分布式文件系统
- 去中心化数据库设计

## 4. Rust代码示例

### 分布式存储系统实现

```rust
use std::collections::{HashMap, BTreeMap};
use std::sync::{Arc, Mutex, RwLock};
use sha2::{Sha256, Digest};
use serde::{Serialize, Deserialize};
use tokio::sync::mpsc;
use std::time::{SystemTime, UNIX_EPOCH};

// 数据块结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataBlock {
    pub id: String,
    pub content: Vec<u8>,
    pub checksum: String,
    pub timestamp: u64,
    pub size: usize,
    pub metadata: HashMap<String, String>,
}

impl DataBlock {
    pub fn new(content: Vec<u8>, metadata: HashMap<String, String>) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(&content);
        let checksum = format!("{:x}", hasher.finalize());
        
        let id = checksum.clone(); // 内容寻址
        let size = content.len();
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        DataBlock {
            id,
            content,
            checksum,
            timestamp,
            size,
            metadata,
        }
    }
    
    pub fn verify_integrity(&self) -> bool {
        let mut hasher = Sha256::new();
        hasher.update(&self.content);
        let computed_checksum = format!("{:x}", hasher.finalize());
        computed_checksum == self.checksum
    }
}

// 副本策略
#[derive(Debug, Clone)]
pub enum ReplicationStrategy {
    Fixed(usize),           // 固定副本数
    Dynamic(usize, usize),  // 动态副本数(min, max)
    Erasure(usize, usize),  // 纠删码(data_chunks, parity_chunks)
}

// 一致性级别
#[derive(Debug, Clone)]
pub enum ConsistencyLevel {
    Eventual,    // 最终一致性
    Strong,      // 强一致性
    Quorum,      // 法定人数一致性
}

// 存储节点
#[derive(Debug, Clone)]
pub struct StorageNode {
    pub id: String,
    pub address: String,
    pub capacity: u64,
    pub used_space: u64,
    pub is_online: bool,
    pub last_heartbeat: u64,
}

impl StorageNode {
    pub fn new(id: String, address: String, capacity: u64) -> Self {
        StorageNode {
            id,
            address,
            capacity,
            used_space: 0,
            is_online: true,
            last_heartbeat: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        }
    }
    
    pub fn available_space(&self) -> u64 {
        self.capacity.saturating_sub(self.used_space)
    }
    
    pub fn utilization(&self) -> f64 {
        if self.capacity == 0 {
            0.0
        } else {
            self.used_space as f64 / self.capacity as f64
        }
    }
}

// 分布式存储管理器
pub struct DistributedStorage {
    nodes: Arc<RwLock<HashMap<String, StorageNode>>>,
    data_map: Arc<RwLock<HashMap<String, Vec<String>>>>, // data_id -> node_ids
    local_storage: Arc<RwLock<HashMap<String, DataBlock>>>,
    replication_strategy: ReplicationStrategy,
    consistency_level: ConsistencyLevel,
    node_id: String,
}

impl DistributedStorage {
    pub fn new(
        node_id: String,
        replication_strategy: ReplicationStrategy,
        consistency_level: ConsistencyLevel,
    ) -> Self {
        DistributedStorage {
            nodes: Arc::new(RwLock::new(HashMap::new())),
            data_map: Arc::new(RwLock::new(HashMap::new())),
            local_storage: Arc::new(RwLock::new(HashMap::new())),
            replication_strategy,
            consistency_level,
            node_id,
        }
    }
    
    pub fn add_node(&self, node: StorageNode) {
        let mut nodes = self.nodes.write().unwrap();
        nodes.insert(node.id.clone(), node);
    }
    
    pub fn remove_node(&self, node_id: &str) {
        let mut nodes = self.nodes.write().unwrap();
        nodes.remove(node_id);
        
        // 触发数据重新平衡
        self.rebalance_data();
    }
    
    fn select_storage_nodes(&self, data_size: usize) -> Vec<String> {
        let nodes = self.nodes.read().unwrap();
        let replica_count = match self.replication_strategy {
            ReplicationStrategy::Fixed(count) => count,
            ReplicationStrategy::Dynamic(min, _) => min,
            ReplicationStrategy::Erasure(data, parity) => data + parity,
        };
        
        let mut available_nodes: Vec<_> = nodes.iter()
            .filter(|(_, node)| {
                node.is_online && 
                node.available_space() >= data_size as u64
            })
            .map(|(id, node)| (id.clone(), node.utilization()))
            .collect();
        
        // 按使用率排序，优先选择使用率低的节点
        available_nodes.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());
        
        available_nodes.into_iter()
            .take(replica_count)
            .map(|(id, _)| id)
            .collect()
    }
    
    pub fn store_data(&self, content: Vec<u8>, metadata: HashMap<String, String>) -> Result<String, String> {
        let data_block = DataBlock::new(content, metadata);
        let data_id = data_block.id.clone();
        
        // 选择存储节点
        let selected_nodes = self.select_storage_nodes(data_block.size);
        if selected_nodes.is_empty() {
            return Err("没有可用的存储节点".to_string());
        }
        
        // 本地存储
        {
            let mut local_storage = self.local_storage.write().unwrap();
            local_storage.insert(data_id.clone(), data_block.clone());
        }
        
        // 更新数据映射
        {
            let mut data_map = self.data_map.write().unwrap();
            data_map.insert(data_id.clone(), selected_nodes.clone());
        }
        
        // 更新节点使用空间
        {
            let mut nodes = self.nodes.write().unwrap();
            for node_id in &selected_nodes {
                if let Some(node) = nodes.get_mut(node_id) {
                    node.used_space += data_block.size as u64;
                }
            }
        }
        
        // 异步复制到其他节点（在实际实现中）
        self.replicate_data(&data_id, &selected_nodes);
        
        Ok(data_id)
    }
    
    pub fn retrieve_data(&self, data_id: &str) -> Result<DataBlock, String> {
        // 首先尝试本地存储
        {
            let local_storage = self.local_storage.read().unwrap();
            if let Some(data_block) = local_storage.get(data_id) {
                if data_block.verify_integrity() {
                    return Ok(data_block.clone());
                }
            }
        }
        
        // 查找存储该数据的节点
        let storage_nodes = {
            let data_map = self.data_map.read().unwrap();
            data_map.get(data_id).cloned()
        };
        
        if let Some(nodes) = storage_nodes {
            // 从最近的在线节点获取数据
            for node_id in nodes {
                if self.is_node_online(&node_id) {
                    // 在实际实现中，这里会发送网络请求
                    // 现在返回模拟数据
                    break;
                }
            }
        }
        
        Err("数据未找到".to_string())
    }
    
    pub fn delete_data(&self, data_id: &str) -> Result<(), String> {
        // 从本地存储删除
        let data_size = {
            let mut local_storage = self.local_storage.write().unwrap();
            if let Some(data_block) = local_storage.remove(data_id) {
                data_block.size
            } else {
                0
            }
        };
        
        // 获取存储节点列表
        let storage_nodes = {
            let mut data_map = self.data_map.write().unwrap();
            data_map.remove(data_id)
        };
        
        if let Some(nodes) = storage_nodes {
            // 更新节点使用空间
            {
                let mut nodes_map = self.nodes.write().unwrap();
                for node_id in &nodes {
                    if let Some(node) = nodes_map.get_mut(node_id) {
                        node.used_space = node.used_space.saturating_sub(data_size as u64);
                    }
                }
            }
            
            // 从其他节点删除（在实际实现中发送删除请求）
            self.delete_from_nodes(data_id, &nodes);
        }
        
        Ok(())
    }
    
    fn replicate_data(&self, data_id: &str, target_nodes: &[String]) {
        // 在实际实现中，这里会异步发送数据到目标节点
        println!("复制数据 {} 到节点: {:?}", data_id, target_nodes);
    }
    
    fn delete_from_nodes(&self, data_id: &str, target_nodes: &[String]) {
        // 在实际实现中，这里会发送删除请求到目标节点
        println!("从节点删除数据 {}: {:?}", data_id, target_nodes);
    }
    
    fn is_node_online(&self, node_id: &str) -> bool {
        let nodes = self.nodes.read().unwrap();
        nodes.get(node_id).map_or(false, |node| node.is_online)
    }
    
    fn rebalance_data(&self) {
        // 数据重新平衡逻辑
        println!("开始数据重新平衡");
        
        let data_map = self.data_map.read().unwrap();
        for (data_id, current_nodes) in data_map.iter() {
            let online_nodes: Vec<_> = current_nodes.iter()
                .filter(|node_id| self.is_node_online(node_id))
                .collect();
            
            let required_replicas = match self.replication_strategy {
                ReplicationStrategy::Fixed(count) => count,
                ReplicationStrategy::Dynamic(min, _) => min,
                ReplicationStrategy::Erasure(data, parity) => data + parity,
            };
            
            if online_nodes.len() < required_replicas {
                println!("数据 {} 需要额外的副本", data_id);
                // 触发重新复制逻辑
            }
        }
    }
    
    pub fn get_storage_stats(&self) -> StorageStats {
        let nodes = self.nodes.read().unwrap();
        let local_storage = self.local_storage.read().unwrap();
        
        let total_capacity: u64 = nodes.values().map(|n| n.capacity).sum();
        let total_used: u64 = nodes.values().map(|n| n.used_space).sum();
        let online_nodes = nodes.values().filter(|n| n.is_online).count();
        let total_blocks = local_storage.len();
        
        StorageStats {
            total_capacity,
            total_used,
            total_nodes: nodes.len(),
            online_nodes,
            total_blocks,
            utilization: if total_capacity > 0 {
                total_used as f64 / total_capacity as f64
            } else {
                0.0
            },
        }
    }
}

#[derive(Debug)]
pub struct StorageStats {
    pub total_capacity: u64,
    pub total_used: u64,
    pub total_nodes: usize,
    pub online_nodes: usize,
    pub total_blocks: usize,
    pub utilization: f64,
}

// 内容寻址存储层
pub struct ContentAddressableStorage {
    storage: DistributedStorage,
    content_index: Arc<RwLock<HashMap<String, String>>>, // content_hash -> data_id
}

impl ContentAddressableStorage {
    pub fn new(storage: DistributedStorage) -> Self {
        ContentAddressableStorage {
            storage,
            content_index: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub fn put(&self, content: Vec<u8>) -> Result<String, String> {
        // 计算内容哈希
        let mut hasher = Sha256::new();
        hasher.update(&content);
        let content_hash = format!("{:x}", hasher.finalize());
        
        // 检查是否已存在
        {
            let index = self.content_index.read().unwrap();
            if let Some(data_id) = index.get(&content_hash) {
                return Ok(data_id.clone());
            }
        }
        
        // 存储新内容
        let mut metadata = HashMap::new();
        metadata.insert("content_hash".to_string(), content_hash.clone());
        
        let data_id = self.storage.store_data(content, metadata)?;
        
        // 更新内容索引
        {
            let mut index = self.content_index.write().unwrap();
            index.insert(content_hash, data_id.clone());
        }
        
        Ok(data_id)
    }
    
    pub fn get(&self, content_hash: &str) -> Result<Vec<u8>, String> {
        let data_id = {
            let index = self.content_index.read().unwrap();
            index.get(content_hash).cloned()
        };
        
        if let Some(data_id) = data_id {
            let data_block = self.storage.retrieve_data(&data_id)?;
            Ok(data_block.content)
        } else {
            Err("内容未找到".to_string())
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建分布式存储系统
    let storage = DistributedStorage::new(
        "node1".to_string(),
        ReplicationStrategy::Fixed(3),
        ConsistencyLevel::Quorum,
    );
    
    // 添加存储节点
    let node1 = StorageNode::new("node1".to_string(), "127.0.0.1:8001".to_string(), 1024 * 1024 * 1024); // 1GB
    let node2 = StorageNode::new("node2".to_string(), "127.0.0.1:8002".to_string(), 1024 * 1024 * 1024);
    let node3 = StorageNode::new("node3".to_string(), "127.0.0.1:8003".to_string(), 1024 * 1024 * 1024);
    
    storage.add_node(node1);
    storage.add_node(node2);
    storage.add_node(node3);
    
    // 创建内容寻址存储
    let cas = ContentAddressableStorage::new(storage);
    
    // 存储数据
    let test_data = b"Hello, Web3 Storage!".to_vec();
    let data_id = cas.put(test_data.clone())?;
    println!("数据存储完成，ID: {}", data_id);
    
    // 计算内容哈希进行检索
    let mut hasher = Sha256::new();
    hasher.update(&test_data);
    let content_hash = format!("{:x}", hasher.finalize());
    
    // 检索数据
    let retrieved_data = cas.get(&content_hash)?;
    println!("数据检索完成，内容: {}", String::from_utf8_lossy(&retrieved_data));
    
    // 显示存储统计
    let stats = cas.storage.get_storage_stats();
    println!("存储统计: {:?}", stats);
    
    Ok(())
}
```

## 相关链接

- [数据一致性策略](02_Data_Consistency.md)
- [数据备份恢复](03_Data_Backup_Recovery.md)
- [分布式系统架构](../01_System_Architecture/01_Distributed_System_Architecture.md)
- [数据架构总览](../)
- [架构设计总览](../../)

---

*数据存储设计为Web3提供可靠、高效的分布式数据管理能力。*
