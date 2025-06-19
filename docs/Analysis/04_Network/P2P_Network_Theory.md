# P2P网络理论 (P2P Network Theory)

## 目录

1. [P2P网络基础](#1-p2p网络基础)
2. [网络拓扑理论](#2-网络拓扑理论)
3. [Gossip协议](#3-gossip协议)
4. [分布式哈希表(DHT)](#4-分布式哈希表dht)
5. [网络路由算法](#5-网络路由算法)
6. [网络安全性](#6-网络安全性)
7. [实现示例](#7-实现示例)
8. [参考与扩展](#8-参考与扩展)

## 1. P2P网络基础

### 1.1 P2P网络定义

**定义 1.1.1 (P2P网络)**
P2P (Peer-to-Peer) 网络是一种分布式网络架构，其中节点既是客户端又是服务器，直接相互通信而不依赖中央服务器。

**定义 1.1.2 (P2P网络模型)**
P2P网络可以形式化为一个图 $G = (V, E)$，其中：

- $V$ 是节点集合
- $E$ 是连接集合
- 每个节点 $v \in V$ 具有相同的功能和权限

**定义 1.1.3 (P2P网络特性)**
P2P网络具有以下核心特性：

1. **去中心化**: 无单一控制点
2. **自组织**: 节点自主加入和离开
3. **容错性**: 单个节点故障不影响整体
4. **可扩展性**: 支持大量节点
5. **负载均衡**: 资源分布均匀

### 1.2 P2P网络分类

**定义 1.2.1 (结构化P2P网络)**
结构化P2P网络具有预定义的拓扑结构，如DHT (Distributed Hash Table)。

**定义 1.2.2 (非结构化P2P网络)**
非结构化P2P网络具有随机或部分随机的拓扑结构。

**定义 1.2.3 (混合P2P网络)**
混合P2P网络结合了结构化和非结构化的特点。

**定理 1.2.1 (P2P网络连通性)**
在P2P网络中，如果每个节点的度数至少为 $\log n$，则网络以高概率是连通的。

**证明：** 通过随机图理论：

考虑随机图 $G(n, p)$，其中 $p = \frac{\log n}{n}$。

根据随机图理论，当 $p > \frac{\log n}{n}$ 时，图以高概率是连通的。

在P2P网络中，每个节点平均连接到 $\log n$ 个其他节点，因此网络以高概率是连通的。■

## 2. 网络拓扑理论

### 2.1 网络拓扑定义

**定义 2.1.1 (网络拓扑)**
网络拓扑是指网络中节点和连接的物理或逻辑排列方式。

**定义 2.1.2 (拓扑度量)**
网络拓扑的度量包括：

1. **直径 (Diameter)**: 任意两节点间最短路径的最大长度
2. **平均路径长度**: 所有节点对间最短路径的平均长度
3. **聚类系数**: 节点的邻居间连接密度
4. **度分布**: 节点度数的概率分布

### 2.2 小世界网络

**定义 2.2.1 (小世界网络)**
小世界网络具有高聚类系数和短平均路径长度的特性。

**定理 2.2.1 (小世界网络特性)**
小世界网络的平均路径长度与网络大小的对数成正比：
$$L \sim \log N$$

**证明：** 通过网络分析：

在小世界网络中，通过随机重连或添加随机边，可以显著减少平均路径长度。

根据网络理论，小世界网络的平均路径长度与网络大小的对数成正比。■

### 2.3 无标度网络

**定义 2.3.1 (无标度网络)**
无标度网络的度分布遵循幂律分布：
$$P(k) \sim k^{-\gamma}$$

**定理 2.3.1 (无标度网络特性)**
无标度网络具有少数高度节点和大量低度节点的特性。

**证明：** 通过幂律分布分析：

幂律分布 $P(k) \sim k^{-\gamma}$ 表明，高度节点的概率随度数增加而快速下降。

因此，网络中少数节点具有很高的度数，而大多数节点具有较低的度数。■

## 3. Gossip协议

### 3.1 Gossip协议定义

**定义 3.1.1 (Gossip协议)**
Gossip协议是一种基于随机传播的信息扩散协议，节点随机选择邻居传播信息。

**定义 3.1.2 (Gossip传播模型)**
Gossip传播可以建模为：
$$I(t+1) = I(t) + \beta \cdot I(t) \cdot (N - I(t))$$

其中：

- $I(t)$ 是时间 $t$ 时已感染节点数
- $\beta$ 是传播率
- $N$ 是总节点数

### 3.2 Gossip协议分析

**定理 3.2.1 (Gossip传播效率)**
Gossip协议在 $O(\log N)$ 轮内可以将信息传播到所有节点。

**证明：** 通过概率分析：

在每一轮中，每个已感染节点随机选择一个邻居传播信息。

设 $I(t)$ 为第 $t$ 轮已感染节点数，则：
$$E[I(t+1)] = I(t) + \beta \cdot I(t) \cdot (N - I(t))$$

当 $I(t) = N/2$ 时，传播速度最快。因此，传播到所有节点需要 $O(\log N)$ 轮。■

**定理 3.2.2 (Gossip协议容错性)**
Gossip协议对节点故障具有强容错性。

**证明：** 通过冗余传播：

由于每个节点随机选择邻居传播信息，即使部分节点故障，信息仍能通过其他路径传播。

因此，Gossip协议对节点故障具有强容错性。■

### 3.3 Gossip协议变种

**定义 3.3.1 (反熵Gossip)**
反熵Gossip用于同步节点状态，节点定期与随机邻居交换状态信息。

**定义 3.3.2 (谣言传播Gossip)**
谣言传播Gossip用于快速传播信息，节点在收到信息后立即传播给随机邻居。

**定义 3.3.3 (聚合Gossip)**
聚合Gossip用于计算网络中的聚合值，如平均值、最大值等。

## 4. 分布式哈希表(DHT)

### 4.1 DHT基础理论

**定义 4.1.1 (分布式哈希表)**
DHT是一种分布式数据结构，将键值对分布存储在多个节点上。

**定义 4.1.2 (DHT接口)**
DHT提供以下基本操作：

1. **put(key, value)**: 存储键值对
2. **get(key)**: 获取键对应的值
3. **remove(key)**: 删除键值对

### 4.2 Chord DHT

**定义 4.2.1 (Chord环)**
Chord DHT将节点组织成一个环形结构，每个节点负责一个键值范围。

**定理 4.2.1 (Chord路由复杂度)**
Chord DHT的路由复杂度为 $O(\log N)$。

**证明：** 通过手指表分析：

Chord使用手指表，每个节点维护 $\log N$ 个指向其他节点的指针。

每次路由可以将距离减半，因此最多需要 $\log N$ 跳到达目标节点。■

### 4.3 Kademlia DHT

**定义 4.3.1 (Kademlia距离)**
Kademlia使用XOR距离度量：
$$d(x, y) = x \oplus y$$

**定理 4.3.1 (Kademlia路由效率)**
Kademlia的路由复杂度为 $O(\log N)$。

**证明：** 通过k-bucket分析：

Kademlia使用k-bucket存储节点，每个bucket包含距离在 $[2^i, 2^{i+1})$ 范围内的节点。

每次路由可以消除至少一位的XOR距离，因此最多需要 $\log N$ 跳。■

## 5. 网络路由算法

### 5.1 路由算法定义

**定义 5.1.1 (路由算法)**
路由算法决定网络中数据包的传输路径。

**定义 5.1.2 (路由表)**
路由表存储每个目标节点的下一跳信息。

### 5.2 距离向量路由

**定义 5.2.1 (距离向量路由)**
距离向量路由使用Bellman-Ford算法计算最短路径。

**定理 5.2.1 (距离向量收敛)**
距离向量路由在有限时间内收敛到最短路径。

**证明：** 通过Bellman-Ford算法：

Bellman-Ford算法最多需要 $|V|-1$ 次迭代收敛到最短路径。

因此，距离向量路由在有限时间内收敛。■

### 5.3 链路状态路由

**定义 5.3.1 (链路状态路由)**
链路状态路由使用Dijkstra算法计算最短路径。

**定理 5.3.1 (链路状态最优性)**
链路状态路由计算的是全局最优路径。

**证明：** 通过Dijkstra算法：

Dijkstra算法保证找到从源节点到所有其他节点的最短路径。

因此，链路状态路由计算的是全局最优路径。■

## 6. 网络安全性

### 6.1 网络攻击模型

**定义 6.1.1 (网络攻击)**
网络攻击包括：

1. **Sybil攻击**: 攻击者创建大量虚假身份
2. **Eclipse攻击**: 攻击者控制目标节点的所有连接
3. **路由攻击**: 攻击者操纵路由信息
4. **DDoS攻击**: 分布式拒绝服务攻击

### 6.2 安全防护机制

**定义 6.2.1 (身份验证)**
身份验证确保节点的真实身份。

**定义 6.2.2 (加密通信)**
加密通信保护数据传输的机密性。

**定理 6.2.1 (Sybil攻击防护)**
通过工作量证明可以限制Sybil攻击。

**证明：** 通过成本分析：

工作量证明要求节点解决计算难题，增加了创建虚假身份的成本。

因此，通过工作量证明可以限制Sybil攻击。■

## 7. 实现示例

### 7.1 P2P网络实现

```rust
// P2P网络节点实现
use std::collections::HashMap;
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Node {
    id: String,
    address: String,
    port: u16,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Message {
    Ping,
    Pong,
    FindNode { target: String },
    FindNodeResponse { nodes: Vec<Node> },
    Store { key: String, value: String },
    Get { key: String },
    GetResponse { value: Option<String> },
}

pub struct P2PNetwork {
    node: Node,
    peers: Arc<Mutex<HashMap<String, Node>>>,
    storage: Arc<Mutex<HashMap<String, String>>>,
    dht: Arc<Mutex<DHT>>,
}

impl P2PNetwork {
    pub fn new(id: String, address: String, port: u16) -> Self {
        let node = Node { id, address, port };
        let dht = DHT::new(node.id.clone());
        
        P2PNetwork {
            node,
            peers: Arc::new(Mutex::new(HashMap::new())),
            storage: Arc::new(Mutex::new(HashMap::new())),
            dht: Arc::new(Mutex::new(dht)),
        }
    }
    
    pub fn start(&self) -> Result<(), Box<dyn std::error::Error>> {
        let listener = TcpListener::bind(format!("{}:{}", self.node.address, self.node.port))?;
        println!("P2P节点启动在 {}:{}", self.node.address, self.node.port);
        
        let peers = Arc::clone(&self.peers);
        let storage = Arc::clone(&self.storage);
        let dht = Arc::clone(&self.dht);
        let node_id = self.node.id.clone();
        
        for stream in listener.incoming() {
            let stream = stream?;
            let peers = Arc::clone(&peers);
            let storage = Arc::clone(&storage);
            let dht = Arc::clone(&dht);
            let node_id = node_id.clone();
            
            thread::spawn(move || {
                Self::handle_connection(stream, peers, storage, dht, node_id);
            });
        }
        
        Ok(())
    }
    
    fn handle_connection(
        stream: TcpStream,
        peers: Arc<Mutex<HashMap<String, Node>>>,
        storage: Arc<Mutex<HashMap<String, String>>>,
        dht: Arc<Mutex<DHT>>,
        node_id: String,
    ) {
        use std::io::{Read, Write};
        
        let mut buffer = [0; 1024];
        let mut stream = stream;
        
        match stream.read(&mut buffer) {
            Ok(n) => {
                let message_bytes = &buffer[..n];
                if let Ok(message) = serde_json::from_slice::<Message>(message_bytes) {
                    let response = Self::process_message(message, peers, storage, dht, node_id);
                    if let Ok(response_bytes) = serde_json::to_vec(&response) {
                        let _ = stream.write_all(&response_bytes);
                    }
                }
            }
            Err(e) => eprintln!("读取连接错误: {}", e),
        }
    }
    
    fn process_message(
        message: Message,
        peers: Arc<Mutex<HashMap<String, Node>>>,
        storage: Arc<Mutex<HashMap<String, String>>>,
        dht: Arc<Mutex<DHT>>,
        node_id: String,
    ) -> Message {
        match message {
            Message::Ping => Message::Pong,
            
            Message::FindNode { target } => {
                let dht = dht.lock().unwrap();
                let nodes = dht.find_node(&target);
                Message::FindNodeResponse { nodes }
            }
            
            Message::Store { key, value } => {
                let mut storage = storage.lock().unwrap();
                storage.insert(key, value);
                Message::Pong
            }
            
            Message::Get { key } => {
                let storage = storage.lock().unwrap();
                let value = storage.get(&key).cloned();
                Message::GetResponse { value }
            }
            
            _ => Message::Pong,
        }
    }
    
    pub fn join_network(&self, bootstrap_node: &str) -> Result<(), Box<dyn std::error::Error>> {
        let client = TcpStream::connect(bootstrap_node)?;
        let message = Message::FindNode { target: self.node.id.clone() };
        let message_bytes = serde_json::to_vec(&message)?;
        
        use std::io::Write;
        client.try_clone()?.write_all(&message_bytes)?;
        
        let mut buffer = [0; 1024];
        let n = client.read(&mut buffer)?;
        let response: Message = serde_json::from_slice(&buffer[..n])?;
        
        if let Message::FindNodeResponse { nodes } = response {
            let mut peers = self.peers.lock().unwrap();
            for node in nodes {
                peers.insert(node.id.clone(), node);
            }
        }
        
        Ok(())
    }
    
    pub fn store(&self, key: String, value: String) -> Result<(), Box<dyn std::error::Error>> {
        let dht = self.dht.lock().unwrap();
        let responsible_node = dht.find_responsible_node(&key);
        
        if responsible_node == self.node.id {
            let mut storage = self.storage.lock().unwrap();
            storage.insert(key, value);
        } else {
            // 转发到负责的节点
            if let Some(peer) = self.peers.lock().unwrap().get(&responsible_node) {
                let client = TcpStream::connect(format!("{}:{}", peer.address, peer.port))?;
                let message = Message::Store { key, value };
                let message_bytes = serde_json::to_vec(&message)?;
                
                use std::io::Write;
                client.write_all(&message_bytes)?;
            }
        }
        
        Ok(())
    }
    
    pub fn get(&self, key: String) -> Result<Option<String>, Box<dyn std::error::Error>> {
        let dht = self.dht.lock().unwrap();
        let responsible_node = dht.find_responsible_node(&key);
        
        if responsible_node == self.node.id {
            let storage = self.storage.lock().unwrap();
            Ok(storage.get(&key).cloned())
        } else {
            // 从负责的节点获取
            if let Some(peer) = self.peers.lock().unwrap().get(&responsible_node) {
                let client = TcpStream::connect(format!("{}:{}", peer.address, peer.port))?;
                let message = Message::Get { key };
                let message_bytes = serde_json::to_vec(&message)?;
                
                use std::io::Write;
                client.write_all(&message_bytes)?;
                
                let mut buffer = [0; 1024];
                let n = client.read(&mut buffer)?;
                let response: Message = serde_json::from_slice(&buffer[..n])?;
                
                if let Message::GetResponse { value } = response {
                    Ok(value)
                } else {
                    Ok(None)
                }
            } else {
                Ok(None)
            }
        }
    }
}

// DHT实现
pub struct DHT {
    node_id: String,
    finger_table: Vec<String>,
}

impl DHT {
    pub fn new(node_id: String) -> Self {
        let mut finger_table = Vec::new();
        for i in 0..160 {
            let finger_id = Self::calculate_finger_id(&node_id, i);
            finger_table.push(finger_id);
        }
        
        DHT {
            node_id,
            finger_table,
        }
    }
    
    fn calculate_finger_id(node_id: &str, i: usize) -> String {
        // 简化的手指ID计算
        format!("{}_{}", node_id, i)
    }
    
    pub fn find_node(&self, target: &str) -> Vec<Node> {
        // 简化的节点查找
        vec![
            Node {
                id: target.to_string(),
                address: "127.0.0.1".to_string(),
                port: 8080,
            }
        ]
    }
    
    pub fn find_responsible_node(&self, key: &str) -> String {
        // 简化的负责节点查找
        key.to_string()
    }
}
```

### 7.2 Gossip协议实现

```rust
// Gossip协议实现
use std::collections::HashSet;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

#[derive(Clone, Debug)]
pub struct GossipNode {
    id: String,
    neighbors: Vec<String>,
    state: NodeState,
}

#[derive(Clone, Debug)]
pub struct NodeState {
    version: u64,
    data: String,
    timestamp: u64,
}

pub struct GossipProtocol {
    node: GossipNode,
    network: Arc<Mutex<Vec<GossipNode>>>,
    infected_nodes: Arc<Mutex<HashSet<String>>>,
}

impl GossipProtocol {
    pub fn new(id: String, neighbors: Vec<String>) -> Self {
        let node = GossipNode {
            id: id.clone(),
            neighbors,
            state: NodeState {
                version: 0,
                data: "".to_string(),
                timestamp: 0,
            },
        };
        
        GossipProtocol {
            node,
            network: Arc::new(Mutex::new(Vec::new())),
            infected_nodes: Arc::new(Mutex::new(HashSet::new())),
        }
    }
    
    pub fn start_gossip(&self) {
        let node_id = self.node.id.clone();
        let neighbors = self.node.neighbors.clone();
        let network = Arc::clone(&self.network);
        let infected_nodes = Arc::clone(&self.infected_nodes);
        
        thread::spawn(move || {
            loop {
                // 随机选择邻居
                if let Some(neighbor) = neighbors.choose(&mut rand::thread_rng()) {
                    Self::send_gossip_message(&node_id, neighbor, &network, &infected_nodes);
                }
                
                thread::sleep(Duration::from_millis(1000));
            }
        });
    }
    
    fn send_gossip_message(
        sender_id: &str,
        receiver_id: &str,
        network: &Arc<Mutex<Vec<GossipNode>>>,
        infected_nodes: &Arc<Mutex<HashSet<String>>>,
    ) {
        // 模拟发送gossip消息
        println!("节点 {} 向节点 {} 发送gossip消息", sender_id, receiver_id);
        
        // 更新感染节点集合
        let mut infected = infected_nodes.lock().unwrap();
        infected.insert(receiver_id.to_string());
        
        // 模拟网络传播
        let network = network.lock().unwrap();
        if let Some(receiver) = network.iter().find(|n| n.id == receiver_id) {
            // 接收者处理消息
            Self::receive_gossip_message(receiver_id, &network, infected_nodes);
        }
    }
    
    fn receive_gossip_message(
        receiver_id: &str,
        network: &Vec<GossipNode>,
        infected_nodes: &Arc<Mutex<HashSet<String>>>,
    ) {
        println!("节点 {} 接收到gossip消息", receiver_id);
        
        // 更新感染状态
        let mut infected = infected_nodes.lock().unwrap();
        infected.insert(receiver_id.to_string());
        
        // 检查是否所有节点都已感染
        let total_nodes = network.len();
        let infected_count = infected.len();
        
        if infected_count == total_nodes {
            println!("所有节点都已感染，gossip传播完成");
        }
    }
    
    pub fn update_state(&mut self, new_data: String) {
        self.node.state.version += 1;
        self.node.state.data = new_data;
        self.node.state.timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        // 标记自己为已感染
        let mut infected = self.infected_nodes.lock().unwrap();
        infected.insert(self.node.id.clone());
        
        println!("节点 {} 更新状态: {}", self.node.id, new_data);
    }
    
    pub fn get_infected_count(&self) -> usize {
        self.infected_nodes.lock().unwrap().len()
    }
    
    pub fn is_fully_infected(&self) -> bool {
        let network = self.network.lock().unwrap();
        let infected = self.infected_nodes.lock().unwrap();
        infected.len() == network.len()
    }
}

// 反熵Gossip实现
pub struct AntiEntropyGossip {
    node: GossipNode,
    peers: Arc<Mutex<Vec<GossipNode>>>,
    state: Arc<Mutex<NodeState>>,
}

impl AntiEntropyGossip {
    pub fn new(id: String, neighbors: Vec<String>) -> Self {
        let node = GossipNode {
            id: id.clone(),
            neighbors,
            state: NodeState {
                version: 0,
                data: "".to_string(),
                timestamp: 0,
            },
        };
        
        AntiEntropyGossip {
            node,
            peers: Arc::new(Mutex::new(Vec::new())),
            state: Arc::new(Mutex::new(NodeState {
                version: 0,
                data: "".to_string(),
                timestamp: 0,
            })),
        }
    }
    
    pub fn start_anti_entropy(&self) {
        let node_id = self.node.id.clone();
        let neighbors = self.node.neighbors.clone();
        let peers = Arc::clone(&self.peers);
        let state = Arc::clone(&self.state);
        
        thread::spawn(move || {
            loop {
                // 随机选择邻居进行状态同步
                if let Some(neighbor) = neighbors.choose(&mut rand::thread_rng()) {
                    Self::synchronize_state(&node_id, neighbor, &peers, &state);
                }
                
                thread::sleep(Duration::from_millis(5000));
            }
        });
    }
    
    fn synchronize_state(
        sender_id: &str,
        receiver_id: &str,
        peers: &Arc<Mutex<Vec<GossipNode>>>,
        state: &Arc<Mutex<NodeState>>,
    ) {
        println!("节点 {} 与节点 {} 进行状态同步", sender_id, receiver_id);
        
        let sender_state = state.lock().unwrap();
        let peers = peers.lock().unwrap();
        
        if let Some(receiver) = peers.iter().find(|n| n.id == receiver_id) {
            // 比较版本号
            if sender_state.version > receiver.state.version {
                println!("节点 {} 的状态更新，同步到节点 {}", sender_id, receiver_id);
            } else if sender_state.version < receiver.state.version {
                println!("节点 {} 的状态更新，从节点 {} 同步", sender_id, receiver_id);
            } else {
                println!("节点 {} 和节点 {} 状态一致", sender_id, receiver_id);
            }
        }
    }
    
    pub fn update_state(&mut self, new_data: String) {
        let mut state = self.state.lock().unwrap();
        state.version += 1;
        state.data = new_data;
        state.timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        println!("节点 {} 更新状态: {}", self.node.id, new_data);
    }
}
```

### 7.3 网络路由实现

```rust
// 网络路由实现
use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex};

#[derive(Clone, Debug)]
pub struct NetworkNode {
    id: String,
    neighbors: Vec<String>,
    routing_table: HashMap<String, String>, // target -> next_hop
}

pub struct NetworkRouter {
    nodes: Arc<Mutex<HashMap<String, NetworkNode>>>,
}

impl NetworkRouter {
    pub fn new() -> Self {
        NetworkRouter {
            nodes: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn add_node(&mut self, id: String, neighbors: Vec<String>) {
        let node = NetworkNode {
            id: id.clone(),
            neighbors,
            routing_table: HashMap::new(),
        };
        
        self.nodes.lock().unwrap().insert(id, node);
    }
    
    pub fn compute_routes(&mut self) {
        let mut nodes = self.nodes.lock().unwrap();
        
        for node_id in nodes.keys().cloned().collect::<Vec<_>>() {
            self.compute_shortest_paths(&mut nodes, &node_id);
        }
    }
    
    fn compute_shortest_paths(&self, nodes: &mut HashMap<String, NetworkNode>, source: &str) {
        let mut distances: HashMap<String, u32> = HashMap::new();
        let mut previous: HashMap<String, String> = HashMap::new();
        let mut queue: VecDeque<String> = VecDeque::new();
        
        // 初始化
        for node_id in nodes.keys() {
            distances.insert(node_id.clone(), u32::MAX);
        }
        distances.insert(source.to_string(), 0);
        queue.push_back(source.to_string());
        
        // BFS计算最短路径
        while let Some(current) = queue.pop_front() {
            if let Some(node) = nodes.get(&current) {
                for neighbor in &node.neighbors {
                    let new_distance = distances[&current] + 1;
                    
                    if new_distance < distances[neighbor] {
                        distances.insert(neighbor.clone(), new_distance);
                        previous.insert(neighbor.clone(), current.clone());
                        queue.push_back(neighbor.clone());
                    }
                }
            }
        }
        
        // 更新路由表
        if let Some(source_node) = nodes.get_mut(source) {
            for target in nodes.keys() {
                if target != source {
                    if let Some(next_hop) = self.find_next_hop(target, source, &previous) {
                        source_node.routing_table.insert(target.clone(), next_hop);
                    }
                }
            }
        }
    }
    
    fn find_next_hop(&self, target: &str, source: &str, previous: &HashMap<String, String>) -> Option<String> {
        let mut current = target;
        let mut next_hop = None;
        
        while let Some(prev) = previous.get(current) {
            if prev == source {
                next_hop = Some(current.to_string());
                break;
            }
            current = prev;
        }
        
        next_hop
    }
    
    pub fn route_packet(&self, source: &str, destination: &str) -> Option<Vec<String>> {
        let nodes = self.nodes.lock().unwrap();
        
        if let Some(source_node) = nodes.get(source) {
            if let Some(next_hop) = source_node.routing_table.get(destination) {
                let mut path = vec![source.to_string()];
                
                if next_hop == destination {
                    path.push(destination.to_string());
                } else {
                    // 递归查找路径
                    if let Some(sub_path) = self.route_packet(next_hop, destination) {
                        path.extend(sub_path);
                    }
                }
                
                return Some(path);
            }
        }
        
        None
    }
    
    pub fn get_routing_table(&self, node_id: &str) -> Option<HashMap<String, String>> {
        self.nodes.lock().unwrap()
            .get(node_id)
            .map(|node| node.routing_table.clone())
    }
    
    pub fn print_network_topology(&self) {
        let nodes = self.nodes.lock().unwrap();
        
        println!("网络拓扑:");
        for (node_id, node) in nodes.iter() {
            println!("节点 {}: 邻居 {:?}", node_id, node.neighbors);
        }
        
        println!("\n路由表:");
        for (node_id, node) in nodes.iter() {
            println!("节点 {} 的路由表:", node_id);
            for (target, next_hop) in &node.routing_table {
                println!("  {} -> {}", target, next_hop);
            }
            println!();
        }
    }
}

// 距离向量路由实现
pub struct DistanceVectorRouter {
    nodes: Arc<Mutex<HashMap<String, DistanceVectorNode>>>,
}

#[derive(Clone, Debug)]
pub struct DistanceVectorNode {
    id: String,
    neighbors: HashMap<String, u32>, // neighbor_id -> cost
    distance_vector: HashMap<String, u32>, // destination -> cost
    next_hop: HashMap<String, String>, // destination -> next_hop
}

impl DistanceVectorRouter {
    pub fn new() -> Self {
        DistanceVectorRouter {
            nodes: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn add_node(&mut self, id: String, neighbors: HashMap<String, u32>) {
        let mut distance_vector = HashMap::new();
        let mut next_hop = HashMap::new();
        
        // 初始化距离向量
        distance_vector.insert(id.clone(), 0);
        for (neighbor_id, cost) in &neighbors {
            distance_vector.insert(neighbor_id.clone(), *cost);
            next_hop.insert(neighbor_id.clone(), neighbor_id.clone());
        }
        
        let node = DistanceVectorNode {
            id: id.clone(),
            neighbors,
            distance_vector,
            next_hop,
        };
        
        self.nodes.lock().unwrap().insert(id, node);
    }
    
    pub fn run_distance_vector(&mut self) {
        let mut converged = false;
        let mut iterations = 0;
        let max_iterations = 100;
        
        while !converged && iterations < max_iterations {
            converged = self.iterate_distance_vector();
            iterations += 1;
        }
        
        println!("距离向量算法在 {} 次迭代后收敛", iterations);
    }
    
    fn iterate_distance_vector(&mut self) -> bool {
        let mut nodes = self.nodes.lock().unwrap();
        let mut converged = true;
        
        for node_id in nodes.keys().cloned().collect::<Vec<_>>() {
            if let Some(node) = nodes.get(&node_id) {
                let mut updated = false;
                let mut new_distance_vector = node.distance_vector.clone();
                let mut new_next_hop = node.next_hop.clone();
                
                for destination in nodes.keys() {
                    if destination != &node_id {
                        let mut min_cost = u32::MAX;
                        let mut best_next_hop = None;
                        
                        // 通过邻居找到最短路径
                        for (neighbor_id, neighbor_cost) in &node.neighbors {
                            if let Some(neighbor_node) = nodes.get(neighbor_id) {
                                if let Some(&neighbor_to_dest) = neighbor_node.distance_vector.get(destination) {
                                    let total_cost = neighbor_cost + neighbor_to_dest;
                                    if total_cost < min_cost {
                                        min_cost = total_cost;
                                        best_next_hop = Some(neighbor_id.clone());
                                    }
                                }
                            }
                        }
                        
                        if let Some(next_hop) = best_next_hop {
                            let current_cost = new_distance_vector.get(destination).unwrap_or(&u32::MAX);
                            if min_cost < *current_cost {
                                new_distance_vector.insert(destination.clone(), min_cost);
                                new_next_hop.insert(destination.clone(), next_hop);
                                updated = true;
                            }
                        }
                    }
                }
                
                if updated {
                    converged = false;
                    if let Some(node) = nodes.get_mut(&node_id) {
                        node.distance_vector = new_distance_vector;
                        node.next_hop = new_next_hop;
                    }
                }
            }
        }
        
        converged
    }
    
    pub fn print_distance_vectors(&self) {
        let nodes = self.nodes.lock().unwrap();
        
        println!("距离向量表:");
        for (node_id, node) in nodes.iter() {
            println!("节点 {}:", node_id);
            for (destination, cost) in &node.distance_vector {
                if let Some(next_hop) = node.next_hop.get(destination) {
                    println!("  {} -> {} (通过 {})", destination, cost, next_hop);
                }
            }
            println!();
        }
    }
}
```

## 8. 参考与扩展

### 8.1 相关理论

- [区块链基础理论](../01_Foundations/Blockchain_Formal_Model.md)
- [共识机制理论](../02_Consensus_Theory/Consensus_Formal_Proofs.md)
- [网络安全理论](../05_Security_Privacy/Network_Security_Theory.md)
- [性能优化理论](../06_Performance/Network_Performance_Optimization.md)

### 8.2 高级主题

- [网络拓扑优化](../04_Network/Network_Topology_Optimization.md)
- [网络协议设计](../04_Network/Network_Protocol_Design.md)
- [网络监控与分析](../04_Network/Network_Monitoring_Analysis.md)
- [量子网络](../11_Future_Trends/Quantum_Network.md)

### 8.3 实现参考

- [Rust网络实现](../03_Technology_Stack/Rust_Network_Implementation.md)
- [Go网络实现](../03_Technology_Stack/Go_Network_Implementation.md)
- [网络性能测试](../06_Performance/Network_Performance_Benchmarks.md)

### 8.4 外部参考

- [P2P Systems and Applications](https://link.springer.com/book/10.1007/978-3-540-30027-4)
- [Distributed Hash Tables](https://pdos.csail.mit.edu/papers/chord:sigcomm01/chord_sigcomm.pdf)
- [Gossip Protocols](https://www.cs.cornell.edu/home/rvr/papers/flowgossip.pdf)
- [Network Routing](https://www.cs.princeton.edu/courses/archive/fall06/cos561/papers/ek_flow.pdf)
