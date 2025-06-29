# Web3设计模式 (Web3 Design Patterns)

## 概述

Web3设计模式是构建去中心化应用的经典解决方案，通过标准化的设计方法提高系统的可维护性、可扩展性和安全性。

## 1. 基本定义

**定义 1.1**（代理模式）：
通过代理合约实现逻辑与数据分离的升级模式。

**定义 1.2**（工厂模式）：
用于批量创建智能合约实例的设计模式。

**定义 1.3**（状态机模式）：
将复杂业务逻辑建模为有限状态自动机的设计模式。

## 2. 核心定理

**定理 2.1**（代理安全性）：
透明代理模式在正确实现下保证存储布局兼容性。

**定理 2.2**（工厂正确性）：
工厂模式生成的合约实例与模板合约在逻辑上等价。

**定理 2.3**（状态机一致性）：
状态机模式确保系统状态转换的确定性和一致性。

## 3. 应用场景

- 智能合约升级机制
- DeFi协议架构设计
- DAO治理系统构建

## 4. Rust代码示例

### Web3核心设计模式实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use serde::{Serialize, Deserialize};
use uuid::Uuid;

// 1. 代理模式 (Proxy Pattern)
#[derive(Debug, Clone)]
pub struct ProxyContract {
    pub address: String,
    pub implementation_address: String,
    pub admin: String,
    pub storage: Arc<RwLock<HashMap<String, Vec<u8>>>>,
}

impl ProxyContract {
    pub fn new(admin: String, implementation_address: String) -> Self {
        ProxyContract {
            address: format!("proxy_{}", Uuid::new_v4()),
            implementation_address,
            admin,
            storage: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub fn upgrade(&mut self, new_implementation: String, caller: &str) -> Result<(), String> {
        if caller != self.admin {
            return Err("只有管理员可以升级".to_string());
        }
        
        self.implementation_address = new_implementation;
        println!("代理合约已升级到: {}", self.implementation_address);
        Ok(())
    }
    
    pub fn delegate_call(&self, method: &str, data: Vec<u8>) -> Result<Vec<u8>, String> {
        // 模拟委托调用到实现合约
        println!("委托调用 {} 到实现合约 {}", method, self.implementation_address);
        
        // 在实际实现中，这里会调用具体的实现合约逻辑
        match method {
            "get_value" => {
                let storage = self.storage.read().unwrap();
                if let Some(value) = storage.get("value") {
                    Ok(value.clone())
                } else {
                    Ok(b"default_value".to_vec())
                }
            }
            "set_value" => {
                let mut storage = self.storage.write().unwrap();
                storage.insert("value".to_string(), data);
                Ok(b"success".to_vec())
            }
            _ => Err("未知方法".to_string()),
        }
    }
    
    pub fn get_implementation(&self) -> &str {
        &self.implementation_address
    }
}

// 2. 工厂模式 (Factory Pattern)
#[derive(Debug, Clone)]
pub struct ContractTemplate {
    pub template_id: String,
    pub bytecode: Vec<u8>,
    pub abi: String,
    pub version: String,
}

#[derive(Debug, Clone)]
pub struct ContractInstance {
    pub address: String,
    pub template_id: String,
    pub creator: String,
    pub creation_time: u64,
    pub init_params: HashMap<String, String>,
}

pub struct ContractFactory {
    templates: Arc<RwLock<HashMap<String, ContractTemplate>>>,
    instances: Arc<RwLock<HashMap<String, ContractInstance>>>,
    factory_owner: String,
}

impl ContractFactory {
    pub fn new(owner: String) -> Self {
        ContractFactory {
            templates: Arc::new(RwLock::new(HashMap::new())),
            instances: Arc::new(RwLock::new(HashMap::new())),
            factory_owner: owner,
        }
    }
    
    pub fn register_template(
        &self,
        template_id: String,
        bytecode: Vec<u8>,
        abi: String,
        version: String,
    ) -> Result<(), String> {
        let template = ContractTemplate {
            template_id: template_id.clone(),
            bytecode,
            abi,
            version,
        };
        
        let mut templates = self.templates.write().unwrap();
        templates.insert(template_id, template);
        Ok(())
    }
    
    pub fn create_instance(
        &self,
        template_id: &str,
        creator: String,
        init_params: HashMap<String, String>,
    ) -> Result<String, String> {
        // 检查模板是否存在
        {
            let templates = self.templates.read().unwrap();
            if !templates.contains_key(template_id) {
                return Err("模板不存在".to_string());
            }
        }
        
        let instance_address = format!("contract_{}", Uuid::new_v4());
        let instance = ContractInstance {
            address: instance_address.clone(),
            template_id: template_id.to_string(),
            creator,
            creation_time: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            init_params,
        };
        
        let mut instances = self.instances.write().unwrap();
        instances.insert(instance_address.clone(), instance);
        
        println!("创建合约实例: {} 基于模板: {}", instance_address, template_id);
        Ok(instance_address)
    }
    
    pub fn get_instances_by_template(&self, template_id: &str) -> Vec<ContractInstance> {
        let instances = self.instances.read().unwrap();
        instances.values()
            .filter(|instance| instance.template_id == template_id)
            .cloned()
            .collect()
    }
    
    pub fn get_instances_by_creator(&self, creator: &str) -> Vec<ContractInstance> {
        let instances = self.instances.read().unwrap();
        instances.values()
            .filter(|instance| instance.creator == creator)
            .cloned()
            .collect()
    }
}

// 3. 状态机模式 (State Machine Pattern)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ProposalState {
    Pending,
    Active,
    Succeeded,
    Defeated,
    Queued,
    Executed,
    Cancelled,
}

#[derive(Debug, Clone)]
pub struct StateTransition {
    pub from: ProposalState,
    pub to: ProposalState,
    pub condition: String,
    pub action: String,
}

#[derive(Debug, Clone)]
pub struct Proposal {
    pub id: String,
    pub title: String,
    pub description: String,
    pub proposer: String,
    pub state: ProposalState,
    pub votes_for: u64,
    pub votes_against: u64,
    pub quorum_required: u64,
    pub voting_end_time: u64,
    pub execution_time: Option<u64>,
}

pub struct GovernanceStateMachine {
    proposals: Arc<RwLock<HashMap<String, Proposal>>>,
    transitions: Vec<StateTransition>,
    quorum_threshold: u64,
}

impl GovernanceStateMachine {
    pub fn new(quorum_threshold: u64) -> Self {
        let mut transitions = Vec::new();
        
        // 定义状态转换规则
        transitions.push(StateTransition {
            from: ProposalState::Pending,
            to: ProposalState::Active,
            condition: "voting_period_started".to_string(),
            action: "start_voting".to_string(),
        });
        
        transitions.push(StateTransition {
            from: ProposalState::Active,
            to: ProposalState::Succeeded,
            condition: "votes_for > votes_against && quorum_met".to_string(),
            action: "mark_succeeded".to_string(),
        });
        
        transitions.push(StateTransition {
            from: ProposalState::Active,
            to: ProposalState::Defeated,
            condition: "votes_against >= votes_for || voting_ended".to_string(),
            action: "mark_defeated".to_string(),
        });
        
        transitions.push(StateTransition {
            from: ProposalState::Succeeded,
            to: ProposalState::Queued,
            condition: "execution_delay_met".to_string(),
            action: "queue_execution".to_string(),
        });
        
        transitions.push(StateTransition {
            from: ProposalState::Queued,
            to: ProposalState::Executed,
            condition: "execution_called".to_string(),
            action: "execute_proposal".to_string(),
        });
        
        GovernanceStateMachine {
            proposals: Arc::new(RwLock::new(HashMap::new())),
            transitions,
            quorum_threshold,
        }
    }
    
    pub fn create_proposal(
        &self,
        title: String,
        description: String,
        proposer: String,
        voting_end_time: u64,
    ) -> String {
        let proposal_id = format!("proposal_{}", Uuid::new_v4());
        let proposal = Proposal {
            id: proposal_id.clone(),
            title,
            description,
            proposer,
            state: ProposalState::Pending,
            votes_for: 0,
            votes_against: 0,
            quorum_required: self.quorum_threshold,
            voting_end_time,
            execution_time: None,
        };
        
        let mut proposals = self.proposals.write().unwrap();
        proposals.insert(proposal_id.clone(), proposal);
        
        proposal_id
    }
    
    pub fn transition_state(&self, proposal_id: &str, trigger: &str) -> Result<ProposalState, String> {
        let mut proposals = self.proposals.write().unwrap();
        let proposal = proposals.get_mut(proposal_id)
            .ok_or("提案不存在")?;
        
        let current_state = proposal.state.clone();
        
        // 查找可用的状态转换
        for transition in &self.transitions {
            if transition.from == current_state && self.check_condition(proposal, &transition.condition, trigger) {
                proposal.state = transition.to.clone();
                self.execute_action(proposal, &transition.action);
                println!("提案 {} 状态从 {:?} 转换到 {:?}", proposal_id, current_state, proposal.state);
                return Ok(proposal.state.clone());
            }
        }
        
        Err(format!("无有效状态转换: {:?} -> {}", current_state, trigger))
    }
    
    fn check_condition(&self, proposal: &Proposal, condition: &str, trigger: &str) -> bool {
        let current_time = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        match condition {
            "voting_period_started" => trigger == "start_voting",
            "votes_for > votes_against && quorum_met" => {
                proposal.votes_for > proposal.votes_against && 
                (proposal.votes_for + proposal.votes_against) >= proposal.quorum_required &&
                current_time >= proposal.voting_end_time
            }
            "votes_against >= votes_for || voting_ended" => {
                proposal.votes_against >= proposal.votes_for || 
                current_time >= proposal.voting_end_time
            }
            "execution_delay_met" => trigger == "queue_for_execution",
            "execution_called" => trigger == "execute",
            _ => false,
        }
    }
    
    fn execute_action(&self, proposal: &mut Proposal, action: &str) {
        match action {
            "start_voting" => {
                println!("开始投票: {}", proposal.title);
            }
            "mark_succeeded" => {
                println!("提案通过: {}", proposal.title);
            }
            "mark_defeated" => {
                println!("提案被否决: {}", proposal.title);
            }
            "queue_execution" => {
                proposal.execution_time = Some(
                    std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap()
                        .as_secs() + 86400 // 24小时延迟
                );
                println!("提案排队执行: {}", proposal.title);
            }
            "execute_proposal" => {
                println!("执行提案: {}", proposal.title);
            }
            _ => {}
        }
    }
    
    pub fn vote(&self, proposal_id: &str, voter: &str, support: bool, weight: u64) -> Result<(), String> {
        let mut proposals = self.proposals.write().unwrap();
        let proposal = proposals.get_mut(proposal_id)
            .ok_or("提案不存在")?;
        
        if proposal.state != ProposalState::Active {
            return Err("提案不在投票状态".to_string());
        }
        
        if support {
            proposal.votes_for += weight;
        } else {
            proposal.votes_against += weight;
        }
        
        println!("用户 {} 对提案 {} 投票: {} (权重: {})", voter, proposal_id, if support { "支持" } else { "反对" }, weight);
        Ok(())
    }
    
    pub fn get_proposal(&self, proposal_id: &str) -> Option<Proposal> {
        let proposals = self.proposals.read().unwrap();
        proposals.get(proposal_id).cloned()
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Web3设计模式演示 ===\n");
    
    // 1. 代理模式演示
    println!("1. 代理模式演示:");
    let mut proxy = ProxyContract::new(
        "admin_address".to_string(),
        "implementation_v1".to_string(),
    );
    
    // 设置值
    let _ = proxy.delegate_call("set_value", b"hello_world".to_vec())?;
    
    // 获取值
    let value = proxy.delegate_call("get_value", vec![])?;
    println!("获取的值: {}", String::from_utf8_lossy(&value));
    
    // 升级合约
    proxy.upgrade("implementation_v2".to_string(), "admin_address")?;
    println!("当前实现: {}\n", proxy.get_implementation());
    
    // 2. 工厂模式演示
    println!("2. 工厂模式演示:");
    let factory = ContractFactory::new("factory_owner".to_string());
    
    // 注册模板
    factory.register_template(
        "erc20_template".to_string(),
        b"erc20_bytecode".to_vec(),
        "erc20_abi".to_string(),
        "1.0.0".to_string(),
    )?;
    
    // 创建实例
    let mut init_params = HashMap::new();
    init_params.insert("name".to_string(), "MyToken".to_string());
    init_params.insert("symbol".to_string(), "MTK".to_string());
    
    let instance1 = factory.create_instance(
        "erc20_template",
        "user1".to_string(),
        init_params.clone(),
    )?;
    
    let instance2 = factory.create_instance(
        "erc20_template",
        "user2".to_string(),
        init_params,
    )?;
    
    println!("创建的实例: {}, {}\n", instance1, instance2);
    
    // 3. 状态机模式演示
    println!("3. 状态机模式演示:");
    let governance = GovernanceStateMachine::new(100);
    
    let proposal_id = governance.create_proposal(
        "升级协议".to_string(),
        "升级到新版本协议".to_string(),
        "proposer_address".to_string(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs() + 3600,
    );
    
    // 状态转换
    governance.transition_state(&proposal_id, "start_voting")?;
    
    // 模拟投票
    governance.vote(&proposal_id, "voter1", true, 60)?;
    governance.vote(&proposal_id, "voter2", true, 50)?;
    
    // 结束投票
    governance.transition_state(&proposal_id, "end_voting")?;
    
    if let Some(proposal) = governance.get_proposal(&proposal_id) {
        println!("最终状态: {:?}\n", proposal.state);
    }
    
    Ok(())
}
```

## 相关链接

- [微服务设计模式](02_Microservices_Patterns.md)
- [并发设计模式](03_Concurrency_Patterns.md)
- [智能合约基础](../../02_Core_Technologies/02_Smart_Contracts/)
- [设计模式总览](../)
- [架构设计总览](../../)

---

*Web3设计模式为去中心化应用提供经过验证的架构解决方案。*
