# 智能合约基础 (Smart Contract Fundamentals)

## 概述

智能合约是部署在区块链上的自动执行程序，通过代码实现合约条款的自动化执行，是Web3应用的核心构建模块。

## 1. 基本定义

**定义 1.1**（智能合约）：
存储在区块链上的程序，当满足预定条件时自动执行合约条款。

**定义 1.2**（合约状态）：
智能合约在区块链上的数据存储，包括变量值和持久化信息。

**定义 1.3**（Gas机制）：
衡量和限制智能合约执行计算复杂度的经济机制。

## 2. 核心定理

**定理 2.1**（确定性执行）：
相同输入下，智能合约在不同节点上的执行结果必须相同。

**定理 2.2**（状态一致性）：
经过网络共识的合约状态变更对所有节点都是一致的。

**定理 2.3**（不可变性）：
一旦部署，智能合约的代码逻辑无法被修改（除非设计了升级机制）。

## 3. 应用场景

- 去中心化金融（DeFi）协议
- 数字资产管理和交易
- 去中心化自治组织（DAO）治理

## 4. Rust代码示例

### 基础智能合约框架

```rust
use std::collections::HashMap;
use sha2::{Sha256, Digest};

#[derive(Debug, Clone)]
struct Account {
    address: String,
    balance: u64,
    nonce: u64,
}

impl Account {
    fn new(address: String, initial_balance: u64) -> Self {
        Account {
            address,
            balance: initial_balance,
            nonce: 0,
        }
    }
}

#[derive(Debug, Clone)]
struct Transaction {
    from: String,
    to: String,
    value: u64,
    gas_limit: u64,
    gas_price: u64,
    data: Vec<u8>,
    nonce: u64,
}

trait SmartContract {
    fn execute(&mut self, tx: &Transaction, state: &mut WorldState) -> Result<(), String>;
    fn get_address(&self) -> String;
    fn get_storage(&self, key: &str) -> Option<String>;
    fn set_storage(&mut self, key: String, value: String);
}

#[derive(Debug)]
struct SimpleToken {
    address: String,
    total_supply: u64,
    balances: HashMap<String, u64>,
    storage: HashMap<String, String>,
}

impl SimpleToken {
    fn new(address: String, total_supply: u64) -> Self {
        let mut balances = HashMap::new();
        balances.insert(address.clone(), total_supply);
        
        SimpleToken {
            address,
            total_supply,
            balances,
            storage: HashMap::new(),
        }
    }
    
    fn transfer(&mut self, from: &str, to: &str, amount: u64) -> Result<(), String> {
        let from_balance = self.balances.get(from).unwrap_or(&0);
        
        if *from_balance < amount {
            return Err("余额不足".to_string());
        }
        
        self.balances.insert(from.to_string(), from_balance - amount);
        let to_balance = self.balances.get(to).unwrap_or(&0);
        self.balances.insert(to.to_string(), to_balance + amount);
        
        Ok(())
    }
    
    fn balance_of(&self, address: &str) -> u64 {
        *self.balances.get(address).unwrap_or(&0)
    }
}

impl SmartContract for SimpleToken {
    fn execute(&mut self, tx: &Transaction, _state: &mut WorldState) -> Result<(), String> {
        // 简化的函数调用解析
        if tx.data.len() >= 4 {
            let function_selector = &tx.data[0..4];
            
            match function_selector {
                [0x01, 0x00, 0x00, 0x00] => {
                    // transfer函数
                    if tx.data.len() >= 68 {
                        let to = String::from_utf8_lossy(&tx.data[4..36]).to_string();
                        let amount = u64::from_be_bytes(
                            tx.data[60..68].try_into().map_err(|_| "无效的金额")?
                        );
                        self.transfer(&tx.from, &to, amount)?;
                    }
                }
                [0x02, 0x00, 0x00, 0x00] => {
                    // balanceOf函数
                    let balance = self.balance_of(&tx.from);
                    println!("账户 {} 余额: {}", tx.from, balance);
                }
                _ => return Err("未知函数".to_string()),
            }
        }
        Ok(())
    }
    
    fn get_address(&self) -> String {
        self.address.clone()
    }
    
    fn get_storage(&self, key: &str) -> Option<String> {
        self.storage.get(key).cloned()
    }
    
    fn set_storage(&mut self, key: String, value: String) {
        self.storage.insert(key, value);
    }
}

#[derive(Debug)]
struct WorldState {
    accounts: HashMap<String, Account>,
    contracts: HashMap<String, Box<dyn SmartContract>>,
    gas_used: u64,
}

impl WorldState {
    fn new() -> Self {
        WorldState {
            accounts: HashMap::new(),
            contracts: HashMap::new(),
            gas_used: 0,
        }
    }
    
    fn create_account(&mut self, address: String, initial_balance: u64) {
        let account = Account::new(address.clone(), initial_balance);
        self.accounts.insert(address, account);
    }
    
    fn deploy_contract(&mut self, contract: Box<dyn SmartContract>) {
        let address = contract.get_address();
        self.contracts.insert(address, contract);
    }
    
    fn execute_transaction(&mut self, tx: Transaction) -> Result<(), String> {
        // 验证发送者余额
        if let Some(sender) = self.accounts.get_mut(&tx.from) {
            let total_cost = tx.value + tx.gas_limit * tx.gas_price;
            if sender.balance < total_cost {
                return Err("余额不足以支付交易费用".to_string());
            }
            
            sender.balance -= total_cost;
            sender.nonce += 1;
        } else {
            return Err("发送者账户不存在".to_string());
        }
        
        // 执行合约调用
        if let Some(contract) = self.contracts.get_mut(&tx.to) {
            contract.execute(&tx, self)?;
        } else {
            // 普通转账
            if let Some(recipient) = self.accounts.get_mut(&tx.to) {
                recipient.balance += tx.value;
            } else {
                self.create_account(tx.to, tx.value);
            }
        }
        
        self.gas_used += tx.gas_limit;
        Ok(())
    }
}

fn main() {
    let mut state = WorldState::new();
    
    // 创建账户
    state.create_account("alice".to_string(), 1000);
    state.create_account("bob".to_string(), 500);
    
    // 部署代币合约
    let token_contract = SimpleToken::new("token_contract".to_string(), 10000);
    state.deploy_contract(Box::new(token_contract));
    
    // 创建转账交易
    let transfer_tx = Transaction {
        from: "alice".to_string(),
        to: "token_contract".to_string(),
        value: 0,
        gas_limit: 100000,
        gas_price: 1,
        data: vec![0x01, 0x00, 0x00, 0x00], // transfer函数选择器
        nonce: 1,
    };
    
    match state.execute_transaction(transfer_tx) {
        Ok(()) => println!("交易执行成功"),
        Err(e) => println!("交易失败: {}", e),
    }
    
    println!("Gas使用量: {}", state.gas_used);
}
```

## 相关链接

- [合约安全性](02_Contract_Security.md)
- [虚拟机架构](03_Virtual_Machine_Architecture.md)
- [区块链架构](../01_Blockchain_Fundamentals/01_Blockchain_Architecture.md)
- [智能合约总览](../)
- [核心技术总览](../../)

---

*智能合约基础为Web3应用提供可编程、自动执行的去中心化计算平台。*
