# 身份验证与授权 (Authentication & Authorization)

## 概述

身份验证与授权是Web3安全架构的基础，通过密码学方法和去中心化身份系统确保系统的安全性和访问控制。

## 1. 基本定义

**定义 1.1**（身份验证）：
验证用户或实体身份真实性的过程。

**定义 1.2**（授权）：
确定已验证用户是否有权访问特定资源或执行特定操作的过程。

**定义 1.3**（去中心化身份）：
用户完全控制的、不依赖中心化机构的数字身份系统。

## 2. 核心定理

**定理 2.1**（数字签名安全性）：
在RSA假设下，RSA数字签名方案在选择消息攻击下是存在性不可伪造的。

**定理 2.2**（访问控制矩阵）：
访问控制系统的安全性等价于访问控制矩阵的完整性保护。

**定理 2.3**（零知识身份证明）：
存在完备、可靠且零知识的身份证明协议。

## 3. 应用场景

- Web3 DApp访问控制
- 数字身份管理系统
- 多方协作授权机制

## 4. Rust代码示例

### 去中心化身份验证系统

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use sha2::{Sha256, Digest};
use serde::{Serialize, Deserialize};
use uuid::Uuid;
use std::time::{SystemTime, UNIX_EPOCH};

// 数字身份
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DigitalIdentity {
    pub id: String,
    pub public_key: Vec<u8>,
    pub attributes: HashMap<String, String>,
    pub credentials: Vec<VerifiableCredential>,
    pub created_at: u64,
    pub updated_at: u64,
}

impl DigitalIdentity {
    pub fn new(public_key: Vec<u8>, attributes: HashMap<String, String>) -> Self {
        let id = format!("did:web3:{}", hex::encode(&public_key));
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        DigitalIdentity {
            id,
            public_key,
            attributes,
            credentials: Vec::new(),
            created_at: now,
            updated_at: now,
        }
    }
    
    pub fn add_credential(&mut self, credential: VerifiableCredential) {
        self.credentials.push(credential);
        self.updated_at = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
    }
    
    pub fn verify_credential(&self, credential_id: &str) -> bool {
        self.credentials.iter()
            .any(|cred| cred.id == credential_id && cred.verify_signature())
    }
}

// 可验证凭证
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifiableCredential {
    pub id: String,
    pub issuer: String,
    pub subject: String,
    pub claims: HashMap<String, String>,
    pub issued_at: u64,
    pub expires_at: Option<u64>,
    pub signature: Vec<u8>,
}

impl VerifiableCredential {
    pub fn new(
        issuer: String,
        subject: String,
        claims: HashMap<String, String>,
        expires_at: Option<u64>,
    ) -> Self {
        let id = Uuid::new_v4().to_string();
        let issued_at = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let mut credential = VerifiableCredential {
            id,
            issuer,
            subject,
            claims,
            issued_at,
            expires_at,
            signature: Vec::new(),
        };
        
        // 生成签名哈希
        let message_hash = credential.compute_hash();
        credential.signature = message_hash.to_vec();
        
        credential
    }
    
    fn compute_hash(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(self.id.as_bytes());
        hasher.update(self.issuer.as_bytes());
        hasher.update(self.subject.as_bytes());
        hasher.update(&bincode::serialize(&self.claims).unwrap_or_default());
        hasher.update(&self.issued_at.to_le_bytes());
        if let Some(expires) = self.expires_at {
            hasher.update(&expires.to_le_bytes());
        }
        hasher.finalize().into()
    }
    
    pub fn verify_signature(&self) -> bool {
        let computed_hash = self.compute_hash();
        self.signature == computed_hash.to_vec()
    }
    
    pub fn is_expired(&self) -> bool {
        if let Some(expires_at) = self.expires_at {
            let now = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs();
            now > expires_at
        } else {
            false
        }
    }
}

// 访问权限
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Permission {
    pub resource: String,
    pub action: String,
    pub conditions: Vec<String>,
}

// 角色
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Role {
    pub name: String,
    pub permissions: Vec<Permission>,
    pub description: String,
}

// 访问令牌
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AccessToken {
    pub token_id: String,
    pub subject: String,
    pub issuer: String,
    pub audience: Vec<String>,
    pub permissions: Vec<Permission>,
    pub issued_at: u64,
    pub expires_at: u64,
    pub signature: Vec<u8>,
}

impl AccessToken {
    pub fn new(
        subject: String,
        issuer: String,
        audience: Vec<String>,
        permissions: Vec<Permission>,
        expires_at: u64,
    ) -> Self {
        let token_id = Uuid::new_v4().to_string();
        let issued_at = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let mut token = AccessToken {
            token_id,
            subject,
            issuer,
            audience,
            permissions,
            issued_at,
            expires_at,
            signature: Vec::new(),
        };
        
        // 生成签名
        let message_hash = token.compute_hash();
        token.signature = message_hash.to_vec();
        
        token
    }
    
    fn compute_hash(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(self.token_id.as_bytes());
        hasher.update(self.subject.as_bytes());
        hasher.update(self.issuer.as_bytes());
        hasher.update(&bincode::serialize(&self.audience).unwrap_or_default());
        hasher.update(&bincode::serialize(&self.permissions).unwrap_or_default());
        hasher.update(&self.issued_at.to_le_bytes());
        hasher.update(&self.expires_at.to_le_bytes());
        hasher.finalize().into()
    }
    
    pub fn is_expired(&self) -> bool {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        now > self.expires_at
    }
    
    pub fn has_permission(&self, resource: &str, action: &str) -> bool {
        self.permissions.iter().any(|perm| {
            perm.resource == resource && perm.action == action
        })
    }
}

// 身份验证系统
pub struct AuthenticationSystem {
    identities: Arc<RwLock<HashMap<String, DigitalIdentity>>>,
    roles: Arc<RwLock<HashMap<String, Role>>>,
    active_tokens: Arc<RwLock<HashMap<String, AccessToken>>>,
    system_id: String,
}

impl AuthenticationSystem {
    pub fn new() -> Self {
        let system_id = format!("auth_system_{}", Uuid::new_v4());
        
        AuthenticationSystem {
            identities: Arc::new(RwLock::new(HashMap::new())),
            roles: Arc::new(RwLock::new(HashMap::new())),
            active_tokens: Arc::new(RwLock::new(HashMap::new())),
            system_id,
        }
    }
    
    pub fn register_identity(&self, public_key: Vec<u8>, attributes: HashMap<String, String>) -> String {
        let identity = DigitalIdentity::new(public_key, attributes);
        let id = identity.id.clone();
        
        let mut identities = self.identities.write().unwrap();
        identities.insert(id.clone(), identity);
        
        id
    }
    
    pub fn issue_credential(
        &self,
        subject_id: &str,
        claims: HashMap<String, String>,
        expires_at: Option<u64>,
    ) -> Result<VerifiableCredential, String> {
        let credential = VerifiableCredential::new(
            self.system_id.clone(),
            subject_id.to_string(),
            claims,
            expires_at,
        );
        
        // 将凭证添加到身份记录
        {
            let mut identities = self.identities.write().unwrap();
            if let Some(identity) = identities.get_mut(subject_id) {
                identity.add_credential(credential.clone());
            }
        }
        
        Ok(credential)
    }
    
    pub fn create_role(&self, name: String, permissions: Vec<Permission>, description: String) {
        let role = Role {
            name: name.clone(),
            permissions,
            description,
        };
        
        let mut roles = self.roles.write().unwrap();
        roles.insert(name, role);
    }
    
    pub fn authenticate(&self, identity_id: &str, challenge_response: &[u8]) -> Result<bool, String> {
        let identities = self.identities.read().unwrap();
        let _identity = identities.get(identity_id)
            .ok_or("身份不存在")?;
        
        // 简化的验证逻辑 - 在实际实现中需要使用密码学签名验证
        Ok(!challenge_response.is_empty())
    }
    
    pub fn authorize(
        &self,
        identity_id: &str,
        role_names: Vec<String>,
        audience: Vec<String>,
        expires_at: u64,
    ) -> Result<AccessToken, String> {
        // 检查身份是否存在
        {
            let identities = self.identities.read().unwrap();
            if !identities.contains_key(identity_id) {
                return Err("身份不存在".to_string());
            }
        }
        
        // 收集角色权限
        let mut permissions = Vec::new();
        {
            let roles = self.roles.read().unwrap();
            for role_name in role_names {
                if let Some(role) = roles.get(&role_name) {
                    permissions.extend(role.permissions.clone());
                }
            }
        }
        
        // 创建访问令牌
        let token = AccessToken::new(
            identity_id.to_string(),
            self.system_id.clone(),
            audience,
            permissions,
            expires_at,
        );
        
        // 存储活跃令牌
        {
            let mut active_tokens = self.active_tokens.write().unwrap();
            active_tokens.insert(token.token_id.clone(), token.clone());
        }
        
        Ok(token)
    }
    
    pub fn verify_token(&self, token_id: &str) -> Result<AccessToken, String> {
        let active_tokens = self.active_tokens.read().unwrap();
        let token = active_tokens.get(token_id)
            .ok_or("令牌不存在")?;
        
        if token.is_expired() {
            return Err("令牌已过期".to_string());
        }
        
        Ok(token.clone())
    }
    
    pub fn check_permission(&self, token_id: &str, resource: &str, action: &str) -> Result<bool, String> {
        let token = self.verify_token(token_id)?;
        Ok(token.has_permission(resource, action))
    }
    
    pub fn revoke_token(&self, token_id: &str) -> Result<(), String> {
        let mut active_tokens = self.active_tokens.write().unwrap();
        active_tokens.remove(token_id);
        Ok(())
    }
    
    pub fn cleanup_expired_tokens(&self) {
        let mut active_tokens = self.active_tokens.write().unwrap();
        active_tokens.retain(|_, token| !token.is_expired());
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建身份验证系统
    let auth_system = AuthenticationSystem::new();
    
    // 模拟用户公钥
    let user_public_key = b"user_public_key_example".to_vec();
    
    // 注册用户身份
    let mut user_attributes = HashMap::new();
    user_attributes.insert("name".to_string(), "Alice".to_string());
    user_attributes.insert("department".to_string(), "Engineering".to_string());
    user_attributes.insert("level".to_string(), "Senior".to_string());
    
    let user_id = auth_system.register_identity(user_public_key, user_attributes);
    println!("用户身份注册完成: {}", user_id);
    
    // 创建角色和权限
    let permissions = vec![
        Permission {
            resource: "smart_contract".to_string(),
            action: "deploy".to_string(),
            conditions: vec!["department=Engineering".to_string()],
        },
        Permission {
            resource: "blockchain_data".to_string(),
            action: "read".to_string(),
            conditions: vec![],
        },
    ];
    
    auth_system.create_role(
        "developer".to_string(),
        permissions,
        "Smart contract developer role".to_string(),
    );
    
    // 身份验证
    let challenge_response = b"valid_signature";
    let auth_result = auth_system.authenticate(&user_id, challenge_response)?;
    
    if auth_result {
        println!("身份验证成功");
        
        // 授权访问令牌
        let expires_at = SystemTime::now()
            .duration_since(UNIX_EPOCH)?
            .as_secs() + 3600; // 1小时后过期
        
        let token = auth_system.authorize(
            &user_id,
            vec!["developer".to_string()],
            vec!["web3_platform".to_string()],
            expires_at,
        )?;
        
        println!("访问令牌颁发成功: {}", token.token_id);
        
        // 检查权限
        let can_deploy = auth_system.check_permission(
            &token.token_id,
            "smart_contract",
            "deploy",
        )?;
        
        println!("是否可以部署智能合约: {}", can_deploy);
        
        // 验证令牌
        let verified_token = auth_system.verify_token(&token.token_id)?;
        println!("令牌验证成功: {}", verified_token.subject);
    } else {
        println!("身份验证失败");
    }
    
    Ok(())
}
```

## 相关链接

- [密码学安全设计](02_Cryptographic_Security.md)
- [安全审计监控](03_Security_Audit.md)
- [密码学基础](../../01_Theoretical_Foundations/02_Cryptographic_Foundations/)
- [安全架构总览](../)
- [架构设计总览](../../)

---

*身份验证与授权为Web3提供安全可靠的访问控制机制。*
