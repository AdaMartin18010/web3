# 数字身份 (Digital Identity)

## 概述

数字身份是Web3生态系统的基础设施，为用户提供去中心化的身份管理和验证服务。本目录涵盖了现代数字身份系统的核心技术和方法。

## 目录结构

```text
02_Digital_Identity/
├── 01_Decentralized_Identifiers/        # 去中心化标识符
│   ├── DID_Methods/                     # DID方法
│   ├── DID_Documents/                   # DID文档
│   ├── DID_Resolution/                  # DID解析
│   └── DID_Operations/                  # DID操作
├── 02_Verifiable_Credentials/           # 可验证凭证
│   ├── VC_Data_Model/                   # VC数据模型
│   ├── VC_Issuance/                     # VC发行
│   ├── VC_Verification/                 # VC验证
│   └── VC_Revocation/                   # VC撤销
├── 03_Zero_Knowledge_Identity/          # 零知识身份
│   ├── ZK_Proofs_for_Identity/          # 身份零知识证明
│   ├── Age_Verification/                # 年龄验证
│   ├── Credential_Proofs/               # 凭证证明
│   └── Privacy_Preserving_KYC/          # 隐私保护KYC
├── 04_Identity_Wallets/                 # 身份钱包
│   ├── Wallet_Architecture/             # 钱包架构
│   ├── Key_Management/                  # 密钥管理
│   ├── Credential_Storage/              # 凭证存储
│   └── User_Experience/                 # 用户体验
├── 05_Identity_Governance/              # 身份治理
│   ├── Governance_Models/               # 治理模型
│   ├── Trust_Frameworks/                # 信任框架
│   ├── Compliance_Standards/            # 合规标准
│   └── Dispute_Resolution/              # 争议解决
└── 06_Applications/                     # 应用场景
    ├── DeFi_Identity/                   # DeFi身份
    ├── DAO_Governance/                  # DAO治理
    ├── Supply_Chain/                    # 供应链
    └── Healthcare/                      # 医疗健康
```

## 核心概念

### 1. 去中心化标识符 (DID)

**定义：**
DID是一种新型的标识符，由用户自主创建、拥有和控制，不依赖于任何中央机构。

**特点：**

- 去中心化控制
- 持久性
- 可解析性
- 可验证性

**DID格式：**

```text
did:method:method-specific-identifier
```

### 2. 可验证凭证 (VC)

**定义：**
VC是数字化的凭证，包含关于主体的声明，由发行者签名，可以被验证者验证。

**组成部分：**

- 元数据 (Metadata)
- 声明 (Claims)
- 证明 (Proof)

### 3. 零知识身份

**原理：**
使用零知识证明技术，证明者可以向验证者证明某个陈述为真，而无需透露任何额外信息。

**应用场景：**

- 年龄验证
- 资格证明
- 隐私保护KYC

## 技术实现

### Rust - DID实现

```rust
use serde::{Deserialize, Serialize};
use sha2::{Sha256, Digest};
use ed25519_dalek::{Keypair, PublicKey, SecretKey, Signature, Verifier};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DIDDocument {
    pub id: String,
    pub controller: Option<String>,
    pub verification_methods: Vec<VerificationMethod>,
    pub authentication: Vec<String>,
    pub assertion_method: Vec<String>,
    pub key_agreement: Vec<String>,
    pub service_endpoints: Vec<Service>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationMethod {
    pub id: String,
    pub controller: String,
    pub key_type: String,
    pub public_key: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Service {
    pub id: String,
    pub service_type: String,
    pub service_endpoint: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DID {
    pub method: String,
    pub identifier: String,
}

impl DID {
    pub fn new(method: String, identifier: String) -> Self {
        Self { method, identifier }
    }
    
    pub fn to_string(&self) -> String {
        format!("did:{}:{}", self.method, self.identifier)
    }
    
    pub fn from_string(did_string: &str) -> Result<Self, String> {
        let parts: Vec<&str> = did_string.split(':').collect();
        if parts.len() != 3 || parts[0] != "did" {
            return Err("Invalid DID format".to_string());
        }
        
        Ok(Self {
            method: parts[1].to_string(),
            identifier: parts[2].to_string(),
        })
    }
}

pub struct DIDRegistry {
    documents: HashMap<String, DIDDocument>,
    keypairs: HashMap<String, Keypair>,
}

impl DIDRegistry {
    pub fn new() -> Self {
        Self {
            documents: HashMap::new(),
            keypairs: HashMap::new(),
        }
    }
    
    pub fn create_did(&mut self, method: &str) -> Result<DID, String> {
        // 生成密钥对
        let keypair = Keypair::generate(&mut rand::thread_rng());
        
        // 生成DID标识符
        let public_key_bytes = keypair.public.to_bytes();
        let mut hasher = Sha256::new();
        hasher.update(&public_key_bytes);
        let identifier = format!("{:x}", hasher.finalize());
        
        let did = DID::new(method.to_string(), identifier.clone());
        let did_string = did.to_string();
        
        // 创建DID文档
        let verification_method = VerificationMethod {
            id: format!("{}#keys-1", did_string),
            controller: did_string.clone(),
            key_type: "Ed25519VerificationKey2018".to_string(),
            public_key: base64::encode(&public_key_bytes),
        };
        
        let document = DIDDocument {
            id: did_string.clone(),
            controller: Some(did_string.clone()),
            verification_methods: vec![verification_method.clone()],
            authentication: vec![verification_method.id.clone()],
            assertion_method: vec![verification_method.id.clone()],
            key_agreement: vec![],
            service_endpoints: vec![],
        };
        
        // 存储DID文档和密钥对
        self.documents.insert(did_string.clone(), document);
        self.keypairs.insert(did_string, keypair);
        
        Ok(did)
    }
    
    pub fn resolve_did(&self, did: &DID) -> Option<&DIDDocument> {
        let did_string = did.to_string();
        self.documents.get(&did_string)
    }
    
    pub fn sign_message(&self, did: &DID, message: &[u8]) -> Result<Signature, String> {
        let did_string = did.to_string();
        let keypair = self.keypairs.get(&did_string)
            .ok_or("DID not found")?;
        
        Ok(keypair.sign(message))
    }
    
    pub fn verify_signature(&self, did: &DID, message: &[u8], signature: &Signature) -> Result<bool, String> {
        let document = self.resolve_did(did)
            .ok_or("DID not found")?;
        
        if let Some(verification_method) = document.verification_methods.first() {
            let public_key_bytes = base64::decode(&verification_method.public_key)
                .map_err(|_| "Invalid public key")?;
            
            let public_key = PublicKey::from_bytes(&public_key_bytes)
                .map_err(|_| "Invalid public key")?;
            
            Ok(public_key.verify(message, signature).is_ok())
        } else {
            Err("No verification method found".to_string())
        }
    }
    
    pub fn update_did_document(&mut self, did: &DID, document: DIDDocument) -> Result<(), String> {
        let did_string = did.to_string();
        
        // 验证文档所有权
        if document.id != did_string {
            return Err("Document ID mismatch".to_string());
        }
        
        // 验证签名（简化实现）
        self.documents.insert(did_string, document);
        Ok(())
    }
    
    pub fn deactivate_did(&mut self, did: &DID) -> Result<(), String> {
        let did_string = did.to_string();
        
        self.documents.remove(&did_string);
        self.keypairs.remove(&did_string);
        
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_did_creation() {
        let mut registry = DIDRegistry::new();
        let did = registry.create_did("example").unwrap();
        
        assert_eq!(did.method, "example");
        assert!(!did.identifier.is_empty());
        
        let did_string = did.to_string();
        assert!(did_string.starts_with("did:example:"));
    }
    
    #[test]
    fn test_did_resolution() {
        let mut registry = DIDRegistry::new();
        let did = registry.create_did("example").unwrap();
        
        let document = registry.resolve_did(&did);
        assert!(document.is_some());
        
        let doc = document.unwrap();
        assert_eq!(doc.id, did.to_string());
        assert_eq!(doc.verification_methods.len(), 1);
    }
    
    #[test]
    fn test_did_signing() {
        let mut registry = DIDRegistry::new();
        let did = registry.create_did("example").unwrap();
        
        let message = b"Hello, World!";
        let signature = registry.sign_message(&did, message).unwrap();
        
        let is_valid = registry.verify_signature(&did, message, &signature).unwrap();
        assert!(is_valid);
    }
    
    #[test]
    fn test_did_parsing() {
        let did_string = "did:example:123456789abcdef";
        let did = DID::from_string(did_string).unwrap();
        
        assert_eq!(did.method, "example");
        assert_eq!(did.identifier, "123456789abcdef");
        assert_eq!(did.to_string(), did_string);
    }
}
```

### Solidity - 可验证凭证合约

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/utils/Strings.sol";

contract VerifiableCredentials is Ownable {
    using Strings for uint256;
    
    struct Credential {
        string id;
        string issuer;
        string subject;
        string credentialType;
        uint256 issuanceDate;
        uint256 expirationDate;
        bool revoked;
        string dataHash;
    }
    
    struct Proof {
        string type_;
        string created;
        string verificationMethod;
        string proofPurpose;
        string proofValue;
    }
    
    mapping(string => Credential) public credentials;
    mapping(string => Proof) public proofs;
    mapping(string => bool) public revokedCredentials;
    
    mapping(address => bool) public authorizedIssuers;
    mapping(address => string[]) public issuerCredentials;
    
    event CredentialIssued(
        string indexed credentialId,
        string issuer,
        string subject,
        string credentialType
    );
    
    event CredentialRevoked(string indexed credentialId, string reason);
    event IssuerAuthorized(address indexed issuer);
    event IssuerRevoked(address indexed issuer);
    
    modifier onlyAuthorizedIssuer() {
        require(authorizedIssuers[msg.sender], "Not authorized issuer");
        _;
    }
    
    constructor() {
        authorizedIssuers[msg.sender] = true;
    }
    
    function authorizeIssuer(address issuer) external onlyOwner {
        authorizedIssuers[issuer] = true;
        emit IssuerAuthorized(issuer);
    }
    
    function revokeIssuer(address issuer) external onlyOwner {
        authorizedIssuers[issuer] = false;
        emit IssuerRevoked(issuer);
    }
    
    function issueCredential(
        string memory credentialId,
        string memory subject,
        string memory credentialType,
        uint256 expirationDate,
        string memory dataHash,
        string memory proofType,
        string memory proofValue
    ) external onlyAuthorizedIssuer {
        require(bytes(credentialId).length > 0, "Invalid credential ID");
        require(bytes(subject).length > 0, "Invalid subject");
        require(expirationDate > block.timestamp, "Invalid expiration date");
        require(!credentials[credentialId].revoked, "Credential already exists");
        
        Credential memory credential = Credential({
            id: credentialId,
            issuer: _addressToString(msg.sender),
            subject: subject,
            credentialType: credentialType,
            issuanceDate: block.timestamp,
            expirationDate: expirationDate,
            revoked: false,
            dataHash: dataHash
        });
        
        Proof memory proof = Proof({
            type_: proofType,
            created: _timestampToString(block.timestamp),
            verificationMethod: _addressToString(msg.sender),
            proofPurpose: "assertionMethod",
            proofValue: proofValue
        });
        
        credentials[credentialId] = credential;
        proofs[credentialId] = proof;
        issuerCredentials[msg.sender].push(credentialId);
        
        emit CredentialIssued(credentialId, _addressToString(msg.sender), subject, credentialType);
    }
    
    function revokeCredential(string memory credentialId, string memory reason) external {
        require(bytes(credentialId).length > 0, "Invalid credential ID");
        
        Credential storage credential = credentials[credentialId];
        require(bytes(credential.id).length > 0, "Credential not found");
        require(!credential.revoked, "Credential already revoked");
        
        // 只有发行者或合约所有者可以撤销
        require(
            keccak256(bytes(credential.issuer)) == keccak256(bytes(_addressToString(msg.sender))) ||
            msg.sender == owner(),
            "Not authorized to revoke"
        );
        
        credential.revoked = true;
        revokedCredentials[credentialId] = true;
        
        emit CredentialRevoked(credentialId, reason);
    }
    
    function verifyCredential(string memory credentialId) external view returns (bool) {
        Credential memory credential = credentials[credentialId];
        
        if (bytes(credential.id).length == 0) {
            return false; // 凭证不存在
        }
        
        if (credential.revoked) {
            return false; // 凭证已撤销
        }
        
        if (block.timestamp > credential.expirationDate) {
            return false; // 凭证已过期
        }
        
        return true;
    }
    
    function getCredential(string memory credentialId) external view returns (
        string memory id,
        string memory issuer,
        string memory subject,
        string memory credentialType,
        uint256 issuanceDate,
        uint256 expirationDate,
        bool revoked,
        string memory dataHash
    ) {
        Credential memory credential = credentials[credentialId];
        return (
            credential.id,
            credential.issuer,
            credential.subject,
            credential.credentialType,
            credential.issuanceDate,
            credential.expirationDate,
            credential.revoked,
            credential.dataHash
        );
    }
    
    function getProof(string memory credentialId) external view returns (
        string memory type_,
        string memory created,
        string memory verificationMethod,
        string memory proofPurpose,
        string memory proofValue
    ) {
        Proof memory proof = proofs[credentialId];
        return (
            proof.type_,
            proof.created,
            proof.verificationMethod,
            proof.proofPurpose,
            proof.proofValue
        );
    }
    
    function getIssuerCredentials(address issuer) external view returns (string[] memory) {
        return issuerCredentials[issuer];
    }
    
    function isAuthorizedIssuer(address issuer) external view returns (bool) {
        return authorizedIssuers[issuer];
    }
    
    function _addressToString(address addr) internal pure returns (string memory) {
        return string(abi.encodePacked("did:ethr:", _toHexString(addr)));
    }
    
    function _timestampToString(uint256 timestamp) internal pure returns (string memory) {
        return timestamp.toString();
    }
    
    function _toHexString(address addr) internal pure returns (string memory) {
        bytes memory buffer = new bytes(40);
        for (uint256 i = 0; i < 20; i++) {
            bytes1 b = bytes1(uint8(uint256(uint160(addr)) / (2**(8*(19 - i)))));
            bytes1 hi = bytes1(uint8(b) / 16);
            bytes1 lo = bytes1(uint8(b) - 16 * uint8(hi));
            buffer[2*i] = _char(hi);
            buffer[2*i+1] = _char(lo);
        }
        return string(buffer);
    }
    
    function _char(bytes1 b) internal pure returns (bytes1 c) {
        if (uint8(b) < 10) return bytes1(uint8(b) + 0x30);
        else return bytes1(uint8(b) + 0x57);
    }
}
```

### Python - 零知识身份验证

```python
import hashlib
import json
import time
from typing import Dict, List, Optional
from dataclasses import dataclass
from enum import Enum
import secrets

class CredentialType(Enum):
    AGE_VERIFICATION = "age_verification"
    IDENTITY_VERIFICATION = "identity_verification"
    QUALIFICATION = "qualification"
    MEMBERSHIP = "membership"

@dataclass
class Credential:
    id: str
    issuer: str
    subject: str
    credential_type: CredentialType
    claims: Dict
    issuance_date: int
    expiration_date: int
    signature: str

@dataclass
class ZKProof:
    statement: str
    proof_data: Dict
    public_inputs: List
    verification_key: str

class ZeroKnowledgeIdentity:
    def __init__(self):
        self.credentials: Dict[str, Credential] = {}
        self.proofs: Dict[str, ZKProof] = {}
        self.trusted_issuers: List[str] = []
        
    def issue_credential(self, issuer: str, subject: str, credential_type: CredentialType, claims: Dict) -> Credential:
        """发行凭证"""
        credential_id = self._generate_credential_id(issuer, subject, credential_type)
        
        credential = Credential(
            id=credential_id,
            issuer=issuer,
            subject=subject,
            credential_type=credential_type,
            claims=claims,
            issuance_date=int(time.time()),
            expiration_date=int(time.time()) + 365 * 24 * 3600,  # 1年有效期
            signature=self._sign_credential(issuer, claims)
        )
        
        self.credentials[credential_id] = credential
        return credential
    
    def create_age_proof(self, credential_id: str, min_age: int, max_age: Optional[int] = None) -> ZKProof:
        """创建年龄验证的零知识证明"""
        credential = self.credentials.get(credential_id)
        if not credential or credential.credential_type != CredentialType.AGE_VERIFICATION:
            raise ValueError("Invalid credential for age verification")
        
        age = credential.claims.get('age')
        if not age:
            raise ValueError("Age claim not found")
        
        # 简化的零知识证明：证明年龄在指定范围内
        if max_age:
            proof_statement = f"age >= {min_age} AND age <= {max_age}"
        else:
            proof_statement = f"age >= {min_age}"
        
        # 生成证明数据（实际应用中应使用真正的零知识证明系统）
        proof_data = {
            'age': age,
            'min_age': min_age,
            'max_age': max_age,
            'proof_hash': self._hash_proof_data(age, min_age, max_age)
        }
        
        zk_proof = ZKProof(
            statement=proof_statement,
            proof_data=proof_data,
            public_inputs=[min_age, max_age] if max_age else [min_age],
            verification_key=self._generate_verification_key()
        )
        
        proof_id = self._generate_proof_id(credential_id, proof_statement)
        self.proofs[proof_id] = zk_proof
        
        return zk_proof
    
    def verify_age_proof(self, proof_id: str, min_age: int, max_age: Optional[int] = None) -> bool:
        """验证年龄证明"""
        zk_proof = self.proofs.get(proof_id)
        if not zk_proof:
            return False
        
        # 验证证明语句
        expected_statement = f"age >= {min_age}"
        if max_age:
            expected_statement += f" AND age <= {max_age}"
        
        if zk_proof.statement != expected_statement:
            return False
        
        # 验证证明数据
        age = zk_proof.proof_data.get('age')
        if not age:
            return False
        
        if age < min_age:
            return False
        
        if max_age and age > max_age:
            return False
        
        # 验证证明哈希
        expected_hash = self._hash_proof_data(age, min_age, max_age)
        if zk_proof.proof_data.get('proof_hash') != expected_hash:
            return False
        
        return True
    
    def create_qualification_proof(self, credential_id: str, required_qualifications: List[str]) -> ZKProof:
        """创建资格证明的零知识证明"""
        credential = self.credentials.get(credential_id)
        if not credential or credential.credential_type != CredentialType.QUALIFICATION:
            raise ValueError("Invalid credential for qualification verification")
        
        qualifications = credential.claims.get('qualifications', [])
        
        # 检查是否具有所需资格
        has_required = all(q in qualifications for q in required_qualifications)
        
        proof_statement = f"has_qualifications: {', '.join(required_qualifications)}"
        
        proof_data = {
            'qualifications': qualifications,
            'required_qualifications': required_qualifications,
            'has_required': has_required,
            'proof_hash': self._hash_qualification_proof(qualifications, required_qualifications)
        }
        
        zk_proof = ZKProof(
            statement=proof_statement,
            proof_data=proof_data,
            public_inputs=required_qualifications,
            verification_key=self._generate_verification_key()
        )
        
        proof_id = self._generate_proof_id(credential_id, proof_statement)
        self.proofs[proof_id] = zk_proof
        
        return zk_proof
    
    def verify_qualification_proof(self, proof_id: str, required_qualifications: List[str]) -> bool:
        """验证资格证明"""
        zk_proof = self.proofs.get(proof_id)
        if not zk_proof:
            return False
        
        # 验证证明语句
        expected_statement = f"has_qualifications: {', '.join(required_qualifications)}"
        if zk_proof.statement != expected_statement:
            return False
        
        # 验证证明数据
        qualifications = zk_proof.proof_data.get('qualifications', [])
        has_required = zk_proof.proof_data.get('has_required', False)
        
        if not has_required:
            return False
        
        # 验证所有必需资格都存在
        if not all(q in qualifications for q in required_qualifications):
            return False
        
        # 验证证明哈希
        expected_hash = self._hash_qualification_proof(qualifications, required_qualifications)
        if zk_proof.proof_data.get('proof_hash') != expected_hash:
            return False
        
        return True
    
    def create_membership_proof(self, credential_id: str, organization: str) -> ZKProof:
        """创建成员身份证明"""
        credential = self.credentials.get(credential_id)
        if not credential or credential.credential_type != CredentialType.MEMBERSHIP:
            raise ValueError("Invalid credential for membership verification")
        
        membership_org = credential.claims.get('organization')
        if membership_org != organization:
            raise ValueError("Organization mismatch")
        
        proof_statement = f"is_member_of: {organization}"
        
        proof_data = {
            'organization': organization,
            'membership_status': 'active',
            'proof_hash': self._hash_membership_proof(organization)
        }
        
        zk_proof = ZKProof(
            statement=proof_statement,
            proof_data=proof_data,
            public_inputs=[organization],
            verification_key=self._generate_verification_key()
        )
        
        proof_id = self._generate_proof_id(credential_id, proof_statement)
        self.proofs[proof_id] = zk_proof
        
        return zk_proof
    
    def verify_membership_proof(self, proof_id: str, organization: str) -> bool:
        """验证成员身份证明"""
        zk_proof = self.proofs.get(proof_id)
        if not zk_proof:
            return False
        
        # 验证证明语句
        expected_statement = f"is_member_of: {organization}"
        if zk_proof.statement != expected_statement:
            return False
        
        # 验证证明数据
        proof_org = zk_proof.proof_data.get('organization')
        membership_status = zk_proof.proof_data.get('membership_status')
        
        if proof_org != organization or membership_status != 'active':
            return False
        
        # 验证证明哈希
        expected_hash = self._hash_membership_proof(organization)
        if zk_proof.proof_data.get('proof_hash') != expected_hash:
            return False
        
        return True
    
    def _generate_credential_id(self, issuer: str, subject: str, credential_type: CredentialType) -> str:
        """生成凭证ID"""
        data = f"{issuer}:{subject}:{credential_type.value}:{int(time.time())}"
        return hashlib.sha256(data.encode()).hexdigest()
    
    def _generate_proof_id(self, credential_id: str, statement: str) -> str:
        """生成证明ID"""
        data = f"{credential_id}:{statement}:{int(time.time())}"
        return hashlib.sha256(data.encode()).hexdigest()
    
    def _sign_credential(self, issuer: str, claims: Dict) -> str:
        """签名凭证（简化实现）"""
        data = json.dumps(claims, sort_keys=True)
        return hashlib.sha256(f"{issuer}:{data}".encode()).hexdigest()
    
    def _hash_proof_data(self, age: int, min_age: int, max_age: Optional[int]) -> str:
        """哈希证明数据"""
        data = f"{age}:{min_age}:{max_age}"
        return hashlib.sha256(data.encode()).hexdigest()
    
    def _hash_qualification_proof(self, qualifications: List[str], required: List[str]) -> str:
        """哈希资格证明数据"""
        data = f"{','.join(qualifications)}:{','.join(required)}"
        return hashlib.sha256(data.encode()).hexdigest()
    
    def _hash_membership_proof(self, organization: str) -> str:
        """哈希成员身份证明数据"""
        return hashlib.sha256(organization.encode()).hexdigest()
    
    def _generate_verification_key(self) -> str:
        """生成验证密钥"""
        return secrets.token_hex(32)

# 使用示例
def main():
    zk_identity = ZeroKnowledgeIdentity()
    
    # 发行年龄验证凭证
    age_credential = zk_identity.issue_credential(
        issuer="government",
        subject="alice",
        credential_type=CredentialType.AGE_VERIFICATION,
        claims={"age": 25, "nationality": "US"}
    )
    
    # 创建年龄证明
    age_proof = zk_identity.create_age_proof(age_credential.id, min_age=18, max_age=65)
    
    # 验证年龄证明
    is_valid = zk_identity.verify_age_proof(age_proof.statement, min_age=18, max_age=65)
    print(f"Age proof valid: {is_valid}")
    
    # 发行资格凭证
    qualification_credential = zk_identity.issue_credential(
        issuer="university",
        subject="bob",
        credential_type=CredentialType.QUALIFICATION,
        claims={"qualifications": ["bachelor", "master", "phd"]}
    )
    
    # 创建资格证明
    qualification_proof = zk_identity.create_qualification_proof(
        qualification_credential.id, 
        required_qualifications=["bachelor", "master"]
    )
    
    # 验证资格证明
    is_qualified = zk_identity.verify_qualification_proof(
        qualification_proof.statement, 
        required_qualifications=["bachelor", "master"]
    )
    print(f"Qualification proof valid: {is_qualified}")

if __name__ == "__main__":
    main()
```

## 最佳实践

### 1. 隐私保护

- 最小化数据收集
- 零知识证明应用
- 数据加密存储
- 用户控制权

### 2. 安全设计

- 多重签名机制
- 密钥管理
- 防重放攻击
- 安全审计

### 3. 用户体验

- 简化操作流程
- 跨平台兼容
- 离线功能
- 恢复机制

## 总结

数字身份是Web3生态系统的基础设施，为用户提供安全、隐私、可控的身份管理服务。通过DID、VC、零知识证明等技术，实现了真正去中心化的身份系统。

随着技术的不断发展，数字身份将在更多领域得到应用，为用户提供更好的身份体验。
