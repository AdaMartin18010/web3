# 去中心化身份理论分析

## 1. 去中心化身份基础

### 1.1 基本定义

**定义 1.1 (去中心化身份)** 用户拥有和控制，不依赖中央权威的数字身份系统。

**定义 1.2 (DID)** 去中心化标识符，全球唯一的数字标识符。

**定义 1.3 (可验证凭证)** 由发行方签名的数字凭证，包含关于主体的声明。

### 1.2 身份模型

**定义 1.4 (自主身份)** 用户完全控制自己的身份数据和凭证。

**定义 1.5 (最小披露)** 只披露必要的信息，保护用户隐私。

**定义 1.6 (可移植性)** 身份可以在不同系统间自由转移。

## 2. DID标准

### 2.1 DID结构

```python
import hashlib
import json
import base64
from typing import Dict, List, Optional

class DID:
    def __init__(self, method: str, identifier: str):
        """
        初始化DID
        method: DID方法
        identifier: 唯一标识符
        """
        self.method = method
        self.identifier = identifier
        self.did = f"did:{method}:{identifier}"
        self.document = None
    
    def create_did_document(self, public_keys: List[Dict], services: List[Dict] = None) -> Dict:
        """创建DID文档"""
        self.document = {
            "@context": ["https://www.w3.org/ns/did/v1"],
            "id": self.did,
            "verificationMethod": public_keys,
            "authentication": [],
            "assertionMethod": [],
            "keyAgreement": [],
            "service": services or []
        }
        
        # 添加验证方法到相应类别
        for key in public_keys:
            if key.get("type") == "Ed25519VerificationKey2018":
                self.document["authentication"].append(key["id"])
                self.document["assertionMethod"].append(key["id"])
            elif key.get("type") == "X25519KeyAgreementKey2019":
                self.document["keyAgreement"].append(key["id"])
        
        return self.document
    
    def resolve_did(self) -> Optional[Dict]:
        """解析DID"""
        # 根据DID方法解析DID文档
        if self.method == "example":
            return self.resolve_example_did()
        elif self.method == "web":
            return self.resolve_web_did()
        else:
            return self.resolve_generic_did()
    
    def resolve_example_did(self) -> Dict:
        """解析example方法DID"""
        # 从区块链或IPFS解析
        return self.document
    
    def resolve_web_did(self) -> Dict:
        """解析web方法DID"""
        # 从Web服务器解析
        import requests
        try:
            response = requests.get(f"https://{self.identifier}/.well-known/did.json")
            return response.json()
        except:
            return None
    
    def resolve_generic_did(self) -> Dict:
        """解析通用DID"""
        # 根据DID方法规范解析
        return self.document
    
    def update_did_document(self, updates: Dict):
        """更新DID文档"""
        if self.document:
            self.document.update(updates)
    
    def deactivate_did(self):
        """停用DID"""
        if self.document:
            self.document["deactivated"] = True
```

### 2.2 DID方法实现

```python
class DIDMethod:
    def __init__(self, method_name: str):
        self.method_name = method_name
    
    def create_did(self, identifier: str) -> DID:
        """创建DID"""
        return DID(self.method_name, identifier)
    
    def validate_did(self, did: str) -> bool:
        """验证DID格式"""
        if not did.startswith(f"did:{self.method_name}:"):
            return False
        
        # 验证标识符格式
        identifier = did.split(":", 2)[2]
        return self.validate_identifier(identifier)
    
    def validate_identifier(self, identifier: str) -> bool:
        """验证标识符"""
        # 基本格式验证
        if not identifier or len(identifier) < 1:
            return False
        
        # 检查字符集
        valid_chars = set("abcdefghijklmnopqrstuvwxyz0123456789-._")
        return all(c in valid_chars for c in identifier.lower())
    
    def generate_identifier(self) -> str:
        """生成唯一标识符"""
        import secrets
        return secrets.token_urlsafe(16)
```

## 3. 可验证凭证

### 3.1 凭证结构

```python
class VerifiableCredential:
    def __init__(self, issuer: str, subject: str, claims: Dict):
        """
        初始化可验证凭证
        issuer: 发行方DID
        subject: 主体DID
        claims: 声明内容
        """
        self.issuer = issuer
        self.subject = subject
        self.claims = claims
        self.credential = None
    
    def create_credential(self, credential_type: List[str], 
                         expiration_date: str = None) -> Dict:
        """创建凭证"""
        self.credential = {
            "@context": [
                "https://www.w3.org/2018/credentials/v1",
                "https://www.w3.org/2018/credentials/examples/v1"
            ],
            "id": self.generate_credential_id(),
            "type": credential_type,
            "issuer": self.issuer,
            "issuanceDate": self.get_current_time(),
            "credentialSubject": {
                "id": self.subject,
                **self.claims
            }
        }
        
        if expiration_date:
            self.credential["expirationDate"] = expiration_date
        
        return self.credential
    
    def sign_credential(self, private_key: str) -> Dict:
        """签名凭证"""
        if not self.credential:
            raise ValueError("Credential not created")
        
        # 创建可验证凭证
        verifiable_credential = {
            **self.credential,
            "proof": self.create_proof(private_key)
        }
        
        return verifiable_credential
    
    def create_proof(self, private_key: str) -> Dict:
        """创建证明"""
        # 计算凭证哈希
        credential_hash = self.hash_credential()
        
        # 使用私钥签名
        signature = self.sign_data(credential_hash, private_key)
        
        return {
            "type": "Ed25519Signature2018",
            "created": self.get_current_time(),
            "verificationMethod": f"{self.issuer}#key-1",
            "proofPurpose": "assertionMethod",
            "jws": signature
        }
    
    def verify_credential(self, verifiable_credential: Dict) -> bool:
        """验证凭证"""
        # 验证签名
        proof = verifiable_credential.get("proof")
        if not proof:
            return False
        
        # 验证签名
        signature = proof.get("jws")
        public_key = self.get_public_key(verifiable_credential["issuer"])
        
        credential_hash = self.hash_credential(verifiable_credential)
        return self.verify_signature(credential_hash, signature, public_key)
    
    def hash_credential(self, credential: Dict = None) -> str:
        """哈希凭证"""
        if credential is None:
            credential = self.credential
        
        # 规范化JSON
        normalized = json.dumps(credential, sort_keys=True, separators=(',', ':'))
        
        # 计算哈希
        return hashlib.sha256(normalized.encode()).hexdigest()
    
    def sign_data(self, data: str, private_key: str) -> str:
        """签名数据"""
        # 使用Ed25519签名
        import nacl.signing
        
        signing_key = nacl.signing.SigningKey(private_key.encode())
        signature = signing_key.sign(data.encode())
        
        return base64.b64encode(signature.signature).decode()
    
    def verify_signature(self, data: str, signature: str, public_key: str) -> bool:
        """验证签名"""
        import nacl.signing
        
        try:
            verify_key = nacl.signing.VerifyKey(public_key.encode())
            verify_key.verify(data.encode(), base64.b64decode(signature))
            return True
        except:
            return False
    
    def generate_credential_id(self) -> str:
        """生成凭证ID"""
        import secrets
        return f"urn:uuid:{secrets.uuid4()}"
    
    def get_current_time(self) -> str:
        """获取当前时间"""
        from datetime import datetime
        return datetime.utcnow().isoformat() + "Z"
```

### 3.2 凭证演示

```python
class CredentialPresentation:
    def __init__(self):
        self.verifiable_credentials = []
    
    def add_credential(self, verifiable_credential: Dict):
        """添加凭证"""
        self.verifiable_credentials.append(verifiable_credential)
    
    def create_presentation(self, holder: str, 
                          selected_credentials: List[str] = None) -> Dict:
        """创建凭证演示"""
        if selected_credentials is None:
            selected_credentials = [cred["id"] for cred in self.verifiable_credentials]
        
        # 选择凭证
        selected = [cred for cred in self.verifiable_credentials 
                   if cred["id"] in selected_credentials]
        
        presentation = {
            "@context": [
                "https://www.w3.org/2018/credentials/v1",
                "https://www.w3.org/2018/credentials/examples/v1"
            ],
            "type": ["VerifiablePresentation"],
            "holder": holder,
            "verifiableCredential": selected
        }
        
        return presentation
    
    def sign_presentation(self, presentation: Dict, private_key: str) -> Dict:
        """签名演示"""
        # 计算演示哈希
        presentation_hash = self.hash_presentation(presentation)
        
        # 签名
        signature = self.sign_data(presentation_hash, private_key)
        
        # 添加证明
        presentation["proof"] = {
            "type": "Ed25519Signature2018",
            "created": self.get_current_time(),
            "verificationMethod": f"{presentation['holder']}#key-1",
            "proofPurpose": "authentication",
            "jws": signature
        }
        
        return presentation
    
    def verify_presentation(self, presentation: Dict) -> bool:
        """验证演示"""
        # 验证演示签名
        proof = presentation.get("proof")
        if not proof:
            return False
        
        signature = proof.get("jws")
        holder = presentation.get("holder")
        public_key = self.get_public_key(holder)
        
        presentation_hash = self.hash_presentation(presentation)
        if not self.verify_signature(presentation_hash, signature, public_key):
            return False
        
        # 验证所有凭证
        credentials = presentation.get("verifiableCredential", [])
        for credential in credentials:
            if not self.verify_credential(credential):
                return False
        
        return True
    
    def hash_presentation(self, presentation: Dict) -> str:
        """哈希演示"""
        # 移除证明部分
        presentation_copy = presentation.copy()
        presentation_copy.pop("proof", None)
        
        # 规范化JSON
        normalized = json.dumps(presentation_copy, sort_keys=True, separators=(',', ':'))
        
        # 计算哈希
        return hashlib.sha256(normalized.encode()).hexdigest()
```

## 4. 身份钱包

### 4.1 钱包实现

```python
class IdentityWallet:
    def __init__(self, seed: str = None):
        """
        初始化身份钱包
        seed: 种子短语
        """
        self.seed = seed or self.generate_seed()
        self.dids = {}
        self.credentials = {}
        self.private_keys = {}
    
    def generate_seed(self) -> str:
        """生成种子短语"""
        import secrets
        words = []
        wordlist = self.get_bip39_wordlist()
        
        for _ in range(12):
            word = secrets.choice(wordlist)
            words.append(word)
        
        return " ".join(words)
    
    def create_did(self, method: str = "example") -> str:
        """创建DID"""
        # 生成密钥对
        private_key, public_key = self.generate_keypair()
        
        # 生成标识符
        identifier = self.generate_identifier()
        
        # 创建DID
        did = DID(method, identifier)
        did_document = did.create_did_document([
            {
                "id": f"{did.did}#key-1",
                "type": "Ed25519VerificationKey2018",
                "controller": did.did,
                "publicKeyJwk": self.public_key_to_jwk(public_key)
            }
        ])
        
        # 存储到钱包
        self.dids[did.did] = did_document
        self.private_keys[did.did] = private_key
        
        return did.did
    
    def generate_keypair(self) -> Tuple[str, str]:
        """生成密钥对"""
        import nacl.signing
        
        signing_key = nacl.signing.SigningKey.generate()
        verify_key = signing_key.verify_key
        
        private_key = base64.b64encode(signing_key.encode()).decode()
        public_key = base64.b64encode(verify_key.encode()).decode()
        
        return private_key, public_key
    
    def public_key_to_jwk(self, public_key: str) -> Dict:
        """转换公钥为JWK格式"""
        return {
            "kty": "OKP",
            "crv": "Ed25519",
            "x": public_key
        }
    
    def store_credential(self, did: str, credential: Dict):
        """存储凭证"""
        if did not in self.credentials:
            self.credentials[did] = []
        
        self.credentials[did].append(credential)
    
    def get_credentials(self, did: str) -> List[Dict]:
        """获取凭证"""
        return self.credentials.get(did, [])
    
    def create_presentation(self, did: str, credential_ids: List[str] = None) -> Dict:
        """创建凭证演示"""
        credentials = self.get_credentials(did)
        
        if credential_ids:
            selected_credentials = [cred for cred in credentials 
                                 if cred["id"] in credential_ids]
        else:
            selected_credentials = credentials
        
        presentation = CredentialPresentation()
        for credential in selected_credentials:
            presentation.add_credential(credential)
        
        return presentation.create_presentation(did)
    
    def sign_presentation(self, did: str, presentation: Dict) -> Dict:
        """签名演示"""
        private_key = self.private_keys.get(did)
        if not private_key:
            raise ValueError("Private key not found")
        
        presentation_signer = CredentialPresentation()
        return presentation_signer.sign_presentation(presentation, private_key)
    
    def generate_identifier(self) -> str:
        """生成标识符"""
        import secrets
        return secrets.token_urlsafe(16)
    
    def get_bip39_wordlist(self) -> List[str]:
        """获取BIP39词表"""
        # 简化的词表
        return [
            "abandon", "ability", "able", "about", "above", "absent", "absorb", "abstract",
            "absurd", "abuse", "access", "accident", "account", "accuse", "achieve", "acid",
            "acoustic", "acquire", "across", "act", "action", "actor", "actual", "adapt"
        ]
```

### 4.2 凭证管理

```python
class CredentialManager:
    def __init__(self, wallet: IdentityWallet):
        self.wallet = wallet
    
    def issue_credential(self, issuer_did: str, subject_did: str, 
                        claims: Dict, credential_type: List[str]) -> Dict:
        """发行凭证"""
        # 创建凭证
        credential = VerifiableCredential(issuer_did, subject_did, claims)
        credential_doc = credential.create_credential(credential_type)
        
        # 签名凭证
        private_key = self.wallet.private_keys.get(issuer_did)
        if not private_key:
            raise ValueError("Issuer private key not found")
        
        verifiable_credential = credential.sign_credential(private_key)
        
        return verifiable_credential
    
    def verify_credential(self, verifiable_credential: Dict) -> bool:
        """验证凭证"""
        credential = VerifiableCredential("", "", {})
        return credential.verify_credential(verifiable_credential)
    
    def revoke_credential(self, credential_id: str, issuer_did: str):
        """撤销凭证"""
        # 创建撤销列表
        revocation_list = {
            "issuer": issuer_did,
            "revokedCredentials": [credential_id],
            "timestamp": self.get_current_time()
        }
        
        # 签名撤销列表
        private_key = self.wallet.private_keys.get(issuer_did)
        if not private_key:
            raise ValueError("Issuer private key not found")
        
        signature = self.sign_data(json.dumps(revocation_list), private_key)
        revocation_list["signature"] = signature
        
        return revocation_list
    
    def check_revocation(self, credential_id: str, revocation_list: Dict) -> bool:
        """检查凭证是否被撤销"""
        revoked_credentials = revocation_list.get("revokedCredentials", [])
        return credential_id in revoked_credentials
    
    def sign_data(self, data: str, private_key: str) -> str:
        """签名数据"""
        import nacl.signing
        
        signing_key = nacl.signing.SigningKey(private_key.encode())
        signature = signing_key.sign(data.encode())
        
        return base64.b64encode(signature.signature).decode()
    
    def get_current_time(self) -> str:
        """获取当前时间"""
        from datetime import datetime
        return datetime.utcnow().isoformat() + "Z"
```

## 5. 应用场景

### 5.1 数字身份验证

```python
class DigitalIdentityVerification:
    def __init__(self):
        self.wallet = IdentityWallet()
        self.credential_manager = CredentialManager(self.wallet)
    
    def create_digital_identity(self) -> str:
        """创建数字身份"""
        return self.wallet.create_did()
    
    def issue_identity_credential(self, issuer_did: str, subject_did: str, 
                                identity_data: Dict) -> Dict:
        """发行身份凭证"""
        claims = {
            "name": identity_data.get("name"),
            "dateOfBirth": identity_data.get("dateOfBirth"),
            "nationality": identity_data.get("nationality"),
            "documentNumber": identity_data.get("documentNumber")
        }
        
        return self.credential_manager.issue_credential(
            issuer_did, subject_did, claims, ["IdentityCredential"]
        )
    
    def verify_identity(self, presentation: Dict) -> bool:
        """验证身份"""
        # 验证演示
        presentation_verifier = CredentialPresentation()
        if not presentation_verifier.verify_presentation(presentation):
            return False
        
        # 验证凭证
        credentials = presentation.get("verifiableCredential", [])
        for credential in credentials:
            if not self.credential_manager.verify_credential(credential):
                return False
        
        return True
```

### 5.2 访问控制

```python
class AccessControl:
    def __init__(self):
        self.wallet = IdentityWallet()
        self.credential_manager = CredentialManager(self.wallet)
    
    def issue_access_credential(self, issuer_did: str, subject_did: str, 
                              permissions: List[str], resource: str) -> Dict:
        """发行访问凭证"""
        claims = {
            "permissions": permissions,
            "resource": resource,
            "issuedAt": self.get_current_time()
        }
        
        return self.credential_manager.issue_credential(
            issuer_did, subject_did, claims, ["AccessCredential"]
        )
    
    def check_access(self, presentation: Dict, required_permissions: List[str], 
                    resource: str) -> bool:
        """检查访问权限"""
        # 验证演示
        presentation_verifier = CredentialPresentation()
        if not presentation_verifier.verify_presentation(presentation):
            return False
        
        # 检查凭证
        credentials = presentation.get("verifiableCredential", [])
        for credential in credentials:
            if not self.credential_manager.verify_credential(credential):
                continue
            
            # 检查资源匹配
            subject = credential.get("credentialSubject", {})
            if subject.get("resource") != resource:
                continue
            
            # 检查权限
            user_permissions = subject.get("permissions", [])
            if all(perm in user_permissions for perm in required_permissions):
                return True
        
        return False
    
    def get_current_time(self) -> str:
        """获取当前时间"""
        from datetime import datetime
        return datetime.utcnow().isoformat() + "Z"
```

### 5.3 隐私保护认证

```python
class PrivacyPreservingAuthentication:
    def __init__(self):
        self.wallet = IdentityWallet()
        self.credential_manager = CredentialManager(self.wallet)
    
    def create_age_proof(self, user_did: str, age: int, minimum_age: int) -> Dict:
        """创建年龄证明"""
        # 使用零知识证明证明年龄范围
        claims = {
            "ageRange": f"{minimum_age}+",
            "proofType": "ageRangeProof"
        }
        
        return self.credential_manager.issue_credential(
            user_did, user_did, claims, ["AgeProofCredential"]
        )
    
    def create_citizenship_proof(self, user_did: str, country: str) -> Dict:
        """创建公民身份证明"""
        claims = {
            "citizenship": country,
            "proofType": "citizenshipProof"
        }
        
        return self.credential_manager.issue_credential(
            user_did, user_did, claims, ["CitizenshipCredential"]
        )
    
    def verify_age_requirement(self, presentation: Dict, minimum_age: int) -> bool:
        """验证年龄要求"""
        # 验证演示
        presentation_verifier = CredentialPresentation()
        if not presentation_verifier.verify_presentation(presentation):
            return False
        
        # 检查年龄证明
        credentials = presentation.get("verifiableCredential", [])
        for credential in credentials:
            if not self.credential_manager.verify_credential(credential):
                continue
            
            subject = credential.get("credentialSubject", {})
            if subject.get("proofType") == "ageRangeProof":
                age_range = subject.get("ageRange", "")
                if age_range.endswith("+") and int(age_range[:-1]) >= minimum_age:
                    return True
        
        return False
```

## 6. 总结

去中心化身份为Web3提供了强大的身份管理能力：

1. **DID标准**：全球唯一的去中心化标识符
2. **可验证凭证**：数字化的可信凭证系统
3. **身份钱包**：用户控制和管理身份数据
4. **凭证管理**：发行、验证、撤销凭证
5. **应用场景**：数字身份验证、访问控制、隐私保护认证
6. **Web3集成**：与区块链和去中心化应用深度集成

去中心化身份将继续在Web3生态系统中发挥核心作用，为用户提供自主、安全、隐私的身份管理能力。
