
# Web3密码学基础理论

## 概述

本文档提供了Web3密码学的基础理论，涵盖从信息论基础到高级密码学协议，为Web3系统的安全性提供理论支撑。

## 1. 密码学理论基础

### 1.1 信息论基础

- **香农熵定义**: $H(X) = -\sum_{i} p(i) \log_2 p(i)$
- **条件熵**: $H(X|Y) = -\sum_{x,y} p(x,y) \log_2 p(x|y)$
- **互信息**: $I(X;Y) = H(X) - H(X|Y)$

### 1.2 计算复杂性理论

```latex
\begin{align}
P &= \{L | L \text{ 可在多项式时间内判定}\} \\
NP &= \{L | L \text{ 可在非确定多项式时间内判定}\} \\
BPP &= \{L | L \text{ 可在概率多项式时间内判定，错误率} \leq 1/3\}
\end{align}
```

### 1.3 数论基础

```python
class NumberTheory:
    """数论基础"""
    
    def __init__(self):
        self.prime_generators = {
            "miller_rabin": "Miller-Rabin素性测试",
            "aks": "AKS素性测试",
            "fermat": "费马小定理测试"
        }
    
    def is_prime(self, n: int) -> bool:
        """判断是否为素数"""
        if n < 2:
            return False
        if n == 2:
            return True
        if n % 2 == 0:
            return False
        
        # Miller-Rabin素性测试
        return self._miller_rabin_test(n)
    
    def _miller_rabin_test(self, n: int, k: int = 5) -> bool:
        """Miller-Rabin素性测试"""
        if n == 2 or n == 3:
            return True
        if n < 2 or n % 2 == 0:
            return False
        
        # 将n-1写成2^r * d的形式
        r, d = 0, n - 1
        while d % 2 == 0:
            r += 1
            d //= 2
        
        # 进行k次测试
        for _ in range(k):
            a = random.randint(2, n - 2)
            x = pow(a, d, n)
            if x == 1 or x == n - 1:
                continue
            for _ in range(r - 1):
                x = (x * x) % n
                if x == n - 1:
                    break
            else:
                return False
        return True
    
    def generate_prime(self, bits: int) -> int:
        """生成指定位数的素数"""
        while True:
            n = random.getrandbits(bits)
            n |= (1 << bits - 1) | 1  # 确保是奇数且位数正确
            if self.is_prime(n):
                return n
    
    def extended_gcd(self, a: int, b: int) -> tuple:
        """扩展欧几里得算法"""
        if a == 0:
            return b, 0, 1
        gcd, x1, y1 = self.extended_gcd(b % a, a)
        x = y1 - (b // a) * x1
        y = x1
        return gcd, x, y
    
    def mod_inverse(self, a: int, m: int) -> int:
        """模逆元"""
        gcd, x, _ = self.extended_gcd(a, m)
        if gcd != 1:
            raise ValueError("模逆元不存在")
        return (x % m + m) % m
```

## 2. 核心密码学原语

### 2.1 对称加密

```python
class SymmetricEncryption:
    """对称加密"""
    
    def __init__(self):
        self.algorithms = {
            "aes": "AES加密",
            "des": "DES加密",
            "chacha20": "ChaCha20加密"
        }
    
    def aes_encrypt(self, plaintext: bytes, key: bytes, mode: str = "CBC") -> dict:
        """AES加密"""
        from Crypto.Cipher import AES
        from Crypto.Util.Padding import pad
        import os
        
        # 生成随机IV
        iv = os.urandom(16)
        
        if mode == "CBC":
            cipher = AES.new(key, AES.MODE_CBC, iv)
        elif mode == "GCM":
            cipher = AES.new(key, AES.MODE_GCM, iv)
        else:
            raise ValueError("不支持的加密模式")
        
        # 填充明文
        padded_plaintext = pad(plaintext, AES.block_size)
        
        # 加密
        ciphertext = cipher.encrypt(padded_plaintext)
        
        return {
            "ciphertext": ciphertext,
            "iv": iv,
            "mode": mode,
            "algorithm": "AES"
        }
    
    def aes_decrypt(self, ciphertext: bytes, key: bytes, iv: bytes, mode: str = "CBC") -> bytes:
        """AES解密"""
        from Crypto.Cipher import AES
        from Crypto.Util.Padding import unpad
        
        if mode == "CBC":
            cipher = AES.new(key, AES.MODE_CBC, iv)
        elif mode == "GCM":
            cipher = AES.new(key, AES.MODE_GCM, iv)
        else:
            raise ValueError("不支持的加密模式")
        
        # 解密
        padded_plaintext = cipher.decrypt(ciphertext)
        
        # 去除填充
        plaintext = unpad(padded_plaintext, AES.block_size)
        
        return plaintext
```

### 2.2 非对称加密

```python
class AsymmetricEncryption:
    """非对称加密"""
    
    def __init__(self):
        self.algorithms = {
            "rsa": "RSA加密",
            "ecc": "椭圆曲线加密",
            "elgamal": "ElGamal加密"
        }
    
    def rsa_key_generation(self, key_size: int = 2048) -> dict:
        """RSA密钥生成"""
        from Crypto.PublicKey import RSA
        
        # 生成RSA密钥对
        key = RSA.generate(key_size)
        
        return {
            "private_key": key.export_key(),
            "public_key": key.publickey().export_key(),
            "key_size": key_size
        }
    
    def rsa_encrypt(self, plaintext: bytes, public_key: bytes) -> bytes:
        """RSA加密"""
        from Crypto.PublicKey import RSA
        from Crypto.Cipher import PKCS1_OAEP
        
        # 导入公钥
        key = RSA.import_key(public_key)
        
        # 创建加密器
        cipher = PKCS1_OAEP.new(key)
        
        # 加密
        ciphertext = cipher.encrypt(plaintext)
        
        return ciphertext
    
    def rsa_decrypt(self, ciphertext: bytes, private_key: bytes) -> bytes:
        """RSA解密"""
        from Crypto.PublicKey import RSA
        from Crypto.Cipher import PKCS1_OAEP
        
        # 导入私钥
        key = RSA.import_key(private_key)
        
        # 创建解密器
        cipher = PKCS1_OAEP.new(key)
        
        # 解密
        plaintext = cipher.decrypt(ciphertext)
        
        return plaintext
    
    def ecc_key_generation(self, curve: str = "secp256k1") -> dict:
        """椭圆曲线密钥生成"""
        from cryptography.hazmat.primitives.asymmetric import ec
        from cryptography.hazmat.primitives import serialization
        
        # 生成私钥
        private_key = ec.generate_private_key(
            ec.SECP256K1()
        )
        
        # 获取公钥
        public_key = private_key.public_key()
        
        return {
            "private_key": private_key.private_bytes(
                encoding=serialization.Encoding.PEM,
                format=serialization.PrivateFormat.PKCS8,
                encryption_algorithm=serialization.NoEncryption()
            ),
            "public_key": public_key.public_bytes(
                encoding=serialization.Encoding.PEM,
                format=serialization.PublicFormat.SubjectPublicKeyInfo
            ),
            "curve": curve
        }
```

### 2.3 哈希函数

```python
class HashFunctions:
    """哈希函数"""
    
    def __init__(self):
        self.hash_algorithms = {
            "sha256": "SHA-256",
            "sha512": "SHA-512",
            "keccak": "Keccak-256",
            "blake2b": "BLAKE2b"
        }
    
    def sha256_hash(self, data: bytes) -> bytes:
        """SHA-256哈希"""
        import hashlib
        
        return hashlib.sha256(data).digest()
    
    def keccak256_hash(self, data: bytes) -> bytes:
        """Keccak-256哈希（以太坊使用）"""
        from eth_hash.auto import keccak
        
        return keccak(data)
    
    def merkle_tree(self, data_list: list) -> dict:
        """构建默克尔树"""
        import hashlib
        
        def hash_pair(a: bytes, b: bytes) -> bytes:
            return hashlib.sha256(a + b).digest()
        
        # 将数据转换为字节
        leaves = [hashlib.sha256(data.encode()).digest() for data in data_list]
        
        # 如果叶子节点数为奇数，复制最后一个
        if len(leaves) % 2 == 1:
            leaves.append(leaves[-1])
        
        # 构建树
        tree = [leaves]
        current_level = leaves
        
        while len(current_level) > 1:
            next_level = []
            for i in range(0, len(current_level), 2):
                if i + 1 < len(current_level):
                    next_level.append(hash_pair(current_level[i], current_level[i + 1]))
                else:
                    next_level.append(current_level[i])
            
            # 如果节点数为奇数，复制最后一个
            if len(next_level) % 2 == 1 and len(next_level) > 1:
                next_level.append(next_level[-1])
            
            tree.append(next_level)
            current_level = next_level
        
        return {
            "tree": tree,
            "root": current_level[0] if current_level else None,
            "height": len(tree) - 1
        }
    
    def generate_merkle_proof(self, tree: dict, leaf_index: int) -> list:
        """生成默克尔证明"""
        proof = []
        current_index = leaf_index
        
        for level in tree["tree"][:-1]:  # 除了根节点
            if current_index % 2 == 0:
                # 左节点，需要右兄弟
                if current_index + 1 < len(level):
                    proof.append(("right", level[current_index + 1]))
            else:
                # 右节点，需要左兄弟
                proof.append(("left", level[current_index - 1]))
            
            current_index //= 2
        
        return proof
    
    def verify_merkle_proof(self, leaf: bytes, proof: list, root: bytes) -> bool:
        """验证默克尔证明"""
        import hashlib
        
        def hash_pair(a: bytes, b: bytes) -> bytes:
            return hashlib.sha256(a + b).digest()
        
        current_hash = leaf
        
        for direction, sibling in proof:
            if direction == "left":
                current_hash = hash_pair(sibling, current_hash)
            else:
                current_hash = hash_pair(current_hash, sibling)
        
        return current_hash == root
```

### 2.4 数字签名

```python
class DigitalSignatures:
    """数字签名"""
    
    def __init__(self):
        self.signature_algorithms = {
            "ecdsa": "椭圆曲线数字签名算法",
            "rsa_pss": "RSA-PSS签名",
            "ed25519": "Ed25519签名"
        }
    
    def ecdsa_sign(self, message: bytes, private_key: bytes) -> dict:
        """ECDSA签名"""
        from cryptography.hazmat.primitives.asymmetric import ec
        from cryptography.hazmat.primitives import hashes
        from cryptography.hazmat.primitives import serialization
        
        # 导入私钥
        key = serialization.load_pem_private_key(
            private_key,
            password=None
        )
        
        # 签名
        signature = key.sign(
            message,
            ec.ECDSA(hashes.SHA256())
        )
        
        return {
            "signature": signature,
            "algorithm": "ECDSA",
            "hash_algorithm": "SHA256"
        }
    
    def ecdsa_verify(self, message: bytes, signature: bytes, public_key: bytes) -> bool:
        """ECDSA验证"""
        from cryptography.hazmat.primitives.asymmetric import ec
        from cryptography.hazmat.primitives import hashes
        from cryptography.hazmat.primitives import serialization
        
        try:
            # 导入公钥
            key = serialization.load_pem_public_key(public_key)
            
            # 验证签名
            key.verify(
                signature,
                message,
                ec.ECDSA(hashes.SHA256())
            )
            return True
        except:
            return False
    
    def schnorr_sign(self, message: bytes, private_key: int, public_key: int) -> dict:
        """Schnorr签名（简化版）"""
        import hashlib
        import random
        
        # 生成随机数k
        k = random.randint(1, 2**256 - 1)
        
        # 计算R = k * G
        R = k * 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798  # 简化的基点
        
        # 计算e = H(R || P || m)
        e = int.from_bytes(
            hashlib.sha256(
                R.to_bytes(32, 'big') + 
                public_key.to_bytes(32, 'big') + 
                message
            ).digest(),
            'big'
        )
        
        # 计算s = k + e * private_key
        s = (k + e * private_key) % (2**256)
        
        return {
            "R": R,
            "s": s,
            "algorithm": "Schnorr"
        }
```

## 3. 高级密码学协议

### 3.1 零知识证明

```python
class ZeroKnowledgeProofs:
    """零知识证明"""
    
    def __init__(self):
        self.zk_protocols = {
            "schnorr": "Schnorr协议",
            "fiat_shamir": "Fiat-Shamir协议",
            "zk_snark": "zk-SNARK"
        }
    
    def schnorr_protocol(self, secret: int, public_key: int) -> dict:
        """Schnorr零知识证明协议"""
        import random
        import hashlib
        
        # 承诺阶段
        r = random.randint(1, 2**256 - 1)
        R = r * 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
        
        # 挑战阶段（模拟）
        challenge = random.randint(1, 2**256 - 1)
        
        # 响应阶段
        response = (r + challenge * secret) % (2**256)
        
        return {
            "commitment": R,
            "challenge": challenge,
            "response": response,
            "public_key": public_key
        }
    
    def verify_schnorr_proof(self, proof: dict) -> bool:
        """验证Schnorr零知识证明"""
        # 验证: R + challenge * public_key = response * G
        left_side = proof["commitment"] + proof["challenge"] * proof["public_key"]
        right_side = proof["response"] * 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
        
        return left_side == right_side
```

### 3.2 多方安全计算

```python
class MultiPartyComputation:
    """多方安全计算"""
    
    def __init__(self):
        self.mpc_protocols = {
            "yao": "姚氏电路",
            "garbled_circuit": "混淆电路",
            "secret_sharing": "秘密共享"
        }
    
    def shamir_secret_sharing(self, secret: int, n: int, t: int) -> list:
        """Shamir秘密共享"""
        import random
        
        # 生成随机系数
        coefficients = [secret] + [random.randint(1, 2**256 - 1) for _ in range(t - 1)]
        
        # 计算份额
        shares = []
        for i in range(1, n + 1):
            share = 0
            for j, coeff in enumerate(coefficients):
                share += coeff * (i ** j)
            shares.append((i, share))
        
        return shares
    
    def reconstruct_secret(self, shares: list, t: int) -> int:
        """重构秘密"""
        from scipy.interpolate import lagrange
        
        # 使用拉格朗日插值重构
        x = [share[0] for share in shares[:t]]
        y = [share[1] for share in shares[:t]]
        
        poly = lagrange(x, y)
        return int(poly(0))
```

### 3.3 同态加密

```python
class HomomorphicEncryption:
    """同态加密"""
    
    def __init__(self):
        self.he_schemes = {
            "paillier": "Paillier加密",
            "bfv": "BFV方案",
            "ckks": "CKKS方案"
        }
    
    def paillier_encrypt(self, message: int, public_key: tuple) -> int:
        """Paillier加密"""
        import random
        
        n, g = public_key
        r = random.randint(1, n - 1)
        
        # 加密: c = g^m * r^n mod n^2
        c = (pow(g, message, n * n) * pow(r, n, n * n)) % (n * n)
        
        return c
    
    def paillier_decrypt(self, ciphertext: int, private_key: tuple) -> int:
        """Paillier解密"""
        n, lambda_val, mu = private_key
        
        # 解密: m = L(c^lambda mod n^2) * mu mod n
        # 其中 L(x) = (x - 1) / n
        x = pow(ciphertext, lambda_val, n * n)
        L = (x - 1) // n
        message = (L * mu) % n
        
        return message
    
    def paillier_add(self, c1: int, c2: int, public_key: tuple) -> int:
        """Paillier同态加法"""
        n, _ = public_key
        return (c1 * c2) % (n * n)
```

## 4. Web3密码学应用

### 4.1 区块链密码学

```python
class BlockchainCryptography:
    """区块链密码学"""
    
    def __init__(self):
        self.blockchain_crypto = {
            "consensus": "共识机制密码学",
            "privacy": "隐私保护",
            "scalability": "可扩展性密码学"
        }
    
    def proof_of_work(self, block_header: bytes, target: int) -> dict:
        """工作量证明"""
        import hashlib
        import time
        
        nonce = 0
        start_time = time.time()
        
        while True:
            # 构造区块头
            header = block_header + nonce.to_bytes(8, 'big')
            
            # 计算哈希
            hash_result = hashlib.sha256(header).digest()
            hash_int = int.from_bytes(hash_result, 'big')
            
            # 检查是否满足目标
            if hash_int < target:
                return {
                    "nonce": nonce,
                    "hash": hash_result.hex(),
                    "time_taken": time.time() - start_time
                }
            
            nonce += 1
    
    def proof_of_stake(self, stake_amount: int, total_stake: int) -> float:
        """权益证明概率计算"""
        # 简化的PoS概率计算
        return stake_amount / total_stake
```

### 4.2 智能合约安全

```python
class SmartContractSecurity:
    """智能合约安全"""
    
    def __init__(self):
        self.security_measures = {
            "access_control": "访问控制",
            "reentrancy_protection": "重入攻击防护",
            "overflow_protection": "溢出防护"
        }
    
    def check_reentrancy_vulnerability(self, contract_code: str) -> dict:
        """检查重入攻击漏洞"""
        vulnerabilities = []
        
        # 检查外部调用
        if "call(" in contract_code or "send(" in contract_code or "transfer(" in contract_code:
            # 检查是否在状态更新之前进行外部调用
            if not self._has_state_update_before_external_call(contract_code):
                vulnerabilities.append("重入攻击漏洞")
        
        return {
            "vulnerabilities": vulnerabilities,
            "risk_level": "high" if vulnerabilities else "low"
        }
    
    def _has_state_update_before_external_call(self, code: str) -> bool:
        """检查是否在外部调用前更新状态"""
        # 简化的检查逻辑
        return "state_update" in code.lower()
```

## 5. 安全分析与证明

### 5.1 可证明安全性

```python
class ProvableSecurity:
    """可证明安全性"""
    
    def __init__(self):
        self.security_models = {
            "ind_cpa": "选择明文攻击下的不可区分性",
            "ind_cca": "选择密文攻击下的不可区分性",
            "euf_cma": "存在性不可伪造性"
        }
    
    def security_reduction(self, adversary_advantage: float, reduction_factor: float) -> float:
        """安全归约"""
        return adversary_advantage / reduction_factor
```

## 6. 实现与标准

### 6.1 算法实现

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract CryptographicPrimitives {
    // 哈希函数
    function sha256Hash(bytes memory data) public pure returns (bytes32) {
        return sha256(data);
    }
    
    // 椭圆曲线签名验证
    function ecrecover(bytes32 hash, uint8 v, bytes32 r, bytes32 s) 
        public pure returns (address) {
        return ecrecover(hash, v, r, s);
    }
    
    // 默克尔树验证
    function verifyMerkleProof(
        bytes32 leaf,
        bytes32 root,
        bytes32[] memory proof
    ) public pure returns (bool) {
        bytes32 computedHash = leaf;
        
        for (uint256 i = 0; i < proof.length; i++) {
            bytes32 proofElement = proof[i];
            
            if (computedHash <= proofElement) {
                computedHash = keccak256(abi.encodePacked(computedHash, proofElement));
            } else {
                computedHash = keccak256(abi.encodePacked(proofElement, computedHash));
            }
        }
        
        return computedHash == root;
    }
}
```

## 7. 后量子密码学

### 7.1 格密码学

```python
class LatticeCryptography:
    """格密码学"""
    
    def __init__(self):
        self.lattice_schemes = {
            "lwe": "学习带误差问题",
            "rlwe": "环学习带误差问题",
            "nist_pqc": "NIST后量子密码学标准"
        }
    
    def lwe_encrypt(self, message: int, public_key: list, error: int) -> tuple:
        """LWE加密"""
        # 简化的LWE加密
        # 实际实现需要更复杂的格运算
        ciphertext = sum(public_key) + message + error
        return (ciphertext, public_key)
```

## 8. 参考文献

1. **基础理论**
   - Shannon, C. E. (1949). Communication theory of secrecy systems
   - Diffie, W., & Hellman, M. (1976). New directions in cryptography
   - Rivest, R. L., Shamir, A., & Adleman, L. (1978). A method for obtaining digital signatures and public-key cryptosystems

2. **Web3应用**
   - Nakamoto, S. (2008). Bitcoin: A peer-to-peer electronic cash system
   - Buterin, V. (2014). Ethereum: A next-generation smart contract and decentralized application platform
   - Wood, G. (2014). Ethereum: A secure decentralised generalised transaction ledger

3. **后量子密码学**
   - Chen, L., et al. (2016). Report on post-quantum cryptography
   - Alkim, E., et al. (2016). NewHope: A key encapsulation mechanism
   - Ducas, L., et al. (2018). CRYSTALS-Dilithium: A lattice-based digital signature scheme

本文档为Web3密码学提供了全面的理论基础，从基础原语到高级协议，为Web3系统的安全性提供了坚实的密码学支撑。
