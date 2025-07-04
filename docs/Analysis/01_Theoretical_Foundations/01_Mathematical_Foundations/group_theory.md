# 群论基础理论分析

## 1. 群论基本概念

### 1.1 基本定义

**定义 1.1 (群)** 一个集合G连同其上的二元运算·，满足以下四个公理：
1. 封闭性：∀a,b∈G，a·b∈G
2. 结合律：∀a,b,c∈G，(a·b)·c = a·(b·c)
3. 单位元：存在e∈G，使得∀a∈G，e·a = a·e = a
4. 逆元：∀a∈G，存在a⁻¹∈G，使得a·a⁻¹ = a⁻¹·a = e

**定义 1.2 (子群)** 群G的子集H是G的子群，如果H在G的运算下也构成群。

**定义 1.3 (同态)** 群G到群H的映射φ是群同态，如果∀a,b∈G，φ(a·b) = φ(a)·φ(b)。

### 1.2 群的基本性质

**定义 1.4 (阶)** 群G的阶是G中元素的个数，记作|G|。

**定义 1.5 (元素的阶)** 元素a的阶是使得aⁿ = e的最小正整数n。

**定义 1.6 (循环群)** 由单个元素生成的群称为循环群。

## 2. 群论实现

### 2.1 基本群操作

```python
import numpy as np
from typing import List, Dict, Optional, Tuple
from dataclasses import dataclass

@dataclass
class GroupElement:
    value: int
    order: int
    
    def __str__(self):
        return f"g^{self.value}"

class FiniteGroup:
    def __init__(self, order: int, operation: str = "multiplication"):
        self.order = order
        self.operation = operation
        self.elements = []
        self.identity = None
        self.cayley_table = {}
        
        self._initialize_group()
    
    def _initialize_group(self):
        """初始化群"""
        # 创建群元素
        for i in range(self.order):
            element = GroupElement(i, 0)
            self.elements.append(element)
        
        # 设置单位元
        self.identity = self.elements[0]
        
        # 生成Cayley表
        self._generate_cayley_table()
        
        # 计算元素阶
        self._compute_element_orders()
    
    def _generate_cayley_table(self):
        """生成Cayley表"""
        for i in range(self.order):
            for j in range(self.order):
                if self.operation == "multiplication":
                    result = (i * j) % self.order
                elif self.operation == "addition":
                    result = (i + j) % self.order
                else:
                    result = (i + j) % self.order
                
                self.cayley_table[(i, j)] = result
    
    def _compute_element_orders(self):
        """计算元素阶"""
        for element in self.elements:
            if element.value == 0:  # 单位元
                element.order = 1
            else:
                # 计算元素阶
                power = element.value
                order = 1
                while power != 0:
                    power = self.cayley_table[(power, element.value)]
                    order += 1
                    if order > self.order:
                        break
                element.order = order
    
    def multiply(self, a: int, b: int) -> int:
        """群乘法"""
        return self.cayley_table.get((a, b), 0)
    
    def inverse(self, a: int) -> int:
        """求逆元"""
        for i in range(self.order):
            if self.multiply(a, i) == 0:  # 0是单位元
                return i
        return None
    
    def power(self, a: int, n: int) -> int:
        """计算幂"""
        if n == 0:
            return 0  # 单位元
        elif n < 0:
            a = self.inverse(a)
            n = -n
        
        result = a
        for _ in range(n - 1):
            result = self.multiply(result, a)
        
        return result
    
    def is_subgroup(self, elements: List[int]) -> bool:
        """检查是否为子群"""
        # 检查封闭性
        for a in elements:
            for b in elements:
                product = self.multiply(a, b)
                if product not in elements:
                    return False
        
        # 检查单位元
        if 0 not in elements:
            return False
        
        # 检查逆元
        for a in elements:
            if a != 0:  # 单位元的逆元是自身
                inverse = self.inverse(a)
                if inverse not in elements:
                    return False
        
        return True
    
    def generate_subgroup(self, generator: int) -> List[int]:
        """生成子群"""
        subgroup = [0]  # 包含单位元
        current = generator
        
        while current != 0:
            if current not in subgroup:
                subgroup.append(current)
            current = self.multiply(current, generator)
        
        return subgroup
    
    def find_all_subgroups(self) -> List[List[int]]:
        """找到所有子群"""
        subgroups = [[0]]  # 平凡子群
        
        for element in self.elements:
            if element.value != 0:
                subgroup = self.generate_subgroup(element.value)
                if subgroup not in subgroups:
                    subgroups.append(subgroup)
        
        return subgroups
    
    def is_cyclic(self) -> bool:
        """检查是否为循环群"""
        # 检查是否存在生成元
        for element in self.elements:
            if element.value != 0:
                subgroup = self.generate_subgroup(element.value)
                if len(subgroup) == self.order:
                    return True
        return False
    
    def find_generators(self) -> List[int]:
        """找到所有生成元"""
        generators = []
        
        for element in self.elements:
            if element.value != 0:
                subgroup = self.generate_subgroup(element.value)
                if len(subgroup) == self.order:
                    generators.append(element.value)
        
        return generators
    
    def lagrange_theorem(self, subgroup_elements: List[int]) -> bool:
        """验证拉格朗日定理"""
        subgroup_order = len(subgroup_elements)
        return self.order % subgroup_order == 0
    
    def cosets(self, subgroup_elements: List[int]) -> List[List[int]]:
        """计算陪集"""
        cosets = []
        used_elements = set()
        
        for element in self.elements:
            if element.value not in used_elements:
                # 计算左陪集
                coset = []
                for h in subgroup_elements:
                    product = self.multiply(element.value, h)
                    coset.append(product)
                    used_elements.add(product)
                cosets.append(coset)
        
        return cosets
```

### 2.2 对称群

```python
class SymmetricGroup:
    def __init__(self, n: int):
        self.n = n
        self.order = self._factorial(n)
        self.elements = []
        self._generate_permutations()
    
    def _factorial(self, n: int) -> int:
        """计算阶乘"""
        if n <= 1:
            return 1
        return n * self._factorial(n - 1)
    
    def _generate_permutations(self):
        """生成所有置换"""
        # 生成所有n!个置换
        numbers = list(range(1, self.n + 1))
        self.elements = self._all_permutations(numbers)
    
    def _all_permutations(self, numbers: List[int]) -> List[List[int]]:
        """生成所有置换"""
        if len(numbers) <= 1:
            return [numbers]
        
        permutations = []
        for i in range(len(numbers)):
            current = numbers[i]
            remaining = numbers[:i] + numbers[i+1:]
            
            for perm in self._all_permutations(remaining):
                permutations.append([current] + perm)
        
        return permutations
    
    def multiply_permutations(self, perm1: List[int], perm2: List[int]) -> List[int]:
        """置换乘法"""
        result = [0] * self.n
        
        for i in range(self.n):
            # perm1(perm2(i))
            result[i] = perm1[perm2[i] - 1]
        
        return result
    
    def inverse_permutation(self, perm: List[int]) -> List[int]:
        """求置换的逆"""
        inverse = [0] * self.n
        
        for i in range(self.n):
            inverse[perm[i] - 1] = i + 1
        
        return inverse
    
    def cycle_decomposition(self, perm: List[int]) -> List[List[int]]:
        """循环分解"""
        cycles = []
        visited = [False] * self.n
        
        for i in range(self.n):
            if not visited[i]:
                cycle = []
                current = i + 1
                
                while not visited[current - 1]:
                    visited[current - 1] = True
                    cycle.append(current)
                    current = perm[current - 1]
                
                if len(cycle) > 1:
                    cycles.append(cycle)
        
        return cycles
    
    def cycle_type(self, perm: List[int]) -> List[int]:
        """循环类型"""
        cycles = self.cycle_decomposition(perm)
        cycle_lengths = [len(cycle) for cycle in cycles]
        cycle_lengths.sort(reverse=True)
        return cycle_lengths
    
    def is_even_permutation(self, perm: List[int]) -> bool:
        """检查是否为偶置换"""
        cycles = self.cycle_decomposition(perm)
        inversions = 0
        
        for cycle in cycles:
            inversions += len(cycle) - 1
        
        return inversions % 2 == 0
    
    def alternating_group(self) -> List[List[int]]:
        """生成交错群"""
        alternating = []
        
        for perm in self.elements:
            if self.is_even_permutation(perm):
                alternating.append(perm)
        
        return alternating
    
    def conjugacy_classes(self) -> List[List[List[int]]]:
        """计算共轭类"""
        classes = []
        used = [False] * len(self.elements)
        
        for i, perm in enumerate(self.elements):
            if not used[i]:
                # 找到共轭类
                conjugacy_class = []
                
                for j, other_perm in enumerate(self.elements):
                    if not used[j]:
                        # 检查是否共轭
                        if self._are_conjugate(perm, other_perm):
                            conjugacy_class.append(other_perm)
                            used[j] = True
                
                classes.append(conjugacy_class)
        
        return classes
    
    def _are_conjugate(self, perm1: List[int], perm2: List[int]) -> bool:
        """检查两个置换是否共轭"""
        # 两个置换共轭当且仅当它们有相同的循环类型
        return self.cycle_type(perm1) == self.cycle_type(perm2)
```

### 2.3 有限域上的群

```python
class FiniteFieldGroup:
    def __init__(self, p: int, n: int = 1):
        self.p = p  # 素数
        self.n = n  # 扩展次数
        self.q = p ** n  # 域的大小
        self.elements = []
        self._initialize_field()
    
    def _initialize_field(self):
        """初始化有限域"""
        # 生成域元素
        for i in range(self.q):
            self.elements.append(i)
    
    def add(self, a: int, b: int) -> int:
        """域加法"""
        return (a + b) % self.q
    
    def multiply(self, a: int, b: int) -> int:
        """域乘法"""
        return (a * b) % self.q
    
    def inverse(self, a: int) -> int:
        """乘法逆元"""
        if a == 0:
            return None
        
        # 使用扩展欧几里得算法
        def extended_gcd(a: int, b: int) -> Tuple[int, int, int]:
            if a == 0:
                return b, 0, 1
            else:
                gcd, x, y = extended_gcd(b % a, a)
                return gcd, y - (b // a) * x, x
        
        gcd, x, y = extended_gcd(a, self.q)
        if gcd != 1:
            return None
        
        return x % self.q
    
    def power(self, a: int, n: int) -> int:
        """快速幂"""
        if n == 0:
            return 1
        elif n < 0:
            a = self.inverse(a)
            n = -n
        
        result = 1
        while n > 0:
            if n % 2 == 1:
                result = self.multiply(result, a)
            a = self.multiply(a, a)
            n //= 2
        
        return result
    
    def multiplicative_group(self) -> List[int]:
        """乘法群"""
        group = []
        for element in self.elements:
            if element != 0:
                group.append(element)
        return group
    
    def primitive_root(self) -> Optional[int]:
        """寻找本原根"""
        if self.q == 2:
            return 1
        
        # 找到q-1的素因子
        factors = self._prime_factors(self.q - 1)
        
        # 寻找本原根
        for g in range(2, self.q):
            is_primitive = True
            
            for factor in factors:
                if self.power(g, (self.q - 1) // factor) == 1:
                    is_primitive = False
                    break
            
            if is_primitive:
                return g
        
        return None
    
    def _prime_factors(self, n: int) -> List[int]:
        """素因子分解"""
        factors = []
        d = 2
        
        while d * d <= n:
            while n % d == 0:
                if d not in factors:
                    factors.append(d)
                n //= d
            d += 1
        
        if n > 1 and n not in factors:
            factors.append(n)
        
        return factors
    
    def discrete_logarithm(self, base: int, value: int) -> Optional[int]:
        """离散对数"""
        if value == 1:
            return 0
        
        # Baby-step Giant-step算法
        m = int(np.sqrt(self.q - 1)) + 1
        
        # Baby steps
        baby_steps = {}
        current = 1
        for j in range(m):
            baby_steps[current] = j
            current = self.multiply(current, base)
        
        # Giant steps
        factor = self.power(base, m)
        current = value
        
        for i in range(m):
            if current in baby_steps:
                return i * m + baby_steps[current]
            current = self.multiply(current, factor)
        
        return None
    
    def quadratic_residues(self) -> List[int]:
        """二次剩余"""
        residues = []
        
        for a in range(1, self.q):
            # 检查a是否为二次剩余
            legendre = self.power(a, (self.q - 1) // 2)
            if legendre == 1:
                residues.append(a)
        
        return residues
    
    def legendre_symbol(self, a: int) -> int:
        """勒让德符号"""
        if a == 0:
            return 0
        
        return self.power(a, (self.q - 1) // 2)
```

## 3. 群论在密码学中的应用

### 3.1 离散对数问题

```python
class DiscreteLogarithmCrypto:
    def __init__(self, p: int, g: int):
        self.p = p  # 素数
        self.g = g  # 生成元
        self.group = FiniteFieldGroup(p)
    
    def generate_key_pair(self) -> Tuple[int, int]:
        """生成密钥对"""
        # 私钥
        private_key = np.random.randint(2, self.p - 1)
        
        # 公钥
        public_key = self.group.power(self.g, private_key)
        
        return private_key, public_key
    
    def encrypt(self, message: int, public_key: int, ephemeral_key: int) -> Tuple[int, int]:
        """加密"""
        # 计算共享密钥
        shared_secret = self.group.power(public_key, ephemeral_key)
        
        # 计算密文
        c1 = self.group.power(self.g, ephemeral_key)
        c2 = (message * shared_secret) % self.p
        
        return c1, c2
    
    def decrypt(self, ciphertext: Tuple[int, int], private_key: int) -> int:
        """解密"""
        c1, c2 = ciphertext
        
        # 计算共享密钥
        shared_secret = self.group.power(c1, private_key)
        
        # 计算逆元
        shared_secret_inv = self.group.inverse(shared_secret)
        
        # 解密
        message = (c2 * shared_secret_inv) % self.p
        
        return message
    
    def sign(self, message: int, private_key: int, k: int) -> Tuple[int, int]:
        """签名"""
        # 计算r
        r = self.group.power(self.g, k)
        
        # 计算s
        k_inv = self.group.inverse(k)
        s = (k_inv * (message + private_key * r)) % (self.p - 1)
        
        return r, s
    
    def verify(self, message: int, signature: Tuple[int, int], public_key: int) -> bool:
        """验证签名"""
        r, s = signature
        
        # 计算v1
        v1 = self.group.power(self.g, message)
        
        # 计算v2
        v2 = (self.group.power(public_key, r) * self.group.power(r, s)) % self.p
        
        return v1 == v2
```

### 3.2 椭圆曲线群

```python
class EllipticCurveGroup:
    def __init__(self, a: int, b: int, p: int):
        self.a = a
        self.b = b
        self.p = p
        self.points = []
        self._generate_points()
    
    def _generate_points(self):
        """生成椭圆曲线上的点"""
        # 添加无穷远点
        self.points.append((None, None))
        
        # 生成有限点
        for x in range(self.p):
            for y in range(self.p):
                # 检查点是否在曲线上
                left = (y * y) % self.p
                right = (x * x * x + self.a * x + self.b) % self.p
                
                if left == right:
                    self.points.append((x, y))
    
    def add_points(self, P: Tuple[int, int], Q: Tuple[int, int]) -> Tuple[int, int]:
        """点加法"""
        if P == (None, None):
            return Q
        if Q == (None, None):
            return P
        
        x1, y1 = P
        x2, y2 = Q
        
        if x1 == x2 and y1 != y2:
            return (None, None)  # 无穷远点
        
        if x1 == x2:
            # P = Q，计算切线斜率
            lambda_val = ((3 * x1 * x1 + self.a) * self._mod_inverse(2 * y1)) % self.p
        else:
            # P ≠ Q，计算连线斜率
            lambda_val = ((y2 - y1) * self._mod_inverse(x2 - x1)) % self.p
        
        # 计算新点
        x3 = (lambda_val * lambda_val - x1 - x2) % self.p
        y3 = (lambda_val * (x1 - x3) - y1) % self.p
        
        return (x3, y3)
    
    def _mod_inverse(self, a: int) -> int:
        """模逆"""
        def extended_gcd(a: int, b: int) -> Tuple[int, int, int]:
            if a == 0:
                return b, 0, 1
            else:
                gcd, x, y = extended_gcd(b % a, a)
                return gcd, y - (b // a) * x, x
        
        gcd, x, y = extended_gcd(a, self.p)
        if gcd != 1:
            return None
        
        return x % self.p
    
    def scalar_multiply(self, k: int, P: Tuple[int, int]) -> Tuple[int, int]:
        """标量乘法"""
        if k == 0:
            return (None, None)
        
        result = (None, None)
        current = P
        
        while k > 0:
            if k % 2 == 1:
                result = self.add_points(result, current)
            current = self.add_points(current, current)
            k //= 2
        
        return result
    
    def find_order(self, P: Tuple[int, int]) -> int:
        """计算点的阶"""
        if P == (None, None):
            return 1
        
        current = P
        order = 1
        
        while current != (None, None):
            current = self.add_points(current, P)
            order += 1
            
            if order > len(self.points):
                break
        
        return order
    
    def discrete_logarithm(self, P: Tuple[int, int], Q: Tuple[int, int]) -> Optional[int]:
        """椭圆曲线离散对数"""
        # Baby-step Giant-step算法
        m = int(np.sqrt(len(self.points))) + 1
        
        # Baby steps
        baby_steps = {}
        current = (None, None)
        for j in range(m):
            baby_steps[current] = j
            current = self.add_points(current, P)
        
        # Giant steps
        factor = self.scalar_multiply(m, P)
        current = Q
        
        for i in range(m):
            if current in baby_steps:
                return i * m + baby_steps[current]
            current = self.add_points(current, factor)
        
        return None
```

## 4. 总结

群论为密码学提供了坚实的数学基础：

1. **基本概念**：群、子群、同态、循环群等
2. **对称群**：置换群、循环分解、共轭类等
3. **有限域群**：乘法群、本原根、离散对数等
4. **密码学应用**：离散对数问题、椭圆曲线密码学等
5. **Web3应用**：数字签名、密钥交换、零知识证明等

群论将继续在Web3生态系统中发挥核心作用，为密码学协议提供数学保证。 