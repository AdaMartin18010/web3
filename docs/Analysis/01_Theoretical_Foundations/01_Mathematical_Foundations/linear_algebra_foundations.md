# 线性代数基础理论

## 1. 概述

线性代数是现代数学和计算机科学的基础，在密码学、机器学习、区块链技术中发挥着重要作用。本文档深入探讨线性代数的核心概念及其在Web3技术中的应用。

## 2. 向量空间理论

### 2.1 向量空间的定义

**定义 2.1 (向量空间)** 设 $F$ 是一个域，$V$ 是一个非空集合，配备加法运算 $+$ 和标量乘法运算 $\cdot$，如果满足以下公理，则称 $V$ 是 $F$ 上的向量空间：

1. **加法交换律**: $\forall u, v \in V, u + v = v + u$
2. **加法结合律**: $\forall u, v, w \in V, (u + v) + w = u + (v + w)$
3. **加法单位元**: $\exists 0 \in V, \forall v \in V, v + 0 = v$
4. **加法逆元**: $\forall v \in V, \exists (-v) \in V, v + (-v) = 0$
5. **标量乘法分配律**: $\forall a \in F, \forall u, v \in V, a(u + v) = au + av$
6. **标量乘法结合律**: $\forall a, b \in F, \forall v \in V, (ab)v = a(bv)$
7. **标量乘法单位元**: $\forall v \in V, 1v = v$

```python
import numpy as np
from typing import List, Tuple

class VectorSpace:
    def __init__(self, field, dimension):
        self.field = field
        self.dimension = dimension
        self.zero_vector = [0] * dimension
    
    def add_vectors(self, v1: List, v2: List) -> List:
        """向量加法"""
        if len(v1) != len(v2) or len(v1) != self.dimension:
            raise ValueError("向量维度不匹配")
        
        return [(v1[i] + v2[i]) % self.field.p for i in range(self.dimension)]
    
    def scalar_multiply(self, scalar: int, vector: List) -> List:
        """标量乘法"""
        if len(vector) != self.dimension:
            raise ValueError("向量维度不匹配")
        
        return [(scalar * vector[i]) % self.field.p for i in range(self.dimension)]
    
    def is_linear_combination(self, vectors: List[List], target: List) -> bool:
        """检查目标向量是否为给定向量的线性组合"""
        # 构建增广矩阵
        matrix = []
        for i in range(self.dimension):
            row = [vectors[j][i] for j in range(len(vectors))]
            row.append(target[i])
            matrix.append(row)
        
        # 高斯消元
        return self._solve_linear_system(matrix)
    
    def _solve_linear_system(self, matrix: List[List]) -> bool:
        """求解线性方程组"""
        n = len(matrix)
        m = len(matrix[0]) - 1
        
        # 前向消元
        for i in range(min(n, m)):
            # 寻找主元
            pivot_row = i
            for j in range(i + 1, n):
                if abs(matrix[j][i]) > abs(matrix[pivot_row][i]):
                    pivot_row = j
            
            if matrix[pivot_row][i] == 0:
                continue
            
            # 交换行
            matrix[i], matrix[pivot_row] = matrix[pivot_row], matrix[i]
            
            # 消元
            for j in range(i + 1, n):
                factor = matrix[j][i] * pow(matrix[i][i], -1, self.field.p) % self.field.p
                for k in range(i, m + 1):
                    matrix[j][k] = (matrix[j][k] - factor * matrix[i][k]) % self.field.p
        
        # 检查是否有解
        for i in range(n):
            if all(matrix[i][j] == 0 for j in range(m)) and matrix[i][m] != 0:
                return False
        
        return True
```

### 2.2 线性无关与基

**定义 2.2 (线性无关)** 向量组 $\{v_1, v_2, \ldots, v_n\}$ 称为线性无关，如果方程 $\sum_{i=1}^n a_i v_i = 0$ 只有零解。

**定义 2.3 (基)** 向量空间 $V$ 的子集 $B$ 称为 $V$ 的基，如果：
1. $B$ 是线性无关的
2. $B$ 生成 $V$，即 $\text{span}(B) = V$

```python
class Basis:
    def __init__(self, vector_space):
        self.vector_space = vector_space
        self.basis_vectors = []
    
    def is_linearly_independent(self, vectors: List[List]) -> bool:
        """检查向量组是否线性无关"""
        if len(vectors) == 0:
            return True
        
        # 构建矩阵
        matrix = []
        for i in range(self.vector_space.dimension):
            row = []
            for j in range(len(vectors)):
                row.append(vectors[j][i])
            matrix.append(row)
        
        # 计算秩
        rank = self._compute_rank(matrix)
        return rank == len(vectors)
    
    def _compute_rank(self, matrix: List[List]) -> int:
        """计算矩阵的秩"""
        n = len(matrix)
        m = len(matrix[0])
        rank = 0
        
        # 高斯消元
        for i in range(min(n, m)):
            # 寻找主元
            pivot_row = rank
            for j in range(rank, n):
                if matrix[j][i] != 0:
                    pivot_row = j
                    break
            
            if matrix[pivot_row][i] == 0:
                continue
            
            # 交换行
            matrix[rank], matrix[pivot_row] = matrix[pivot_row], matrix[rank]
            
            # 消元
            for j in range(rank + 1, n):
                if matrix[j][i] != 0:
                    factor = matrix[j][i] * pow(matrix[rank][i], -1, self.vector_space.field.p) % self.vector_space.field.p
                    for k in range(i, m):
                        matrix[j][k] = (matrix[j][k] - factor * matrix[rank][k]) % self.vector_space.field.p
            
            rank += 1
        
        return rank
    
    def find_basis(self, vectors: List[List]) -> List[List]:
        """从向量组中提取基"""
        if len(vectors) == 0:
            return []
        
        # 构建矩阵
        matrix = []
        for i in range(self.vector_space.dimension):
            row = []
            for j in range(len(vectors)):
                row.append(vectors[j][i])
            matrix.append(row)
        
        # 高斯消元
        n = len(matrix)
        m = len(matrix[0])
        rank = 0
        pivot_columns = []
        
        for i in range(min(n, m)):
            # 寻找主元
            pivot_row = rank
            for j in range(rank, n):
                if matrix[j][i] != 0:
                    pivot_row = j
                    break
            
            if matrix[pivot_row][i] == 0:
                continue
            
            # 交换行
            matrix[rank], matrix[pivot_row] = matrix[pivot_row], matrix[rank]
            pivot_columns.append(i)
            
            # 消元
            for j in range(rank + 1, n):
                if matrix[j][i] != 0:
                    factor = matrix[j][i] * pow(matrix[rank][i], -1, self.vector_space.field.p) % self.vector_space.field.p
                    for k in range(i, m):
                        matrix[j][k] = (matrix[j][k] - factor * matrix[rank][k]) % self.vector_space.field.p
            
            rank += 1
        
        # 提取基向量
        basis = []
        for col in pivot_columns:
            basis.append(vectors[col])
        
        return basis
```

## 3. 矩阵理论

### 3.1 矩阵运算

**定义 3.1 (矩阵)** $m \times n$ 矩阵是 $mn$ 个元素排列成的矩形数组。

```python
class Matrix:
    def __init__(self, rows: List[List], field):
        self.rows = rows
        self.field = field
        self.m = len(rows)
        self.n = len(rows[0]) if rows else 0
    
    def add(self, other: 'Matrix') -> 'Matrix':
        """矩阵加法"""
        if self.m != other.m or self.n != other.n:
            raise ValueError("矩阵维度不匹配")
        
        result = []
        for i in range(self.m):
            row = []
            for j in range(self.n):
                row.append((self.rows[i][j] + other.rows[i][j]) % self.field.p)
            result.append(row)
        
        return Matrix(result, self.field)
    
    def multiply(self, other: 'Matrix') -> 'Matrix':
        """矩阵乘法"""
        if self.n != other.m:
            raise ValueError("矩阵维度不匹配")
        
        result = []
        for i in range(self.m):
            row = []
            for j in range(other.n):
                element = 0
                for k in range(self.n):
                    element = (element + self.rows[i][k] * other.rows[k][j]) % self.field.p
                row.append(element)
            result.append(row)
        
        return Matrix(result, self.field)
    
    def transpose(self) -> 'Matrix':
        """矩阵转置"""
        result = []
        for j in range(self.n):
            row = []
            for i in range(self.m):
                row.append(self.rows[i][j])
            result.append(row)
        
        return Matrix(result, self.field)
    
    def determinant(self) -> int:
        """计算行列式（仅适用于方阵）"""
        if self.m != self.n:
            raise ValueError("只有方阵才有行列式")
        
        return self._compute_determinant(self.rows)
    
    def _compute_determinant(self, matrix: List[List]) -> int:
        """递归计算行列式"""
        n = len(matrix)
        if n == 1:
            return matrix[0][0]
        
        if n == 2:
            return (matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]) % self.field.p
        
        det = 0
        for j in range(n):
            # 计算余子式
            minor = []
            for i in range(1, n):
                row = []
                for k in range(n):
                    if k != j:
                        row.append(matrix[i][k])
                minor.append(row)
            
            cofactor = matrix[0][j] * self._compute_determinant(minor)
            if j % 2 == 1:
                cofactor = -cofactor
            
            det = (det + cofactor) % self.field.p
        
        return det
```

### 3.2 特征值与特征向量

**定义 3.2 (特征值)** 设 $A$ 是 $n \times n$ 矩阵，如果存在非零向量 $v$ 和标量 $\lambda$ 使得 $Av = \lambda v$，则称 $\lambda$ 是 $A$ 的特征值，$v$ 是对应的特征向量。

```python
class EigenAnalysis:
    def __init__(self, matrix: Matrix):
        self.matrix = matrix
        self.field = matrix.field
    
    def characteristic_polynomial(self) -> List[int]:
        """计算特征多项式"""
        n = self.matrix.m
        if n != self.matrix.n:
            raise ValueError("只有方阵才有特征多项式")
        
        # 构建特征矩阵
        char_matrix = []
        for i in range(n):
            row = []
            for j in range(n):
                if i == j:
                    row.append(f"x - {self.matrix.rows[i][j]}")
                else:
                    row.append(f"-{self.matrix.rows[i][j]}")
            char_matrix.append(row)
        
        # 计算行列式（符号计算）
        return self._symbolic_determinant(char_matrix)
    
    def _symbolic_determinant(self, matrix: List[List]) -> List[int]:
        """符号计算行列式"""
        n = len(matrix)
        if n == 1:
            # 解析 "x - a" 或 "-a" 形式
            return self._parse_polynomial(matrix[0][0])
        
        if n == 2:
            # 计算 2x2 符号行列式
            a = self._parse_polynomial(matrix[0][0])
            b = self._parse_polynomial(matrix[0][1])
            c = self._parse_polynomial(matrix[1][0])
            d = self._parse_polynomial(matrix[1][1])
            
            # (x-a)(x-d) - bc
            return self._multiply_polynomials(a, d)
        
        # 递归计算
        det = [0] * (n + 1)
        for j in range(n):
            # 计算余子式
            minor = []
            for i in range(1, n):
                row = []
                for k in range(n):
                    if k != j:
                        row.append(matrix[i][k])
                minor.append(row)
            
            cofactor = self._symbolic_determinant(minor)
            if j % 2 == 1:
                cofactor = self._negate_polynomial(cofactor)
            
            det = self._add_polynomials(det, cofactor)
        
        return det
    
    def _parse_polynomial(self, expr: str) -> List[int]:
        """解析多项式表达式"""
        if expr.startswith("x - "):
            a = int(expr[4:])
            return [-a, 1]  # x - a
        elif expr.startswith("-"):
            a = int(expr[1:])
            return [-a]  # -a
        else:
            a = int(expr)
            return [a]  # a
    
    def _add_polynomials(self, p1: List[int], p2: List[int]) -> List[int]:
        """多项式加法"""
        max_degree = max(len(p1), len(p2))
        result = [0] * max_degree
        
        for i in range(len(p1)):
            result[i] = (result[i] + p1[i]) % self.field.p
        
        for i in range(len(p2)):
            result[i] = (result[i] + p2[i]) % self.field.p
        
        return result
    
    def _multiply_polynomials(self, p1: List[int], p2: List[int]) -> List[int]:
        """多项式乘法"""
        result = [0] * (len(p1) + len(p2) - 1)
        
        for i in range(len(p1)):
            for j in range(len(p2)):
                result[i + j] = (result[i + j] + p1[i] * p2[j]) % self.field.p
        
        return result
    
    def _negate_polynomial(self, p: List[int]) -> List[int]:
        """多项式取负"""
        return [(-x) % self.field.p for x in p]
```

## 4. 在Web3中的应用

### 4.1 线性码与纠错编码

**定义 4.1 (线性码)** 设 $C$ 是 $\mathbb{F}_q^n$ 的子空间，则称 $C$ 是 $\mathbb{F}_q$ 上的线性码。

```python
class LinearCode:
    def __init__(self, generator_matrix: Matrix, field):
        self.G = generator_matrix
        self.field = field
        self.n = generator_matrix.n  # 码长
        self.k = generator_matrix.m  # 信息位长度
        self.d = self._compute_minimum_distance()
    
    def encode(self, message: List[int]) -> List[int]:
        """编码"""
        if len(message) != self.k:
            raise ValueError("消息长度不匹配")
        
        # c = mG
        codeword = [0] * self.n
        for i in range(self.n):
            for j in range(self.k):
                codeword[i] = (codeword[i] + message[j] * self.G.rows[j][i]) % self.field.p
        
        return codeword
    
    def decode(self, received: List[int]) -> List[int]:
        """解码（简化版本）"""
        if len(received) != self.n:
            raise ValueError("接收向量长度不匹配")
        
        # 这里实现简化的解码算法
        # 实际应用中需要更复杂的算法
        return self._syndrome_decoding(received)
    
    def _syndrome_decoding(self, received: List[int]) -> List[int]:
        """症状解码"""
        # 计算症状
        syndrome = self._compute_syndrome(received)
        
        # 查找错误模式
        error_pattern = self._find_error_pattern(syndrome)
        
        # 纠正错误
        corrected = [(received[i] - error_pattern[i]) % self.field.p 
                    for i in range(self.n)]
        
        # 解码信息位
        return self._extract_message(corrected)
    
    def _compute_syndrome(self, received: List[int]) -> List[int]:
        """计算症状"""
        # 这里需要校验矩阵H
        # 简化实现
        return [0] * (self.n - self.k)
    
    def _find_error_pattern(self, syndrome: List[int]) -> List[int]:
        """查找错误模式"""
        # 简化实现
        return [0] * self.n
    
    def _extract_message(self, codeword: List[int]) -> List[int]:
        """提取信息位"""
        # 假设前k位是信息位
        return codeword[:self.k]
    
    def _compute_minimum_distance(self) -> int:
        """计算最小距离"""
        min_distance = float('inf')
        
        # 检查所有非零码字
        for i in range(1, 2**self.k):
            message = [(i >> j) & 1 for j in range(self.k)]
            codeword = self.encode(message)
            
            weight = sum(1 for bit in codeword if bit != 0)
            if weight > 0 and weight < min_distance:
                min_distance = weight
        
        return min_distance
```

### 4.2 线性变换与密码学

```python
class LinearTransformation:
    def __init__(self, matrix: Matrix):
        self.matrix = matrix
    
    def apply(self, vector: List[int]) -> List[int]:
        """应用线性变换"""
        if len(vector) != self.matrix.n:
            raise ValueError("向量维度不匹配")
        
        result = []
        for i in range(self.matrix.m):
            element = 0
            for j in range(self.matrix.n):
                element = (element + self.matrix.rows[i][j] * vector[j]) % self.matrix.field.p
            result.append(element)
        
        return result
    
    def inverse(self) -> 'LinearTransformation':
        """计算逆变换"""
        if self.matrix.m != self.matrix.n:
            raise ValueError("只有方阵才有逆矩阵")
        
        det = self.matrix.determinant()
        if det == 0:
            raise ValueError("矩阵不可逆")
        
        # 计算伴随矩阵
        adjoint = self._compute_adjoint()
        
        # 计算逆矩阵
        det_inv = pow(det, -1, self.matrix.field.p)
        inverse_matrix = []
        for i in range(self.matrix.m):
            row = []
            for j in range(self.matrix.n):
                element = (adjoint[i][j] * det_inv) % self.matrix.field.p
                row.append(element)
            inverse_matrix.append(row)
        
        return LinearTransformation(Matrix(inverse_matrix, self.matrix.field))
    
    def _compute_adjoint(self) -> List[List[int]]:
        """计算伴随矩阵"""
        n = self.matrix.m
        adjoint = []
        
        for i in range(n):
            row = []
            for j in range(n):
                # 计算余子式
                minor = []
                for r in range(n):
                    if r != i:
                        minor_row = []
                        for c in range(n):
                            if c != j:
                                minor_row.append(self.matrix.rows[r][c])
                        minor.append(minor_row)
                
                cofactor = self._compute_determinant(minor)
                if (i + j) % 2 == 1:
                    cofactor = (-cofactor) % self.matrix.field.p
                
                row.append(cofactor)
            adjoint.append(row)
        
        return adjoint
    
    def _compute_determinant(self, matrix: List[List]) -> int:
        """计算行列式"""
        n = len(matrix)
        if n == 1:
            return matrix[0][0]
        
        if n == 2:
            return (matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]) % self.matrix.field.p
        
        det = 0
        for j in range(n):
            minor = []
            for i in range(1, n):
                row = []
                for k in range(n):
                    if k != j:
                        row.append(matrix[i][k])
                minor.append(row)
            
            cofactor = matrix[0][j] * self._compute_determinant(minor)
            if j % 2 == 1:
                cofactor = (-cofactor) % self.matrix.field.p
            
            det = (det + cofactor) % self.matrix.field.p
        
        return det
```

## 5. 安全性分析

### 5.1 线性代数攻击

```python
class LinearAlgebraAttack:
    def __init__(self, field):
        self.field = field
    
    def solve_linear_system(self, A: Matrix, b: List[int]) -> List[int]:
        """求解线性方程组 Ax = b"""
        if A.m != len(b):
            raise ValueError("矩阵和向量维度不匹配")
        
        # 构建增广矩阵
        augmented = []
        for i in range(A.m):
            row = A.rows[i].copy()
            row.append(b[i])
            augmented.append(row)
        
        # 高斯消元
        solution = self._gaussian_elimination(augmented)
        
        if solution is None:
            raise ValueError("方程组无解")
        
        return solution
    
    def _gaussian_elimination(self, matrix: List[List]) -> List[int]:
        """高斯消元"""
        n = len(matrix)
        m = len(matrix[0]) - 1
        
        # 前向消元
        for i in range(min(n, m)):
            # 寻找主元
            pivot_row = i
            for j in range(i, n):
                if matrix[j][i] != 0:
                    pivot_row = j
                    break
            
            if matrix[pivot_row][i] == 0:
                continue
            
            # 交换行
            matrix[i], matrix[pivot_row] = matrix[pivot_row], matrix[i]
            
            # 消元
            for j in range(i + 1, n):
                if matrix[j][i] != 0:
                    factor = matrix[j][i] * pow(matrix[i][i], -1, self.field.p) % self.field.p
                    for k in range(i, m + 1):
                        matrix[j][k] = (matrix[j][k] - factor * matrix[i][k]) % self.field.p
        
        # 回代
        solution = [0] * m
        for i in range(min(n, m) - 1, -1, -1):
            if matrix[i][i] == 0:
                continue
            
            sum_val = 0
            for j in range(i + 1, m):
                sum_val = (sum_val + matrix[i][j] * solution[j]) % self.field.p
            
            solution[i] = ((matrix[i][m] - sum_val) * pow(matrix[i][i], -1, self.field.p)) % self.field.p
        
        # 检查是否有解
        for i in range(n):
            if all(matrix[i][j] == 0 for j in range(m)) and matrix[i][m] != 0:
                return None
        
        return solution
```

### 5.2 矩阵分解攻击

```python
class MatrixFactorization:
    def __init__(self, field):
        self.field = field
    
    def lu_decomposition(self, A: Matrix) -> Tuple[Matrix, Matrix]:
        """LU分解"""
        if A.m != A.n:
            raise ValueError("只有方阵才能进行LU分解")
        
        n = A.m
        L = [[0] * n for _ in range(n)]
        U = [[0] * n for _ in range(n)]
        
        for i in range(n):
            L[i][i] = 1
        
        for i in range(n):
            for j in range(i, n):
                U[i][j] = A.rows[i][j]
                for k in range(i):
                    U[i][j] = (U[i][j] - L[i][k] * U[k][j]) % self.field.p
            
            for j in range(i + 1, n):
                L[j][i] = A.rows[j][i]
                for k in range(i):
                    L[j][i] = (L[j][i] - L[j][k] * U[k][i]) % self.field.p
                
                if U[i][i] != 0:
                    L[j][i] = (L[j][i] * pow(U[i][i], -1, self.field.p)) % self.field.p
        
        return Matrix(L, self.field), Matrix(U, self.field)
    
    def eigendecomposition(self, A: Matrix) -> Tuple[List[int], List[List[int]]]:
        """特征值分解（简化版本）"""
        if A.m != A.n:
            raise ValueError("只有方阵才能进行特征值分解")
        
        # 计算特征多项式
        eigen_analysis = EigenAnalysis(A)
        char_poly = eigen_analysis.characteristic_polynomial()
        
        # 寻找特征值（简化）
        eigenvalues = self._find_eigenvalues(char_poly)
        
        # 计算特征向量
        eigenvectors = []
        for eigenvalue in eigenvalues:
            eigenvector = self._find_eigenvector(A, eigenvalue)
            if eigenvector:
                eigenvectors.append(eigenvector)
        
        return eigenvalues, eigenvectors
    
    def _find_eigenvalues(self, char_poly: List[int]) -> List[int]:
        """寻找特征值（简化）"""
        # 这里应该实现更复杂的算法
        # 简化版本只返回一些可能的特征值
        eigenvalues = []
        for x in range(self.field.p):
            # 计算特征多项式在x处的值
            value = 0
            for i, coeff in enumerate(char_poly):
                value = (value + coeff * pow(x, i, self.field.p)) % self.field.p
            
            if value == 0:
                eigenvalues.append(x)
        
        return eigenvalues
    
    def _find_eigenvector(self, A: Matrix, eigenvalue: int) -> List[int]:
        """寻找特征向量"""
        # 求解 (A - λI)v = 0
        n = A.m
        matrix = []
        for i in range(n):
            row = []
            for j in range(n):
                if i == j:
                    row.append((A.rows[i][j] - eigenvalue) % self.field.p)
                else:
                    row.append(A.rows[i][j])
            matrix.append(row)
        
        # 求解齐次方程组
        return self._solve_homogeneous_system(Matrix(matrix, self.field))
    
    def _solve_homogeneous_system(self, A: Matrix) -> List[int]:
        """求解齐次方程组"""
        # 简化实现
        n = A.m
        solution = [0] * n
        solution[0] = 1  # 假设第一个分量非零
        
        return solution
```

## 6. 实现示例

### 6.1 有限域上的线性代数

```python
class GFLinearAlgebra:
    """有限域上的线性代数运算"""
    def __init__(self, p):
        self.p = p
    
    def matrix_rank(self, matrix: List[List]) -> int:
        """计算矩阵的秩"""
        n = len(matrix)
        m = len(matrix[0])
        rank = 0
        
        # 高斯消元
        for i in range(min(n, m)):
            # 寻找主元
            pivot_row = rank
            for j in range(rank, n):
                if matrix[j][i] != 0:
                    pivot_row = j
                    break
            
            if matrix[pivot_row][i] == 0:
                continue
            
            # 交换行
            matrix[rank], matrix[pivot_row] = matrix[pivot_row], matrix[rank]
            
            # 消元
            for j in range(rank + 1, n):
                if matrix[j][i] != 0:
                    factor = matrix[j][i] * pow(matrix[rank][i], -1, self.p) % self.p
                    for k in range(i, m):
                        matrix[j][k] = (matrix[j][k] - factor * matrix[rank][k]) % self.p
            
            rank += 1
        
        return rank
    
    def matrix_inverse(self, matrix: List[List]) -> List[List]:
        """计算矩阵逆"""
        n = len(matrix)
        if n != len(matrix[0]):
            raise ValueError("只有方阵才有逆矩阵")
        
        # 构建增广矩阵 [A|I]
        augmented = []
        for i in range(n):
            row = matrix[i].copy()
            for j in range(n):
                row.append(1 if i == j else 0)
            augmented.append(row)
        
        # 高斯-若尔当消元
        for i in range(n):
            # 寻找主元
            pivot_row = i
            for j in range(i, n):
                if augmented[j][i] != 0:
                    pivot_row = j
                    break
            
            if augmented[pivot_row][i] == 0:
                raise ValueError("矩阵不可逆")
            
            # 交换行
            augmented[i], augmented[pivot_row] = augmented[pivot_row], augmented[i]
            
            # 归一化
            pivot = augmented[i][i]
            pivot_inv = pow(pivot, -1, self.p)
            for j in range(2 * n):
                augmented[i][j] = (augmented[i][j] * pivot_inv) % self.p
            
            # 消元
            for j in range(n):
                if j != i and augmented[j][i] != 0:
                    factor = augmented[j][i]
                    for k in range(2 * n):
                        augmented[j][k] = (augmented[j][k] - factor * augmented[i][k]) % self.p
        
        # 提取逆矩阵
        inverse = []
        for i in range(n):
            row = []
            for j in range(n):
                row.append(augmented[i][j + n])
            inverse.append(row)
        
        return inverse
```

### 6.2 线性代数在密码学中的应用

```python
class LinearCryptoSystem:
    """基于线性代数的密码系统"""
    def __init__(self, field, key_matrix: Matrix):
        self.field = field
        self.key_matrix = key_matrix
        self.inverse_key = self._compute_inverse(key_matrix)
    
    def _compute_inverse(self, matrix: Matrix) -> Matrix:
        """计算矩阵逆"""
        n = matrix.m
        if n != matrix.n:
            raise ValueError("密钥矩阵必须是方阵")
        
        # 构建增广矩阵
        augmented = []
        for i in range(n):
            row = matrix.rows[i].copy()
            for j in range(n):
                row.append(1 if i == j else 0)
            augmented.append(row)
        
        # 高斯-若尔当消元
        for i in range(n):
            # 寻找主元
            pivot_row = i
            for j in range(i, n):
                if augmented[j][i] != 0:
                    pivot_row = j
                    break
            
            if augmented[pivot_row][i] == 0:
                raise ValueError("密钥矩阵不可逆")
            
            # 交换行
            augmented[i], augmented[pivot_row] = augmented[pivot_row], augmented[i]
            
            # 归一化
            pivot = augmented[i][i]
            pivot_inv = pow(pivot, -1, self.field.p)
            for j in range(2 * n):
                augmented[i][j] = (augmented[i][j] * pivot_inv) % self.field.p
            
            # 消元
            for j in range(n):
                if j != i and augmented[j][i] != 0:
                    factor = augmented[j][i]
                    for k in range(2 * n):
                        augmented[j][k] = (augmented[j][k] - factor * augmented[i][k]) % self.field.p
        
        # 提取逆矩阵
        inverse_rows = []
        for i in range(n):
            row = []
            for j in range(n):
                row.append(augmented[i][j + n])
            inverse_rows.append(row)
        
        return Matrix(inverse_rows, self.field)
    
    def encrypt(self, message: List[int]) -> List[int]:
        """加密"""
        if len(message) != self.key_matrix.m:
            raise ValueError("消息长度不匹配")
        
        # c = mK
        ciphertext = []
        for i in range(self.key_matrix.n):
            element = 0
            for j in range(self.key_matrix.m):
                element = (element + message[j] * self.key_matrix.rows[j][i]) % self.field.p
            ciphertext.append(element)
        
        return ciphertext
    
    def decrypt(self, ciphertext: List[int]) -> List[int]:
        """解密"""
        if len(ciphertext) != self.key_matrix.n:
            raise ValueError("密文长度不匹配")
        
        # m = cK^(-1)
        message = []
        for i in range(self.inverse_key.m):
            element = 0
            for j in range(self.inverse_key.n):
                element = (element + ciphertext[j] * self.inverse_key.rows[i][j]) % self.field.p
            message.append(element)
        
        return message
```

## 7. 总结

线性代数为Web3技术提供了重要的数学工具：

1. **向量空间理论**：为编码理论和密码学提供基础
2. **矩阵运算**：支持线性变换和特征值分析
3. **线性码**：在纠错编码和数据传输中发挥重要作用
4. **安全性**：通过线性代数攻击分析系统安全性

这些理论不仅保证了系统的可靠性，还为未来的技术创新提供了数学基础。 