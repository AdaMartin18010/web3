# 概率论与统计学基础理论

## 1. 概述

概率论与统计学是Web3技术中不可或缺的数学基础，为随机性建模、风险评估、数据分析提供了理论支撑。本文档深入探讨概率论与统计学的核心概念及其在区块链和分布式系统中的应用。

## 2. 概率论基础

### 2.1 概率空间

**定义 2.1 (概率空间)** 概率空间是一个三元组 $(\Omega, \mathcal{F}, P)$，其中：

- $\Omega$ 是样本空间
- $\mathcal{F}$ 是事件域（$\sigma$-代数）
- $P$ 是概率测度

```python
import random
import math
from typing import List, Dict, Set, Callable

class ProbabilitySpace:
    def __init__(self, sample_space: Set):
        self.sample_space = sample_space
        self.events = self._generate_sigma_algebra()
        self.probability_measure = self._initialize_probability_measure()
    
    def _generate_sigma_algebra(self) -> Set:
        """生成σ-代数"""
        # 简化实现：包含所有子集
        events = set()
        elements = list(self.sample_space)
        n = len(elements)
        
        for i in range(2**n):
            event = set()
            for j in range(n):
                if i & (1 << j):
                    event.add(elements[j])
            events.add(frozenset(event))
        
        return events
    
    def _initialize_probability_measure(self) -> Dict:
        """初始化概率测度"""
        measure = {}
        total_events = len(self.events)
        
        for event in self.events:
            # 均匀分布
            measure[event] = len(event) / len(self.sample_space)
        
        return measure
    
    def probability(self, event: Set) -> float:
        """计算事件概率"""
        event_frozen = frozenset(event)
        if event_frozen in self.probability_measure:
            return self.probability_measure[event_frozen]
        return 0.0
    
    def conditional_probability(self, A: Set, B: Set) -> float:
        """计算条件概率 P(A|B)"""
        if self.probability(B) == 0:
            return 0.0
        
        intersection = A.intersection(B)
        return self.probability(intersection) / self.probability(B)
    
    def independence_test(self, A: Set, B: Set) -> bool:
        """测试事件独立性"""
        return abs(self.probability(A.intersection(B)) - 
                  self.probability(A) * self.probability(B)) < 1e-10
```

### 2.2 随机变量

**定义 2.2 (随机变量)** 随机变量是从样本空间到实数集的函数 $X: \Omega \to \mathbb{R}$。

```python
class RandomVariable:
    def __init__(self, probability_space: ProbabilitySpace, mapping: Callable):
        self.probability_space = probability_space
        self.mapping = mapping
        self.values = self._compute_values()
        self.distribution = self._compute_distribution()
    
    def _compute_values(self) -> Set:
        """计算随机变量的可能值"""
        values = set()
        for outcome in self.probability_space.sample_space:
            value = self.mapping(outcome)
            values.add(value)
        return values
    
    def _compute_distribution(self) -> Dict:
        """计算概率分布"""
        distribution = {}
        
        for value in self.values:
            probability = 0.0
            for outcome in self.probability_space.sample_space:
                if self.mapping(outcome) == value:
                    probability += self.probability_space.probability({outcome})
            distribution[value] = probability
        
        return distribution
    
    def expectation(self) -> float:
        """计算期望"""
        expectation = 0.0
        for value, prob in self.distribution.items():
            expectation += value * prob
        return expectation
    
    def variance(self) -> float:
        """计算方差"""
        expectation = self.expectation()
        variance = 0.0
        
        for value, prob in self.distribution.items():
            variance += prob * (value - expectation) ** 2
        
        return variance
    
    def standard_deviation(self) -> float:
        """计算标准差"""
        return math.sqrt(self.variance())
    
    def moment(self, k: int) -> float:
        """计算k阶矩"""
        moment = 0.0
        for value, prob in self.distribution.items():
            moment += prob * (value ** k)
        return moment
    
    def central_moment(self, k: int) -> float:
        """计算k阶中心矩"""
        expectation = self.expectation()
        central_moment = 0.0
        
        for value, prob in self.distribution.items():
            central_moment += prob * ((value - expectation) ** k)
        
        return central_moment
```

## 3. 常见概率分布

### 3.1 离散分布

```python
class DiscreteDistribution:
    def __init__(self, distribution: Dict):
        self.distribution = distribution
        self.values = list(distribution.keys())
        self.probabilities = list(distribution.values())
    
    def pmf(self, x: float) -> float:
        """概率质量函数"""
        return self.distribution.get(x, 0.0)
    
    def cdf(self, x: float) -> float:
        """累积分布函数"""
        cumulative = 0.0
        for value, prob in self.distribution.items():
            if value <= x:
                cumulative += prob
        return cumulative
    
    def expectation(self) -> float:
        """期望"""
        return sum(value * prob for value, prob in self.distribution.items())
    
    def variance(self) -> float:
        """方差"""
        expectation = self.expectation()
        return sum(prob * (value - expectation) ** 2 
                  for value, prob in self.distribution.items())

class BinomialDistribution(DiscreteDistribution):
    def __init__(self, n: int, p: float):
        self.n = n
        self.p = p
        distribution = self._compute_distribution()
        super().__init__(distribution)
    
    def _compute_distribution(self) -> Dict:
        """计算二项分布"""
        distribution = {}
        for k in range(self.n + 1):
            prob = self._binomial_coefficient(self.n, k) * (self.p ** k) * ((1 - self.p) ** (self.n - k))
            distribution[k] = prob
        return distribution
    
    def _binomial_coefficient(self, n: int, k: int) -> int:
        """计算二项式系数"""
        if k > n:
            return 0
        if k == 0 or k == n:
            return 1
        
        # 使用帕斯卡三角形
        C = [[0] * (n + 1) for _ in range(n + 1)]
        for i in range(n + 1):
            C[i][0] = 1
            for j in range(1, i + 1):
                C[i][j] = C[i-1][j-1] + C[i-1][j]
        
        return C[n][k]

class PoissonDistribution(DiscreteDistribution):
    def __init__(self, lambda_param: float):
        self.lambda_param = lambda_param
        distribution = self._compute_distribution()
        super().__init__(distribution)
    
    def _compute_distribution(self) -> Dict:
        """计算泊松分布"""
        distribution = {}
        factorial = 1
        
        for k in range(100):  # 限制计算范围
            if k == 0:
                prob = math.exp(-self.lambda_param)
            else:
                factorial *= k
                prob = (self.lambda_param ** k) * math.exp(-self.lambda_param) / factorial
            
            if prob < 1e-10:  # 停止条件
                break
            
            distribution[k] = prob
        
        return distribution
```

### 3.2 连续分布

```python
class ContinuousDistribution:
    def __init__(self):
        pass
    
    def pdf(self, x: float) -> float:
        """概率密度函数"""
        raise NotImplementedError
    
    def cdf(self, x: float) -> float:
        """累积分布函数"""
        raise NotImplementedError
    
    def expectation(self) -> float:
        """期望"""
        raise NotImplementedError
    
    def variance(self) -> float:
        """方差"""
        raise NotImplementedError
    
    def quantile(self, p: float) -> float:
        """分位数"""
        raise NotImplementedError

class NormalDistribution(ContinuousDistribution):
    def __init__(self, mu: float, sigma: float):
        self.mu = mu
        self.sigma = sigma
    
    def pdf(self, x: float) -> float:
        """正态分布概率密度函数"""
        return (1 / (self.sigma * math.sqrt(2 * math.pi))) * \
               math.exp(-0.5 * ((x - self.mu) / self.sigma) ** 2)
    
    def cdf(self, x: float) -> float:
        """正态分布累积分布函数"""
        z = (x - self.mu) / self.sigma
        return 0.5 * (1 + self._erf(z / math.sqrt(2)))
    
    def _erf(self, x: float) -> float:
        """误差函数近似"""
        # 使用近似公式
        a1 = 0.254829592
        a2 = -0.284496736
        a3 = 1.421413741
        a4 = -1.453152027
        a5 = 1.061405429
        p = 0.3275911
        
        sign = 1 if x >= 0 else -1
        x = abs(x)
        
        t = 1 / (1 + p * x)
        y = 1 - (((((a5 * t + a4) * t) + a3) * t + a2) * t + a1) * t * math.exp(-x * x)
        
        return sign * y
    
    def expectation(self) -> float:
        return self.mu
    
    def variance(self) -> float:
        return self.sigma ** 2
    
    def quantile(self, p: float) -> float:
        """正态分布分位数"""
        # 使用近似公式
        if p < 0.5:
            return self.mu - self.sigma * self._inverse_normal_cdf(p)
        else:
            return self.mu + self.sigma * self._inverse_normal_cdf(1 - p)
    
    def _inverse_normal_cdf(self, p: float) -> float:
        """逆正态分布CDF近似"""
        # 使用近似公式
        c0 = 2.515517
        c1 = 0.802853
        c2 = 0.010328
        d1 = 1.432788
        d2 = 0.189269
        d3 = 0.001308
        
        if p <= 0 or p >= 1:
            raise ValueError("概率必须在(0,1)之间")
        
        if p < 0.5:
            t = math.sqrt(-2 * math.log(p))
        else:
            t = math.sqrt(-2 * math.log(1 - p))
        
        num = c0 + c1 * t + c2 * t * t
        den = 1 + d1 * t + d2 * t * t + d3 * t * t * t
        
        if p < 0.5:
            return -(num / den)
        else:
            return num / den

class ExponentialDistribution(ContinuousDistribution):
    def __init__(self, lambda_param: float):
        self.lambda_param = lambda_param
    
    def pdf(self, x: float) -> float:
        """指数分布概率密度函数"""
        if x < 0:
            return 0.0
        return self.lambda_param * math.exp(-self.lambda_param * x)
    
    def cdf(self, x: float) -> float:
        """指数分布累积分布函数"""
        if x < 0:
            return 0.0
        return 1 - math.exp(-self.lambda_param * x)
    
    def expectation(self) -> float:
        return 1 / self.lambda_param
    
    def variance(self) -> float:
        return 1 / (self.lambda_param ** 2)
    
    def quantile(self, p: float) -> float:
        """指数分布分位数"""
        if p < 0 or p >= 1:
            raise ValueError("概率必须在[0,1)之间")
        return -math.log(1 - p) / self.lambda_param
```

## 4. 统计推断

### 4.1 参数估计

```python
class ParameterEstimation:
    def __init__(self, data: List[float]):
        self.data = data
        self.n = len(data)
    
    def sample_mean(self) -> float:
        """样本均值"""
        return sum(self.data) / self.n
    
    def sample_variance(self) -> float:
        """样本方差"""
        mean = self.sample_mean()
        return sum((x - mean) ** 2 for x in self.data) / (self.n - 1)
    
    def sample_standard_deviation(self) -> float:
        """样本标准差"""
        return math.sqrt(self.sample_variance())
    
    def maximum_likelihood_estimation(self, distribution_type: str) -> Dict:
        """最大似然估计"""
        if distribution_type == "normal":
            return self._mle_normal()
        elif distribution_type == "exponential":
            return self._mle_exponential()
        elif distribution_type == "poisson":
            return self._mle_poisson()
        else:
            raise ValueError("不支持的分布类型")
    
    def _mle_normal(self) -> Dict:
        """正态分布的最大似然估计"""
        mu_hat = self.sample_mean()
        sigma_squared_hat = sum((x - mu_hat) ** 2 for x in self.data) / self.n
        
        return {
            "mu": mu_hat,
            "sigma": math.sqrt(sigma_squared_hat)
        }
    
    def _mle_exponential(self) -> Dict:
        """指数分布的最大似然估计"""
        lambda_hat = self.n / sum(self.data)
        return {"lambda": lambda_hat}
    
    def _mle_poisson(self) -> Dict:
        """泊松分布的最大似然估计"""
        lambda_hat = self.sample_mean()
        return {"lambda": lambda_hat}
    
    def confidence_interval(self, confidence_level: float = 0.95) -> Dict:
        """置信区间"""
        mean = self.sample_mean()
        std_error = self.sample_standard_deviation() / math.sqrt(self.n)
        
        # 使用t分布
        t_value = self._t_distribution_quantile(confidence_level, self.n - 1)
        margin_of_error = t_value * std_error
        
        return {
            "lower": mean - margin_of_error,
            "upper": mean + margin_of_error,
            "confidence_level": confidence_level
        }
    
    def _t_distribution_quantile(self, p: float, df: int) -> float:
        """t分布分位数近似"""
        # 简化近似，实际应用中应使用更精确的方法
        if df > 30:
            # 大样本时近似为正态分布
            normal_dist = NormalDistribution(0, 1)
            return normal_dist.quantile(p)
        else:
            # 小样本时的近似
            return 1.96  # 简化处理
```

### 4.2 假设检验

```python
class HypothesisTesting:
    def __init__(self, data: List[float]):
        self.data = data
        self.n = len(data)
    
    def t_test(self, mu0: float, alpha: float = 0.05) -> Dict:
        """单样本t检验"""
        sample_mean = sum(self.data) / self.n
        sample_variance = sum((x - sample_mean) ** 2 for x in self.data) / (self.n - 1)
        sample_std = math.sqrt(sample_variance)
        
        # 计算t统计量
        t_statistic = (sample_mean - mu0) / (sample_std / math.sqrt(self.n))
        
        # 计算p值（简化）
        p_value = self._calculate_p_value_t(t_statistic, self.n - 1)
        
        # 决策
        reject_null = p_value < alpha
        
        return {
            "t_statistic": t_statistic,
            "p_value": p_value,
            "reject_null": reject_null,
            "alpha": alpha
        }
    
    def _calculate_p_value_t(self, t_statistic: float, df: int) -> float:
        """计算t检验的p值（简化）"""
        # 简化实现，实际应用中应使用更精确的方法
        if abs(t_statistic) > 2:
            return 0.05  # 简化处理
        else:
            return 0.5  # 简化处理
    
    def chi_square_test(self, expected_frequencies: List[float]) -> Dict:
        """卡方检验"""
        if len(self.data) != len(expected_frequencies):
            raise ValueError("数据长度不匹配")
        
        # 计算卡方统计量
        chi_square = 0.0
        for observed, expected in zip(self.data, expected_frequencies):
            if expected > 0:
                chi_square += (observed - expected) ** 2 / expected
        
        # 计算p值（简化）
        p_value = self._calculate_p_value_chi_square(chi_square, len(self.data) - 1)
        
        return {
            "chi_square_statistic": chi_square,
            "p_value": p_value,
            "degrees_of_freedom": len(self.data) - 1
        }
    
    def _calculate_p_value_chi_square(self, chi_square: float, df: int) -> float:
        """计算卡方检验的p值（简化）"""
        # 简化实现
        if chi_square > df + 2 * math.sqrt(2 * df):
            return 0.05
        else:
            return 0.5
```

## 5. 在Web3中的应用

### 5.1 区块链随机性

```python
class BlockchainRandomness:
    def __init__(self, seed: str):
        self.seed = seed
        self.random_generator = self._initialize_generator()
    
    def _initialize_generator(self) -> random.Random:
        """初始化随机数生成器"""
        # 使用种子初始化
        rng = random.Random()
        rng.seed(self.seed)
        return rng
    
    def verifiable_random_function(self, input_data: str) -> Dict:
        """可验证随机函数"""
        # 简化实现
        combined = self.seed + input_data
        hash_value = hash(combined) % (2**256)
        
        # 生成随机数
        random_value = self.random_generator.random()
        
        # 生成证明（简化）
        proof = {
            "hash": hash_value,
            "random_value": random_value,
            "input": input_data
        }
        
        return proof
    
    def proof_of_stake_randomness(self, stakes: List[float]) -> int:
        """权益证明随机选择"""
        total_stake = sum(stakes)
        if total_stake == 0:
            return 0
        
        # 使用累积分布函数进行加权随机选择
        cumulative = 0.0
        random_value = self.random_generator.random()
        
        for i, stake in enumerate(stakes):
            cumulative += stake / total_stake
            if random_value <= cumulative:
                return i
        
        return len(stakes) - 1
    
    def byzantine_fault_tolerance_probability(self, n: int, f: int) -> float:
        """拜占庭容错概率"""
        # 计算在n个节点中有f个恶意节点时的安全性概率
        if f >= n / 3:
            return 0.0  # 不可能达成共识
        
        # 简化计算
        honest_nodes = n - f
        required_quorum = 2 * f + 1
        
        if honest_nodes >= required_quorum:
            return 1.0
        else:
            return 0.0
```

### 5.2 风险评估

```python
class RiskAssessment:
    def __init__(self):
        self.risk_models = {}
    
    def value_at_risk(self, returns: List[float], confidence_level: float = 0.95) -> float:
        """计算风险价值(VaR)"""
        sorted_returns = sorted(returns)
        index = int((1 - confidence_level) * len(sorted_returns))
        return sorted_returns[index]
    
    def expected_shortfall(self, returns: List[float], confidence_level: float = 0.95) -> float:
        """计算期望损失(ES)"""
        var = self.value_at_risk(returns, confidence_level)
        tail_returns = [r for r in returns if r <= var]
        
        if not tail_returns:
            return var
        
        return sum(tail_returns) / len(tail_returns)
    
    def portfolio_risk(self, weights: List[float], returns_matrix: List[List[float]]) -> Dict:
        """投资组合风险分析"""
        if len(weights) != len(returns_matrix):
            raise ValueError("权重和收益矩阵维度不匹配")
        
        # 计算协方差矩阵
        n_assets = len(weights)
        covariance_matrix = [[0.0] * n_assets for _ in range(n_assets)]
        
        for i in range(n_assets):
            for j in range(n_assets):
                if i == j:
                    # 方差
                    mean_i = sum(returns_matrix[i]) / len(returns_matrix[i])
                    variance = sum((r - mean_i) ** 2 for r in returns_matrix[i]) / (len(returns_matrix[i]) - 1)
                    covariance_matrix[i][j] = variance
                else:
                    # 协方差
                    mean_i = sum(returns_matrix[i]) / len(returns_matrix[i])
                    mean_j = sum(returns_matrix[j]) / len(returns_matrix[j])
                    covariance = sum((returns_matrix[i][k] - mean_i) * (returns_matrix[j][k] - mean_j) 
                                   for k in range(len(returns_matrix[i]))) / (len(returns_matrix[i]) - 1)
                    covariance_matrix[i][j] = covariance
        
        # 计算投资组合方差
        portfolio_variance = 0.0
        for i in range(n_assets):
            for j in range(n_assets):
                portfolio_variance += weights[i] * weights[j] * covariance_matrix[i][j]
        
        portfolio_volatility = math.sqrt(portfolio_variance)
        
        return {
            "portfolio_variance": portfolio_variance,
            "portfolio_volatility": portfolio_volatility,
            "covariance_matrix": covariance_matrix
        }
    
    def monte_carlo_simulation(self, initial_value: float, drift: float, volatility: float, 
                              time_steps: int, n_simulations: int) -> List[List[float]]:
        """蒙特卡洛模拟"""
        simulations = []
        dt = 1.0 / time_steps
        
        for _ in range(n_simulations):
            path = [initial_value]
            current_value = initial_value
            
            for _ in range(time_steps):
                # 随机游走
                random_shock = self.random_generator.normalvariate(0, 1)
                current_value *= math.exp((drift - 0.5 * volatility ** 2) * dt + 
                                        volatility * math.sqrt(dt) * random_shock)
                path.append(current_value)
            
            simulations.append(path)
        
        return simulations
```

## 6. 数据分析与机器学习

### 6.1 时间序列分析

```python
class TimeSeriesAnalysis:
    def __init__(self, time_series: List[float]):
        self.time_series = time_series
        self.n = len(time_series)
    
    def moving_average(self, window_size: int) -> List[float]:
        """移动平均"""
        if window_size > self.n:
            raise ValueError("窗口大小不能超过序列长度")
        
        moving_averages = []
        for i in range(window_size - 1, self.n):
            window = self.time_series[i - window_size + 1:i + 1]
            moving_averages.append(sum(window) / window_size)
        
        return moving_averages
    
    def exponential_smoothing(self, alpha: float) -> List[float]:
        """指数平滑"""
        if alpha < 0 or alpha > 1:
            raise ValueError("平滑参数必须在[0,1]之间")
        
        smoothed = [self.time_series[0]]
        
        for i in range(1, self.n):
            smoothed_value = alpha * self.time_series[i] + (1 - alpha) * smoothed[i - 1]
            smoothed.append(smoothed_value)
        
        return smoothed
    
    def autocorrelation(self, lag: int) -> float:
        """自相关函数"""
        if lag >= self.n:
            return 0.0
        
        mean = sum(self.time_series) / self.n
        variance = sum((x - mean) ** 2 for x in self.time_series) / self.n
        
        if variance == 0:
            return 0.0
        
        autocorr = 0.0
        for i in range(self.n - lag):
            autocorr += (self.time_series[i] - mean) * (self.time_series[i + lag] - mean)
        
        return autocorr / ((self.n - lag) * variance)
    
    def stationarity_test(self) -> Dict:
        """平稳性检验"""
        # 简化的平稳性检验
        first_half = self.time_series[:self.n // 2]
        second_half = self.time_series[self.n // 2:]
        
        mean_first = sum(first_half) / len(first_half)
        mean_second = sum(second_half) / len(second_half)
        
        var_first = sum((x - mean_first) ** 2 for x in first_half) / len(first_half)
        var_second = sum((x - mean_second) ** 2 for x in second_half) / len(second_half)
        
        # 简单的均值方差检验
        mean_difference = abs(mean_first - mean_second)
        var_difference = abs(var_first - var_second)
        
        return {
            "is_stationary": mean_difference < 0.1 and var_difference < 0.1,
            "mean_difference": mean_difference,
            "variance_difference": var_difference
        }
```

### 6.2 异常检测

```python
class AnomalyDetection:
    def __init__(self, data: List[float]):
        self.data = data
        self.mean = sum(data) / len(data)
        self.std = math.sqrt(sum((x - self.mean) ** 2 for x in data) / len(data))
    
    def z_score_detection(self, threshold: float = 3.0) -> List[bool]:
        """Z-score异常检测"""
        anomalies = []
        for x in self.data:
            z_score = abs((x - self.mean) / self.std)
            anomalies.append(z_score > threshold)
        return anomalies
    
    def iqr_detection(self, k: float = 1.5) -> List[bool]:
        """四分位距异常检测"""
        sorted_data = sorted(self.data)
        n = len(sorted_data)
        
        q1_index = n // 4
        q3_index = 3 * n // 4
        
        q1 = sorted_data[q1_index]
        q3 = sorted_data[q3_index]
        iqr = q3 - q1
        
        lower_bound = q1 - k * iqr
        upper_bound = q3 + k * iqr
        
        anomalies = []
        for x in self.data:
            anomalies.append(x < lower_bound or x > upper_bound)
        
        return anomalies
    
    def isolation_forest(self, contamination: float = 0.1) -> List[bool]:
        """隔离森林异常检测（简化版本）"""
        # 简化实现
        n_anomalies = int(len(self.data) * contamination)
        
        # 使用标准差作为异常分数
        scores = []
        for x in self.data:
            score = abs((x - self.mean) / self.std)
            scores.append(score)
        
        # 选择分数最高的作为异常
        threshold = sorted(scores, reverse=True)[n_anomalies - 1]
        
        anomalies = []
        for score in scores:
            anomalies.append(score >= threshold)
        
        return anomalies
```

## 7. 实现示例

### 7.1 区块链数据分析

```python
class BlockchainAnalytics:
    def __init__(self, transaction_data: List[Dict]):
        self.transaction_data = transaction_data
    
    def transaction_volume_analysis(self) -> Dict:
        """交易量分析"""
        volumes = [tx['volume'] for tx in self.transaction_data]
        
        analysis = {
            "total_volume": sum(volumes),
            "average_volume": sum(volumes) / len(volumes),
            "max_volume": max(volumes),
            "min_volume": min(volumes),
            "volume_std": math.sqrt(sum((v - sum(volumes)/len(volumes)) ** 2 for v in volumes) / len(volumes))
        }
        
        return analysis
    
    def network_activity_prediction(self, time_window: int = 24) -> Dict:
        """网络活动预测"""
        # 按时间窗口聚合数据
        hourly_volumes = {}
        for tx in self.transaction_data:
            hour = tx['timestamp'] // 3600
            if hour not in hourly_volumes:
                hourly_volumes[hour] = 0
            hourly_volumes[hour] += tx['volume']
        
        # 计算时间序列统计
        volumes = list(hourly_volumes.values())
        
        # 简单的移动平均预测
        if len(volumes) >= time_window:
            recent_volumes = volumes[-time_window:]
            prediction = sum(recent_volumes) / len(recent_volumes)
        else:
            prediction = sum(volumes) / len(volumes) if volumes else 0
        
        return {
            "predicted_volume": prediction,
            "confidence_interval": self._calculate_prediction_interval(volumes, prediction)
        }
    
    def _calculate_prediction_interval(self, volumes: List[float], prediction: float) -> Dict:
        """计算预测区间"""
        if len(volumes) < 2:
            return {"lower": prediction, "upper": prediction}
        
        std = math.sqrt(sum((v - prediction) ** 2 for v in volumes) / (len(volumes) - 1))
        margin = 1.96 * std  # 95%置信区间
        
        return {
            "lower": max(0, prediction - margin),
            "upper": prediction + margin
        }
    
    def risk_assessment(self) -> Dict:
        """风险评估"""
        volumes = [tx['volume'] for tx in self.transaction_data]
        
        # 计算风险指标
        var_95 = self._value_at_risk(volumes, 0.95)
        var_99 = self._value_at_risk(volumes, 0.99)
        
        return {
            "var_95": var_95,
            "var_99": var_99,
            "volatility": math.sqrt(sum((v - sum(volumes)/len(volumes)) ** 2 for v in volumes) / len(volumes)),
            "max_drawdown": self._calculate_max_drawdown(volumes)
        }
    
    def _value_at_risk(self, data: List[float], confidence_level: float) -> float:
        """计算风险价值"""
        sorted_data = sorted(data)
        index = int((1 - confidence_level) * len(sorted_data))
        return sorted_data[index]
    
    def _calculate_max_drawdown(self, data: List[float]) -> float:
        """计算最大回撤"""
        if not data:
            return 0.0
        
        peak = data[0]
        max_drawdown = 0.0
        
        for value in data:
            if value > peak:
                peak = value
            drawdown = (peak - value) / peak
            max_drawdown = max(max_drawdown, drawdown)
        
        return max_drawdown
```

### 7.2 智能合约风险评估

```python
class SmartContractRiskAssessment:
    def __init__(self, contract_data: List[Dict]):
        self.contract_data = contract_data
    
    def vulnerability_analysis(self) -> Dict:
        """漏洞分析"""
        vulnerabilities = {
            "reentrancy": 0,
            "overflow": 0,
            "access_control": 0,
            "logic_errors": 0
        }
        
        for contract in self.contract_data:
            for vuln_type in vulnerabilities:
                if contract.get(f'has_{vuln_type}', False):
                    vulnerabilities[vuln_type] += 1
        
        total_contracts = len(self.contract_data)
        risk_scores = {}
        
        for vuln_type, count in vulnerabilities.items():
            risk_scores[vuln_type] = count / total_contracts if total_contracts > 0 else 0
        
        return {
            "vulnerability_counts": vulnerabilities,
            "risk_scores": risk_scores,
            "overall_risk_score": sum(risk_scores.values()) / len(risk_scores)
        }
    
    def gas_optimization_analysis(self) -> Dict:
        """Gas优化分析"""
        gas_costs = [contract.get('gas_cost', 0) for contract in self.contract_data]
        
        if not gas_costs:
            return {"average_gas": 0, "gas_efficiency": 0}
        
        average_gas = sum(gas_costs) / len(gas_costs)
        
        # 计算Gas效率（相对于平均值）
        efficiency_scores = []
        for gas_cost in gas_costs:
            if average_gas > 0:
                efficiency = 1 - (gas_cost / average_gas)
                efficiency_scores.append(max(0, efficiency))
            else:
                efficiency_scores.append(0)
        
        return {
            "average_gas": average_gas,
            "gas_efficiency": sum(efficiency_scores) / len(efficiency_scores),
            "gas_distribution": {
                "low": len([g for g in gas_costs if g < average_gas * 0.5]),
                "medium": len([g for g in gas_costs if average_gas * 0.5 <= g <= average_gas * 1.5]),
                "high": len([g for g in gas_costs if g > average_gas * 1.5])
            }
        }
```

## 8. 总结

概率论与统计学为Web3技术提供了重要的数学基础：

1. **随机性建模**：为区块链共识机制和随机数生成提供理论支撑
2. **风险评估**：支持DeFi风险评估和投资组合管理
3. **数据分析**：为链上数据分析和异常检测提供方法
4. **预测建模**：支持网络活动预测和智能合约风险评估

这些理论不仅保证了系统的可靠性，还为Web3生态的安全发展提供了科学依据。
