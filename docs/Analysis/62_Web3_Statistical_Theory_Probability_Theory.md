# Web3统计理论与概率论

## 概述

本文档建立Web3系统的统计理论与概率论基础，从概率论基础、统计推断、随机过程、贝叶斯理论、机器学习统计等多个维度构建完整的理论体系。

## 1. 概率论基础

### 1.1 概率空间

**定义 1.1.1 (概率空间)**
概率空间 $(\Omega, \mathcal{F}, P)$ 包含样本空间、事件域和概率测度。

**定义 1.1.2 (Web3概率空间)**
Web3概率空间描述区块链网络中的随机事件。

**算法 1.1.1 (概率空间构建算法)**

```rust
pub struct ProbabilitySpace {
    sample_space: Vec<Event>,
    events: Vec<EventSet>,
    probability_measure: HashMap<EventSet, f64>,
}

impl ProbabilitySpace {
    pub fn new() -> Self {
        ProbabilitySpace {
            sample_space: Vec::new(),
            events: Vec::new(),
            probability_measure: HashMap::new(),
        }
    }
    
    pub fn add_event(&mut self, event: Event, probability: f64) {
        let event_set = EventSet::singleton(event.clone());
        self.sample_space.push(event);
        self.events.push(event_set.clone());
        self.probability_measure.insert(event_set, probability);
    }
    
    pub fn calculate_probability(&self, event_set: &EventSet) -> f64 {
        let mut total_probability = 0.0;
        
        for event in &event_set.events {
            if let Some(&prob) = self.probability_measure.get(&EventSet::singleton(event.clone())) {
                total_probability += prob;
            }
        }
        
        total_probability
    }
    
    pub fn conditional_probability(&self, a: &EventSet, b: &EventSet) -> f64 {
        let intersection = a.intersection(b);
        let p_intersection = self.calculate_probability(&intersection);
        let p_b = self.calculate_probability(b);
        
        if p_b > 0.0 {
            p_intersection / p_b
        } else {
            0.0
        }
    }
}
```

### 1.2 随机变量

**定义 1.2.1 (随机变量)**
随机变量是从样本空间到实数的映射。

**定义 1.2.2 (分布函数)**
$F_X(x) = P(X \leq x)$ 为随机变量X的分布函数。

**算法 1.2.1 (随机变量算法)**

```rust
pub struct RandomVariable {
    name: String,
    distribution: Box<dyn Distribution>,
}

impl RandomVariable {
    pub fn new(name: String, distribution: Box<dyn Distribution>) -> Self {
        RandomVariable { name, distribution }
    }
    
    pub fn sample(&self) -> f64 {
        self.distribution.sample()
    }
    
    pub fn probability_density(&self, x: f64) -> f64 {
        self.distribution.pdf(x)
    }
    
    pub fn cumulative_distribution(&self, x: f64) -> f64 {
        self.distribution.cdf(x)
    }
    
    pub fn expected_value(&self) -> f64 {
        self.distribution.mean()
    }
    
    pub fn variance(&self) -> f64 {
        self.distribution.variance()
    }
}

pub trait Distribution {
    fn sample(&self) -> f64;
    fn pdf(&self, x: f64) -> f64;
    fn cdf(&self, x: f64) -> f64;
    fn mean(&self) -> f64;
    fn variance(&self) -> f64;
}

pub struct NormalDistribution {
    mean: f64,
    variance: f64,
}

impl Distribution for NormalDistribution {
    fn sample(&self) -> f64 {
        let mut rng = rand::thread_rng();
        let u1: f64 = rng.gen();
        let u2: f64 = rng.gen();
        
        // Box-Muller变换
        let z0 = (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos();
        self.mean + z0 * self.variance.sqrt()
    }
    
    fn pdf(&self, x: f64) -> f64 {
        let sigma = self.variance.sqrt();
        let exponent = -0.5 * ((x - self.mean) / sigma).powi(2);
        (1.0 / (sigma * (2.0 * std::f64::consts::PI).sqrt())) * exponent.exp()
    }
    
    fn cdf(&self, x: f64) -> f64 {
        let z = (x - self.mean) / self.variance.sqrt();
        0.5 * (1.0 + erf(z / 2.0_f64.sqrt()))
    }
    
    fn mean(&self) -> f64 {
        self.mean
    }
    
    fn variance(&self) -> f64 {
        self.variance
    }
}

fn erf(x: f64) -> f64 {
    // 误差函数的近似实现
    let a1 = 0.254829592;
    let a2 = -0.284496736;
    let a3 = 1.421413741;
    let a4 = -1.453152027;
    let a5 = 1.061405429;
    let p = 0.3275911;
    
    let sign = if x < 0.0 { -1.0 } else { 1.0 };
    let x = x.abs();
    
    let t = 1.0 / (1.0 + p * x);
    let y = 1.0 - (((((a5 * t + a4) * t) + a3) * t + a2) * t + a1) * t * (-x * x).exp();
    
    sign * y
}
```

## 2. 统计推断

### 2.1 参数估计

**定义 2.1.1 (参数估计)**
参数估计是从样本数据推断总体参数的过程。

**定义 2.1.2 (最大似然估计)**
$$\hat{\theta} = \arg\max_{\theta} L(\theta|X)$$

**算法 2.1.1 (最大似然估计算法)**

```rust
pub struct MaximumLikelihoodEstimator {
    data: Vec<f64>,
    distribution_type: DistributionType,
}

impl MaximumLikelihoodEstimator {
    pub fn new(data: Vec<f64>, distribution_type: DistributionType) -> Self {
        MaximumLikelihoodEstimator { data, distribution_type }
    }
    
    pub fn estimate_parameters(&self) -> EstimatedParameters {
        match self.distribution_type {
            DistributionType::Normal => self.estimate_normal_parameters(),
            DistributionType::Exponential => self.estimate_exponential_parameters(),
            DistributionType::Poisson => self.estimate_poisson_parameters(),
        }
    }
    
    fn estimate_normal_parameters(&self) -> EstimatedParameters {
        let n = self.data.len() as f64;
        let mean = self.data.iter().sum::<f64>() / n;
        let variance = self.data.iter()
            .map(|x| (x - mean).powi(2))
            .sum::<f64>() / n;
        
        EstimatedParameters {
            mean: Some(mean),
            variance: Some(variance),
            lambda: None,
        }
    }
    
    fn estimate_exponential_parameters(&self) -> EstimatedParameters {
        let n = self.data.len() as f64;
        let mean = self.data.iter().sum::<f64>() / n;
        let lambda = 1.0 / mean;
        
        EstimatedParameters {
            mean: Some(mean),
            variance: Some(mean.powi(2)),
            lambda: Some(lambda),
        }
    }
    
    fn estimate_poisson_parameters(&self) -> EstimatedParameters {
        let n = self.data.len() as f64;
        let lambda = self.data.iter().sum::<f64>() / n;
        
        EstimatedParameters {
            mean: Some(lambda),
            variance: Some(lambda),
            lambda: Some(lambda),
        }
    }
    
    pub fn log_likelihood(&self, parameters: &EstimatedParameters) -> f64 {
        let mut log_likelihood = 0.0;
        
        for &x in &self.data {
            log_likelihood += self.log_pdf(x, parameters);
        }
        
        log_likelihood
    }
    
    fn log_pdf(&self, x: f64, parameters: &EstimatedParameters) -> f64 {
        match self.distribution_type {
            DistributionType::Normal => {
                let mean = parameters.mean.unwrap();
                let variance = parameters.variance.unwrap();
                let sigma = variance.sqrt();
                -0.5 * ((x - mean) / sigma).powi(2) - sigma.ln() - (2.0 * std::f64::consts::PI).ln() / 2.0
            },
            DistributionType::Exponential => {
                let lambda = parameters.lambda.unwrap();
                lambda.ln() - lambda * x
            },
            DistributionType::Poisson => {
                let lambda = parameters.lambda.unwrap();
                x * lambda.ln() - lambda - (1..=x as i32).map(|i| i as f64).sum::<f64>().ln()
            }
        }
    }
}
```

### 2.2 假设检验

**定义 2.2.1 (假设检验)**
假设检验是检验统计假设的过程。

**定义 2.2.2 (p值)**
p值是观察到的统计量至少与观测值一样极端的概率。

**算法 2.2.1 (假设检验算法)**

```rust
pub struct HypothesisTest {
    null_hypothesis: StatisticalHypothesis,
    alternative_hypothesis: StatisticalHypothesis,
    test_statistic: Box<dyn TestStatistic>,
    significance_level: f64,
}

impl HypothesisTest {
    pub fn new(
        null_hypothesis: StatisticalHypothesis,
        alternative_hypothesis: StatisticalHypothesis,
        test_statistic: Box<dyn TestStatistic>,
        significance_level: f64,
    ) -> Self {
        HypothesisTest {
            null_hypothesis,
            alternative_hypothesis,
            test_statistic,
            significance_level,
        }
    }
    
    pub fn perform_test(&self, data: &[f64]) -> TestResult {
        let test_statistic_value = self.test_statistic.calculate(data);
        let p_value = self.calculate_p_value(test_statistic_value, data);
        let critical_value = self.calculate_critical_value();
        
        let reject_null = p_value < self.significance_level;
        
        TestResult {
            test_statistic: test_statistic_value,
            p_value,
            critical_value,
            reject_null_hypothesis: reject_null,
            conclusion: if reject_null {
                "Reject null hypothesis".to_string()
            } else {
                "Fail to reject null hypothesis".to_string()
            },
        }
    }
    
    fn calculate_p_value(&self, test_statistic: f64, data: &[f64]) -> f64 {
        // 使用蒙特卡洛方法计算p值
        let num_simulations = 10000;
        let mut extreme_count = 0;
        
        for _ in 0..num_simulations {
            let simulated_data = self.generate_simulated_data(data);
            let simulated_statistic = self.test_statistic.calculate(&simulated_data);
            
            if simulated_statistic >= test_statistic {
                extreme_count += 1;
            }
        }
        
        extreme_count as f64 / num_simulations as f64
    }
    
    fn generate_simulated_data(&self, original_data: &[f64]) -> Vec<f64> {
        // 在零假设下生成模拟数据
        let mut rng = rand::thread_rng();
        let mut simulated_data = Vec::new();
        
        for _ in 0..original_data.len() {
            let sample = match self.null_hypothesis.distribution_type {
                DistributionType::Normal => {
                    let mean = self.null_hypothesis.parameters.mean.unwrap();
                    let variance = self.null_hypothesis.parameters.variance.unwrap();
                    NormalDistribution { mean, variance }.sample()
                },
                DistributionType::Exponential => {
                    let lambda = self.null_hypothesis.parameters.lambda.unwrap();
                    ExponentialDistribution { lambda }.sample()
                },
                _ => rng.gen(),
            };
            simulated_data.push(sample);
        }
        
        simulated_data
    }
    
    fn calculate_critical_value(&self) -> f64 {
        // 基于显著性水平计算临界值
        match self.test_statistic.distribution_type() {
            DistributionType::Normal => 1.96, // 95%置信水平
            DistributionType::ChiSquare => 3.841, // 自由度为1的卡方分布
            _ => 1.96,
        }
    }
}

pub trait TestStatistic {
    fn calculate(&self, data: &[f64]) -> f64;
    fn distribution_type(&self) -> DistributionType;
}

pub struct TTestStatistic;

impl TestStatistic for TTestStatistic {
    fn calculate(&self, data: &[f64]) -> f64 {
        let n = data.len() as f64;
        let mean = data.iter().sum::<f64>() / n;
        let variance = data.iter()
            .map(|x| (x - mean).powi(2))
            .sum::<f64>() / (n - 1.0);
        let standard_error = variance.sqrt() / n.sqrt();
        
        mean / standard_error
    }
    
    fn distribution_type(&self) -> DistributionType {
        DistributionType::Normal
    }
}
```

## 3. 随机过程

### 3.1 马尔可夫链

**定义 3.1.1 (马尔可夫链)**
马尔可夫链是具有马尔可夫性质的随机过程。

**定义 3.1.2 (转移概率)**
$P_{ij} = P(X_{n+1} = j | X_n = i)$ 为转移概率。

**算法 3.1.1 (马尔可夫链算法)**

```rust
pub struct MarkovChain {
    states: Vec<String>,
    transition_matrix: Matrix,
    initial_distribution: Vec<f64>,
}

impl MarkovChain {
    pub fn new(states: Vec<String>, transition_matrix: Matrix, initial_distribution: Vec<f64>) -> Self {
        MarkovChain {
            states,
            transition_matrix,
            initial_distribution,
        }
    }
    
    pub fn simulate(&self, steps: usize) -> Vec<String> {
        let mut current_state = self.sample_initial_state();
        let mut path = vec![current_state.clone()];
        
        for _ in 0..steps {
            current_state = self.transition(&current_state);
            path.push(current_state.clone());
        }
        
        path
    }
    
    fn sample_initial_state(&self) -> String {
        let mut rng = rand::thread_rng();
        let random_value = rng.gen::<f64>();
        let mut cumulative = 0.0;
        
        for (i, &prob) in self.initial_distribution.iter().enumerate() {
            cumulative += prob;
            if random_value <= cumulative {
                return self.states[i].clone();
            }
        }
        
        self.states.last().unwrap().clone()
    }
    
    fn transition(&self, current_state: &str) -> String {
        let current_index = self.states.iter().position(|s| s == current_state).unwrap();
        let transition_probs = &self.transition_matrix[current_index];
        
        let mut rng = rand::thread_rng();
        let random_value = rng.gen::<f64>();
        let mut cumulative = 0.0;
        
        for (i, &prob) in transition_probs.iter().enumerate() {
            cumulative += prob;
            if random_value <= cumulative {
                return self.states[i].clone();
            }
        }
        
        self.states.last().unwrap().clone()
    }
    
    pub fn stationary_distribution(&self) -> Vec<f64> {
        let mut distribution = self.initial_distribution.clone();
        let max_iterations = 1000;
        let tolerance = 1e-6;
        
        for _ in 0..max_iterations {
            let new_distribution = self.transition_matrix.multiply_vector(&distribution);
            let change = self.calculate_distribution_change(&distribution, &new_distribution);
            
            if change < tolerance {
                break;
            }
            
            distribution = new_distribution;
        }
        
        distribution
    }
    
    fn calculate_distribution_change(&self, old_dist: &[f64], new_dist: &[f64]) -> f64 {
        old_dist.iter().zip(new_dist.iter())
            .map(|(old, new)| (old - new).abs())
            .sum::<f64>()
    }
}
```

### 3.2 泊松过程

**定义 3.2.1 (泊松过程)**
泊松过程是计数过程，具有独立增量和平稳增量性质。

**算法 3.2.1 (泊松过程算法)**

```rust
pub struct PoissonProcess {
    rate: f64,
    time_horizon: f64,
}

impl PoissonProcess {
    pub fn new(rate: f64, time_horizon: f64) -> Self {
        PoissonProcess { rate, time_horizon }
    }
    
    pub fn simulate(&self) -> Vec<f64> {
        let mut event_times = Vec::new();
        let mut current_time = 0.0;
        let mut rng = rand::thread_rng();
        
        while current_time < self.time_horizon {
            // 生成指数分布的等待时间
            let waiting_time = ExponentialDistribution { lambda: self.rate }.sample();
            current_time += waiting_time;
            
            if current_time < self.time_horizon {
                event_times.push(current_time);
            }
        }
        
        event_times
    }
    
    pub fn expected_events(&self) -> f64 {
        self.rate * self.time_horizon
    }
    
    pub fn probability_of_n_events(&self, n: usize) -> f64 {
        let lambda = self.expected_events();
        (lambda.powi(n as i32) * (-lambda).exp()) / factorial(n)
    }
}

fn factorial(n: usize) -> f64 {
    if n <= 1 {
        1.0
    } else {
        n as f64 * factorial(n - 1)
    }
}
```

## 4. 贝叶斯理论

### 4.1 贝叶斯推断

**定义 4.1.1 (贝叶斯定理)**
$$P(\theta|X) = \frac{P(X|\theta)P(\theta)}{P(X)}$$

**算法 4.1.1 (贝叶斯推断算法)**

```rust
pub struct BayesianInference {
    prior: Box<dyn Distribution>,
    likelihood: Box<dyn LikelihoodFunction>,
    data: Vec<f64>,
}

impl BayesianInference {
    pub fn new(prior: Box<dyn Distribution>, likelihood: Box<dyn LikelihoodFunction>, data: Vec<f64>) -> Self {
        BayesianInference { prior, likelihood, data }
    }
    
    pub fn posterior_distribution(&self) -> PosteriorDistribution {
        let mut posterior_samples = Vec::new();
        let num_samples = 10000;
        
        // 使用马尔可夫链蒙特卡洛(MCMC)采样
        let mut current_theta = self.prior.sample();
        
        for _ in 0..num_samples {
            let proposal = self.propose_new_theta(current_theta);
            let acceptance_ratio = self.calculate_acceptance_ratio(current_theta, proposal);
            
            let mut rng = rand::thread_rng();
            if rng.gen::<f64>() < acceptance_ratio {
                current_theta = proposal;
            }
            
            posterior_samples.push(current_theta);
        }
        
        PosteriorDistribution { samples: posterior_samples }
    }
    
    fn propose_new_theta(&self, current_theta: f64) -> f64 {
        let mut rng = rand::thread_rng();
        let proposal_std = 0.1;
        current_theta + rng.gen_range(-proposal_std..proposal_std)
    }
    
    fn calculate_acceptance_ratio(&self, current_theta: f64, proposal_theta: f64) -> f64 {
        let current_posterior = self.posterior_density(current_theta);
        let proposal_posterior = self.posterior_density(proposal_theta);
        
        (proposal_posterior / current_posterior).min(1.0)
    }
    
    fn posterior_density(&self, theta: f64) -> f64 {
        let prior_density = self.prior.pdf(theta);
        let likelihood_value = self.likelihood.calculate(&self.data, theta);
        
        prior_density * likelihood_value
    }
    
    pub fn credible_interval(&self, confidence_level: f64) -> (f64, f64) {
        let posterior = self.posterior_distribution();
        let mut samples = posterior.samples.clone();
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let alpha = 1.0 - confidence_level;
        let lower_index = ((alpha / 2.0) * samples.len() as f64) as usize;
        let upper_index = ((1.0 - alpha / 2.0) * samples.len() as f64) as usize;
        
        (samples[lower_index], samples[upper_index])
    }
}

pub trait LikelihoodFunction {
    fn calculate(&self, data: &[f64], theta: f64) -> f64;
}

pub struct NormalLikelihood {
    known_variance: f64,
}

impl LikelihoodFunction for NormalLikelihood {
    fn calculate(&self, data: &[f64], theta: f64) -> f64 {
        let n = data.len() as f64;
        let sample_mean = data.iter().sum::<f64>() / n;
        
        let exponent = -0.5 * n * (sample_mean - theta).powi(2) / self.known_variance;
        exponent.exp()
    }
}
```

### 4.2 贝叶斯网络

**定义 4.2.1 (贝叶斯网络)**
贝叶斯网络是有向无环图，表示变量间的条件依赖关系。

**算法 4.2.1 (贝叶斯网络算法)**

```rust
pub struct BayesianNetwork {
    nodes: Vec<BayesianNode>,
    edges: Vec<(usize, usize)>,
}

impl BayesianNetwork {
    pub fn new() -> Self {
        BayesianNetwork {
            nodes: Vec::new(),
            edges: Vec::new(),
        }
    }
    
    pub fn add_node(&mut self, node: BayesianNode) -> usize {
        let node_id = self.nodes.len();
        self.nodes.push(node);
        node_id
    }
    
    pub fn add_edge(&mut self, from: usize, to: usize) {
        self.edges.push((from, to));
    }
    
    pub fn infer(&self, evidence: &HashMap<usize, f64>) -> HashMap<usize, f64> {
        let mut probabilities = HashMap::new();
        
        for (i, node) in self.nodes.iter().enumerate() {
            if !evidence.contains_key(&i) {
                let probability = self.calculate_node_probability(i, evidence);
                probabilities.insert(i, probability);
            }
        }
        
        probabilities
    }
    
    fn calculate_node_probability(&self, node_id: usize, evidence: &HashMap<usize, f64>) -> f64 {
        let node = &self.nodes[node_id];
        let parents = self.get_parents(node_id);
        
        if parents.is_empty() {
            // 根节点
            node.prior_probability
        } else {
            // 有父节点的节点
            let mut conditional_prob = 0.0;
            
            // 计算条件概率
            for parent_config in self.generate_parent_configurations(&parents) {
                let parent_prob = self.calculate_parent_probability(&parent_config, evidence);
                let conditional_prob_given_parents = node.get_conditional_probability(&parent_config);
                conditional_prob += parent_prob * conditional_prob_given_parents;
            }
            
            conditional_prob
        }
    }
    
    fn get_parents(&self, node_id: usize) -> Vec<usize> {
        self.edges.iter()
            .filter(|(_, to)| *to == node_id)
            .map(|(from, _)| *from)
            .collect()
    }
    
    fn generate_parent_configurations(&self, parents: &[usize]) -> Vec<HashMap<usize, bool>> {
        let num_configs = 1 << parents.len();
        let mut configurations = Vec::new();
        
        for i in 0..num_configs {
            let mut config = HashMap::new();
            for (j, &parent) in parents.iter().enumerate() {
                config.insert(parent, (i >> j) & 1 == 1);
            }
            configurations.push(config);
        }
        
        configurations
    }
}

pub struct BayesianNode {
    name: String,
    prior_probability: f64,
    conditional_probabilities: HashMap<Vec<bool>, f64>,
}

impl BayesianNode {
    pub fn new(name: String, prior_probability: f64) -> Self {
        BayesianNode {
            name,
            prior_probability,
            conditional_probabilities: HashMap::new(),
        }
    }
    
    pub fn set_conditional_probability(&mut self, parent_values: Vec<bool>, probability: f64) {
        self.conditional_probabilities.insert(parent_values, probability);
    }
    
    pub fn get_conditional_probability(&self, parent_config: &HashMap<usize, bool>) -> f64 {
        let parent_values: Vec<bool> = parent_config.values().cloned().collect();
        *self.conditional_probabilities.get(&parent_values).unwrap_or(&0.5)
    }
}
```

## 5. 机器学习统计

### 5.1 回归分析

**定义 5.1.1 (线性回归)**
线性回归模型：$Y = X\beta + \epsilon$

**算法 5.1.1 (线性回归算法)**

```rust
pub struct LinearRegression {
    coefficients: Vec<f64>,
    intercept: f64,
    r_squared: f64,
}

impl LinearRegression {
    pub fn new() -> Self {
        LinearRegression {
            coefficients: Vec::new(),
            intercept: 0.0,
            r_squared: 0.0,
        }
    }
    
    pub fn fit(&mut self, x: &Matrix, y: &[f64]) {
        let n = x.rows() as f64;
        let p = x.cols() as f64;
        
        // 最小二乘估计
        let x_transpose = x.transpose();
        let x_t_x = &x_transpose * x;
        let x_t_y = x_transpose.multiply_vector(y);
        
        if let Some(x_t_x_inv) = x_t_x.inverse() {
            let beta = x_t_x_inv.multiply_vector(&x_t_y);
            
            self.intercept = beta[0];
            self.coefficients = beta[1..].to_vec();
            
            // 计算R²
            self.r_squared = self.calculate_r_squared(x, y);
        }
    }
    
    pub fn predict(&self, x: &Matrix) -> Vec<f64> {
        let mut predictions = Vec::new();
        
        for i in 0..x.rows() {
            let mut prediction = self.intercept;
            for j in 0..x.cols() {
                prediction += self.coefficients[j] * x[i][j];
            }
            predictions.push(prediction);
        }
        
        predictions
    }
    
    fn calculate_r_squared(&self, x: &Matrix, y: &[f64]) -> f64 {
        let predictions = self.predict(x);
        let y_mean = y.iter().sum::<f64>() / y.len() as f64;
        
        let ss_res: f64 = y.iter().zip(predictions.iter())
            .map(|(actual, predicted)| (actual - predicted).powi(2))
            .sum();
        
        let ss_tot: f64 = y.iter()
            .map(|&yi| (yi - y_mean).powi(2))
            .sum();
        
        1.0 - ss_res / ss_tot
    }
    
    pub fn confidence_intervals(&self, x: &Matrix, confidence_level: f64) -> Vec<(f64, f64)> {
        let predictions = self.predict(x);
        let n = x.rows() as f64;
        let p = x.cols() as f64;
        
        // 计算残差
        let residuals: Vec<f64> = x.iter().zip(predictions.iter())
            .map(|(_, &pred)| pred)
            .collect();
        
        let mse = residuals.iter().map(|&r| r.powi(2)).sum::<f64>() / (n - p - 1.0);
        let standard_error = mse.sqrt();
        
        let t_value = 1.96; // 95%置信水平
        
        predictions.iter()
            .map(|&pred| {
                let margin = t_value * standard_error;
                (pred - margin, pred + margin)
            })
            .collect()
    }
}
```

### 5.2 分类分析

**定义 5.2.1 (逻辑回归)**
逻辑回归模型：$P(Y=1|X) = \frac{1}{1 + e^{-X\beta}}$

**算法 5.2.1 (逻辑回归算法)**

```rust
pub struct LogisticRegression {
    coefficients: Vec<f64>,
    intercept: f64,
}

impl LogisticRegression {
    pub fn new() -> Self {
        LogisticRegression {
            coefficients: Vec::new(),
            intercept: 0.0,
        }
    }
    
    pub fn fit(&mut self, x: &Matrix, y: &[bool], max_iterations: usize) {
        let mut beta = vec![0.0; x.cols() + 1];
        let learning_rate = 0.01;
        
        for iteration in 0..max_iterations {
            let gradients = self.calculate_gradients(x, y, &beta);
            
            for i in 0..beta.len() {
                beta[i] -= learning_rate * gradients[i];
            }
            
            if iteration % 100 == 0 {
                let loss = self.calculate_loss(x, y, &beta);
                println!("Iteration {}, Loss: {}", iteration, loss);
            }
        }
        
        self.intercept = beta[0];
        self.coefficients = beta[1..].to_vec();
    }
    
    pub fn predict_proba(&self, x: &Matrix) -> Vec<f64> {
        let mut probabilities = Vec::new();
        
        for i in 0..x.rows() {
            let mut logit = self.intercept;
            for j in 0..x.cols() {
                logit += self.coefficients[j] * x[i][j];
            }
            let probability = 1.0 / (1.0 + (-logit).exp());
            probabilities.push(probability);
        }
        
        probabilities
    }
    
    pub fn predict(&self, x: &Matrix) -> Vec<bool> {
        self.predict_proba(x).iter().map(|&p| p > 0.5).collect()
    }
    
    fn calculate_gradients(&self, x: &Matrix, y: &[bool], beta: &[f64]) -> Vec<f64> {
        let mut gradients = vec![0.0; beta.len()];
        let n = x.rows() as f64;
        
        for i in 0..x.rows() {
            let mut logit = beta[0];
            for j in 0..x.cols() {
                logit += beta[j + 1] * x[i][j];
            }
            
            let probability = 1.0 / (1.0 + (-logit).exp());
            let error = if y[i] { 1.0 } else { 0.0 } - probability;
            
            gradients[0] += error / n;
            for j in 0..x.cols() {
                gradients[j + 1] += error * x[i][j] / n;
            }
        }
        
        gradients
    }
    
    fn calculate_loss(&self, x: &Matrix, y: &[bool], beta: &[f64]) -> f64 {
        let mut loss = 0.0;
        
        for i in 0..x.rows() {
            let mut logit = beta[0];
            for j in 0..x.cols() {
                logit += beta[j + 1] * x[i][j];
            }
            
            let probability = 1.0 / (1.0 + (-logit).exp());
            let actual = if y[i] { 1.0 } else { 0.0 };
            
            loss -= actual * probability.ln() + (1.0 - actual) * (1.0 - probability).ln();
        }
        
        loss
    }
}
```

## 6. 时间序列分析

### 6.1 ARIMA模型

**定义 6.1.1 (ARIMA模型)**
ARIMA(p,d,q)模型是自回归积分移动平均模型。

**算法 6.1.1 (ARIMA算法)**

```rust
pub struct ARIMAModel {
    p: usize, // AR阶数
    d: usize, // 差分阶数
    q: usize, // MA阶数
    ar_coefficients: Vec<f64>,
    ma_coefficients: Vec<f64>,
}

impl ARIMAModel {
    pub fn new(p: usize, d: usize, q: usize) -> Self {
        ARIMAModel {
            p,
            d,
            q,
            ar_coefficients: vec![0.0; p],
            ma_coefficients: vec![0.0; q],
        }
    }
    
    pub fn fit(&mut self, data: &[f64]) {
        let mut stationary_data = data.to_vec();
        
        // 差分
        for _ in 0..self.d {
            stationary_data = self.difference(&stationary_data);
        }
        
        // 估计AR和MA系数
        self.estimate_ar_coefficients(&stationary_data);
        self.estimate_ma_coefficients(&stationary_data);
    }
    
    pub fn forecast(&self, data: &[f64], steps: usize) -> Vec<f64> {
        let mut forecast = Vec::new();
        let mut history = data.to_vec();
        
        for _ in 0..steps {
            let prediction = self.predict_next(&history);
            forecast.push(prediction);
            history.push(prediction);
        }
        
        forecast
    }
    
    fn difference(&self, data: &[f64]) -> Vec<f64> {
        let mut differenced = Vec::new();
        
        for i in 1..data.len() {
            differenced.push(data[i] - data[i - 1]);
        }
        
        differenced
    }
    
    fn estimate_ar_coefficients(&mut self, data: &[f64]) {
        // 使用Yule-Walker方程估计AR系数
        let autocorrelations = self.calculate_autocorrelations(data, self.p);
        let toeplitz_matrix = self.build_toeplitz_matrix(&autocorrelations);
        let rhs = autocorrelations[1..=self.p].to_vec();
        
        if let Some(inverse) = toeplitz_matrix.inverse() {
            self.ar_coefficients = inverse.multiply_vector(&rhs);
        }
    }
    
    fn estimate_ma_coefficients(&mut self, data: &[f64]) {
        // 简化MA系数估计
        for i in 0..self.q {
            self.ma_coefficients[i] = 0.1; // 初始值
        }
    }
    
    fn calculate_autocorrelations(&self, data: &[f64], max_lag: usize) -> Vec<f64> {
        let mut autocorrelations = Vec::new();
        let mean = data.iter().sum::<f64>() / data.len() as f64;
        let variance = data.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / data.len() as f64;
        
        for lag in 0..=max_lag {
            let mut autocorr = 0.0;
            for i in lag..data.len() {
                autocorr += (data[i] - mean) * (data[i - lag] - mean);
            }
            autocorr /= (data.len() - lag) as f64;
            autocorrelations.push(autocorr / variance);
        }
        
        autocorrelations
    }
    
    fn build_toeplitz_matrix(&self, autocorrelations: &[f64]) -> Matrix {
        let mut matrix = Matrix::zeros(self.p, self.p);
        
        for i in 0..self.p {
            for j in 0..self.p {
                matrix[i][j] = autocorrelations[(i as i32 - j as i32).abs() as usize];
            }
        }
        
        matrix
    }
    
    fn predict_next(&self, history: &[f64]) -> f64 {
        let mut prediction = 0.0;
        
        // AR项
        for i in 0..self.p {
            if i < history.len() {
                prediction += self.ar_coefficients[i] * history[history.len() - 1 - i];
            }
        }
        
        // MA项（简化）
        for i in 0..self.q {
            prediction += self.ma_coefficients[i] * 0.1; // 假设残差为0.1
        }
        
        prediction
    }
}
```

## 7. 未来发展方向

### 7.1 理论发展方向

1. **高维统计**：研究高维数据的统计方法
2. **非参数统计**：发展非参数统计理论
3. **稳健统计**：研究稳健统计方法
4. **计算统计**：发展计算统计学

### 7.2 技术发展方向

1. **大数据统计**：处理大规模数据的统计方法
2. **在线学习**：发展在线统计学习
3. **分布式统计**：研究分布式统计计算
4. **统计软件**：开发统计计算软件

### 7.3 应用发展方向

1. **区块链统计**：区块链数据的统计分析
2. **DeFi统计**：DeFi协议的统计分析
3. **网络统计**：网络数据的统计分析
4. **智能合约统计**：智能合约的统计分析

## 总结

本文档建立了完整的Web3统计理论与概率论框架，包括：

1. **概率论基础**：建立了概率空间和随机变量理论
2. **统计推断**：提供了参数估计和假设检验方法
3. **随机过程**：构建了马尔可夫链和泊松过程模型
4. **贝叶斯理论**：建立了贝叶斯推断和贝叶斯网络
5. **机器学习统计**：提供了回归分析和分类分析方法
6. **时间序列分析**：建立了ARIMA模型
7. **发展方向**：指明了理论、技术、应用发展方向

这个理论框架为Web3系统的统计分析提供了科学基础，有助于构建更加可靠、高效的Web3系统。
