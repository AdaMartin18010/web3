# 控制论 (Control Theory)

## 1. 控制系统基础

### 1.1 系统定义

**定义 1.1 (动态系统)**
动态系统是一个五元组 $\Sigma = (X, U, Y, f, h)$，其中：

- $X \subseteq \mathbb{R}^n$ 是状态空间
- $U \subseteq \mathbb{R}^m$ 是输入空间
- $Y \subseteq \mathbb{R}^p$ 是输出空间
- $f : X \times U \rightarrow X$ 是状态转移函数
- $h : X \rightarrow Y$ 是输出函数

**定义 1.2 (连续时间系统)**
连续时间系统的状态方程：
$$\dot{x}(t) = f(x(t), u(t))$$
$$y(t) = h(x(t))$$

**定义 1.3 (离散时间系统)**
离散时间系统的状态方程：
$$x(k+1) = f(x(k), u(k))$$
$$y(k) = h(x(k))$$

### 1.2 线性系统

**定义 1.4 (线性系统)**
线性系统满足叠加原理：
$$f(\alpha x_1 + \beta x_2, \alpha u_1 + \beta u_2) = \alpha f(x_1, u_1) + \beta f(x_2, u_2)$$

**定义 1.5 (线性时不变系统)**
线性时不变系统的状态空间表示：
$$\dot{x}(t) = Ax(t) + Bu(t)$$
$$y(t) = Cx(t) + Du(t)$$

其中 $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$, $C \in \mathbb{R}^{p \times n}$, $D \in \mathbb{R}^{p \times m}$。

**定理 1.1 (线性系统解)**
线性时不变系统的解为：
$$x(t) = e^{At}x(0) + \int_0^t e^{A(t-\tau)}Bu(\tau)d\tau$$

**证明：** 通过状态方程的积分：

1. 齐次方程 $\dot{x} = Ax$ 的解为 $x(t) = e^{At}x(0)$
2. 非齐次方程通过变分常数法求解
3. 利用卷积积分得到完整解

## 2. 稳定性分析

### 2.1 李雅普诺夫稳定性

**定义 2.1 (平衡点)**
状态 $x_e \in X$ 是平衡点，如果 $f(x_e, 0) = 0$。

**定义 2.2 (李雅普诺夫稳定性)**
平衡点 $x_e$ 是李雅普诺夫稳定的，如果对于任意 $\epsilon > 0$，存在 $\delta > 0$ 使得：
$$\|x(0) - x_e\| < \delta \Rightarrow \|x(t) - x_e\| < \epsilon \text{ for all } t \geq 0$$

**定义 2.3 (渐近稳定性)**
平衡点 $x_e$ 是渐近稳定的，如果它是李雅普诺夫稳定的且：
$$\lim_{t \rightarrow \infty} x(t) = x_e$$

**定理 2.1 (李雅普诺夫直接法)**
如果存在连续可微函数 $V : X \rightarrow \mathbb{R}$ 满足：

1. $V(x_e) = 0$
2. $V(x) > 0$ 对于 $x \neq x_e$
3. $\dot{V}(x) \leq 0$ 对于 $x \neq x_e$

则平衡点 $x_e$ 是李雅普诺夫稳定的。

**证明：** 通过李雅普诺夫函数的单调性：

1. $V(x)$ 在平衡点附近有下界
2. $\dot{V}(x) \leq 0$ 确保 $V(x)$ 不增加
3. 因此状态轨迹保持在平衡点附近

### 2.2 线性系统稳定性

**定理 2.2 (线性系统稳定性)**
线性系统 $\dot{x} = Ax$ 的零平衡点是渐近稳定的当且仅当 $A$ 的所有特征值都有负实部。

**证明：** 通过特征值分解：

1. $A$ 的特征值决定系统动态
2. 负实部特征值对应衰减模态
3. 正实部特征值对应增长模态

**定义 2.4 (赫尔维茨判据)**
多项式 $p(s) = a_n s^n + a_{n-1} s^{n-1} + \cdots + a_0$ 是赫尔维茨的，如果所有根都有负实部。

-**算法 2.1 (赫尔维茨判据)**

```haskell
hurwitzCriterion :: [Double] -> Bool
hurwitzCriterion coeffs = 
  let n = length coeffs - 1
      hurwitzMatrix = buildHurwitzMatrix coeffs
      minors = [determinant (submatrix hurwitzMatrix i) | i <- [1..n]]
  in all (> 0) minors
```

## 3. 可控性和可观性

### 3.1 可控性

**定义 3.1 (可控性)**
系统 $\Sigma$ 在时间 $T$ 内可控，如果对于任意初始状态 $x_0$ 和目标状态 $x_f$，存在输入 $u(t)$ 使得 $x(T) = x_f$。

**定义 3.2 (可控性矩阵)**
线性系统的可控性矩阵：
$$\mathcal{C} = [B \quad AB \quad A^2B \quad \cdots \quad A^{n-1}B]$$

**定理 3.1 (可控性判据)**
线性系统完全可控当且仅当可控性矩阵 $\mathcal{C}$ 满秩。

**证明：** 通过凯莱-哈密顿定理：

1. 可控性矩阵的列空间包含可达状态空间
2. 满秩确保可达整个状态空间
3. 凯莱-哈密顿定理限制矩阵幂的线性相关性

### 3.2 可观性

**定义 3.3 (可观性)**
系统 $\Sigma$ 可观，如果任意初始状态 $x_0$ 都可以通过输出 $y(t)$ 唯一确定。

**定义 3.4 (可观性矩阵)**
线性系统的可观性矩阵：
$$\mathcal{O} = \begin{bmatrix} C \\ CA \\ CA^2 \\ \vdots \\ CA^{n-1} \end{bmatrix}$$

**定理 3.2 (可观性判据)**
线性系统完全可观当且仅当可观性矩阵 $\mathcal{O}$ 满秩。

**证明：** 通过输出方程：

1. 可观性矩阵的行空间包含可观测状态空间
2. 满秩确保状态唯一确定
3. 输出序列包含足够信息重构状态

## 4. 反馈控制

### 4.1 状态反馈

**定义 4.1 (状态反馈)**
状态反馈控制律：
$$u(t) = -Kx(t) + r(t)$$

其中 $K \in \mathbb{R}^{m \times n}$ 是反馈增益矩阵，$r(t)$ 是参考输入。

**定理 4.1 (极点配置)**
如果系统 $(A, B)$ 可控，则可以通过状态反馈任意配置闭环极点。

**证明：** 通过可控性标准形：

1. 可控系统可以变换为标准形
2. 标准形下极点配置直接可得
3. 变换回原坐标系得到反馈增益

-**算法 4.1 (极点配置)**

```haskell
polePlacement :: Matrix -> Matrix -> [Complex Double] -> Matrix
polePlacement a b desiredPoles = 
  let controllableForm = toControllableForm a b
      kStandard = placePoles controllableForm desiredPoles
      transformation = getTransformation a b
  in kStandard * transformation
```

### 4.2 输出反馈

**定义 4.2 (输出反馈)**
输出反馈控制律：
$$u(t) = -Ky(t) + r(t)$$

**定理 4.2 (输出反馈限制)**
输出反馈不能任意配置极点，只能配置可观部分的极点。

**证明：** 通过可观性分解：

1. 系统可以分解为可观和不可观部分
2. 输出反馈只能影响可观部分
3. 不可观部分的极点无法通过输出反馈改变

### 4.3 观测器设计

**定义 4.3 (全维观测器)**
全维观测器：
$$\dot{\hat{x}}(t) = A\hat{x}(t) + Bu(t) + L(y(t) - C\hat{x}(t))$$

其中 $L \in \mathbb{R}^{n \times p}$ 是观测器增益矩阵。

**定理 4.3 (观测器极点配置)**
如果系统 $(A, C)$ 可观，则可以通过选择 $L$ 任意配置观测器极点。

**证明：** 通过可观性对偶性：

1. $(A, C)$ 可观等价于 $(A^T, C^T)$ 可控
2. 观测器设计转化为状态反馈设计
3. 对偶系统极点配置得到观测器增益

## 5. 最优控制

### 5.1 线性二次型调节器

**定义 5.1 (LQR问题)**
线性二次型调节器问题：
$$\min_{u(t)} \int_0^\infty (x^T(t)Qx(t) + u^T(t)Ru(t))dt$$

其中 $Q \geq 0$, $R > 0$ 是权重矩阵。

**定理 5.1 (LQR解)**
LQR问题的最优控制律为：
$$u^*(t) = -R^{-1}B^TPx(t)$$

其中 $P$ 是代数黎卡提方程的解：
$$A^TP + PA - PBR^{-1}B^TP + Q = 0$$

**证明：** 通过变分法：

1. 构造哈密顿函数
2. 应用最优性条件
3. 求解黎卡提方程得到最优解

### 5.2 卡尔曼滤波器

**定义 5.2 (卡尔曼滤波器)**
考虑噪声的系统：
$$\dot{x}(t) = Ax(t) + Bu(t) + w(t)$$
$$y(t) = Cx(t) + v(t)$$

其中 $w(t) \sim \mathcal{N}(0, Q)$, $v(t) \sim \mathcal{N}(0, R)$。

**定理 5.2 (卡尔曼滤波器)**
最优状态估计由卡尔曼滤波器给出：
$$\dot{\hat{x}}(t) = A\hat{x}(t) + Bu(t) + K(t)(y(t) - C\hat{x}(t))$$

其中卡尔曼增益：
$$K(t) = P(t)C^TR^{-1}$$

**证明：** 通过最小方差估计：

1. 状态估计误差协方差最小化
2. 求解黎卡提微分方程
3. 得到最优卡尔曼增益

## 6. 鲁棒控制

### 6.1 H∞控制

**定义 6.1 (H∞范数)**
传递函数 $G(s)$ 的H∞范数：
$$\|G\|_\infty = \sup_{\omega \in \mathbb{R}} \sigma_{\max}(G(j\omega))$$

**定义 6.2 (H∞控制问题)**
H∞控制问题：
$$\min_{K} \|T_{zw}\|_\infty < \gamma$$

其中 $T_{zw}$ 是从干扰 $w$ 到性能输出 $z$ 的闭环传递函数。

**定理 6.1 (H∞控制解)**
H∞控制问题可以通过求解两个代数黎卡提方程得到。

### 6.2 μ综合

**定义 6.3 (结构奇异值)**
结构奇异值：
$$\mu_\Delta(M) = \frac{1}{\min\{\bar{\sigma}(\Delta) \mid \Delta \in \Delta, \det(I - M\Delta) = 0\}}$$

**定理 6.2 (μ综合)**
μ综合提供处理结构不确定性的鲁棒控制方法。

## 7. 自适应控制

### 7.1 模型参考自适应控制

**定义 7.1 (参考模型)**
参考模型：
$$\dot{x}_m(t) = A_mx_m(t) + B_mr(t)$$

**定义 7.2 (自适应控制律)**
自适应控制律：
$$u(t) = \hat{\theta}^T(t)\phi(x(t), r(t))$$

其中 $\hat{\theta}(t)$ 是参数估计，$\phi$ 是回归向量。

**定理 7.1 (自适应稳定性)**
在适当条件下，自适应控制系统是稳定的。

## 8. 结论

控制论为动态系统分析和设计提供了完整的理论框架：

1. **系统建模**：精确描述动态系统行为
2. **稳定性分析**：确保系统稳定运行
3. **控制设计**：实现期望的系统性能
4. **鲁棒性**：处理系统不确定性和干扰

控制论在工程、经济、生物等领域发挥着关键作用。通过形式化的控制理论，我们可以：

- 设计高性能控制系统
- 分析系统稳定性和性能
- 处理不确定性和干扰
- 优化系统运行效率
