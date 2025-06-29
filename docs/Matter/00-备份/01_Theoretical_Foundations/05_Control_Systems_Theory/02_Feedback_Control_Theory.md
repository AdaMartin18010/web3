# 反馈控制理论 (Feedback Control Theory)

## 概述

反馈控制理论是控制系统的核心，通过测量输出并调整输入来实现系统稳定性和性能优化。

## 1. 基本定义

**定义 1.1**（反馈控制）：
利用系统输出信息调整控制输入的控制策略。

**定义 1.2**（闭环系统）：
包含反馈环节的控制系统，输出影响输入。

**定义 1.3**（开环系统）：
无反馈的控制系统，输入独立于输出。

## 2. 稳定性理论

### 2.1 李雅普诺夫稳定性

**定理 2.1**（李雅普诺夫稳定性）：
若存在正定函数$V(x)$使得$\dot{V}(x) < 0$，则系统在平衡点稳定。

### 2.2 奈奎斯特稳定性判据

**定理 2.2**（奈奎斯特判据）：
闭环系统稳定的充要条件是奈奎斯特图包围点$(-1,0)$的次数等于开环系统右半平面极点数。

## 3. 应用场景

- 区块链网络流量控制
- 智能合约执行速率调节
- 分布式系统负载均衡

## 4. Rust代码示例

### 反馈控制系统仿真

```rust
use std::f64::consts::PI;

struct FeedbackSystem {
    controller: PIDController,
    plant_gain: f64,
    plant_time_constant: f64,
    output: f64,
    output_rate: f64,
}

impl FeedbackSystem {
    fn new(controller: PIDController, plant_gain: f64, plant_time_constant: f64) -> Self {
        FeedbackSystem {
            controller,
            plant_gain,
            plant_time_constant,
            output: 0.0,
            output_rate: 0.0,
        }
    }
    
    fn step(&mut self, dt: f64) {
        let control_signal = self.controller.update(self.output, dt);
        
        // 一阶系统动态
        let input_to_plant = control_signal * self.plant_gain;
        self.output_rate = (input_to_plant - self.output) / self.plant_time_constant;
        self.output += self.output_rate * dt;
    }
    
    fn get_output(&self) -> f64 {
        self.output
    }
}

fn main() {
    let controller = PIDController::new(2.0, 0.5, 0.1, 1.0);
    let mut system = FeedbackSystem::new(controller, 1.0, 0.5);
    let dt = 0.01;
    
    for i in 0..1000 {
        system.step(dt);
        if i % 100 == 0 {
            println!("时间: {:.2}, 输出: {:.4}", i as f64 * dt, system.get_output());
        }
    }
}
```

## 相关链接

- [控制系统理论基础](README.md)
- [控制系统基础](01_Control_Systems_Foundations.md)
- [自适应控制](03_Adaptive_Control.md)
- [鲁棒控制理论](04_Robust_Control_Theory.md)
- [控制系统理论总览](../)

---

*反馈控制理论为Web3系统提供稳定性和性能优化的核心控制方法。*
