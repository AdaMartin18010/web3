# 形式化语言理论 (Formal Language Theory)

## 概述

形式化语言理论研究符号系统、语法规则和自动机，是Web3协议、智能合约语言和形式化验证的基础。

## 1. 形式语言与文法

**定义 1.1**（形式语言）：
符号表$\Sigma$上的字符串集合$L \subseteq \Sigma^*$。

**定义 1.2**（文法）：
四元组$G = (V, \Sigma, R, S)$，$V$为非终结符，$\Sigma$为终结符，$R$为产生式，$S$为开始符号。

- 正则文法、上下文无关文法、上下文相关文法

## 2. 自动机理论

- 有限自动机（DFA/NFA）
- 图灵机
- 语言的可判定性与复杂性

**定理 2.1**（正则语言与DFA等价）：
每个正则语言都可由DFA识别，反之亦然。

## 3. 应用场景

- 智能合约语言的语法与语义分析
- 区块链协议的状态机建模
- 形式化验证工具的底层理论

## 4. Rust代码示例

### 简单DFA实现

```rust
struct DFA {
    state: usize,
    transitions: Vec<Vec<usize>>,
    accept: Vec<bool>,
}

impl DFA {
    fn new(transitions: Vec<Vec<usize>>, accept: Vec<bool>) -> Self {
        DFA { state: 0, transitions, accept }
    }
    fn reset(&mut self) { self.state = 0; }
    fn step(&mut self, input: usize) { self.state = self.transitions[self.state][input]; }
    fn is_accept(&self) -> bool { self.accept[self.state] }
}

fn main() {
    // 识别偶数个1的二进制串
    let transitions = vec![vec![0, 1], vec![1, 0]];
    let accept = vec![true, false];
    let mut dfa = DFA::new(transitions, accept);
    for &bit in &[1, 0, 1, 1] {
        dfa.step(bit);
    }
    println!("接受状态: {}", dfa.is_accept());
}
```

## 相关链接

- [Web3形式化系统基础](01_Web3_Formal_System_Foundations.md)
- [类型理论](03_Type_Theory.md)
- [形式化验证](05_Formal_Verification.md)
- [形式化理论总览](../)

---

*形式化语言理论为Web3协议、智能合约和验证工具提供符号与自动机基础。*
