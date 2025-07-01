# Web3理论形式化检查器

## 项目概述

Web3理论形式化检查器是一个自动化工具，用于检查Web3理论文档中的数学符号使用、定理证明格式和假设条件的规范性。该工具帮助研究人员和开发者确保理论文档的一致性、完整性和准确性。

## 功能特性

- **符号检查**: 验证数学符号的定义和使用是否符合规范
- **证明验证**: 检查定理证明的结构完整性和逻辑正确性
- **假设分析**: 验证假设条件的明确性和分类正确性
- **改进建议**: 提供具体的改进建议和修正方案

## 安装指南

### 前提条件

- Python 3.8+
- pip 包管理器

### 安装步骤

```bash
# 克隆仓库
git clone https://github.com/yourusername/web3-formalization-checker.git
cd web3-formalization-checker

# 创建虚拟环境
python -m venv venv
source venv/bin/activate  # Linux/Mac
# 或
venv\Scripts\activate  # Windows

# 安装依赖
pip install -r requirements.txt
```

## 使用方法

### 命令行使用

```bash
# 检查单个文档
python checker.py check --file document.md

# 检查整个目录
python checker.py check-dir --dir ./docs

# 生成详细报告
python checker.py check --file document.md --report detailed

# 自动修正
python checker.py check --file document.md --auto-fix
```

### 配置文件

在项目根目录创建 `.web3-checker.yml` 文件:

```yaml
rules:
  enable_all: true
  exclude_rules: ["SYM_003"]
  
output:
  format: "json"
  include_suggestions: true
  
severity:
  min_level: "WARNING"
```

## 项目结构

```
web3-formalization-checker/
├── checker.py               # 主程序入口
├── requirements.txt         # 项目依赖
├── .web3-checker.yml        # 默认配置文件
├── docs/                    # 文档
└── src/
    ├── __init__.py
    ├── parser/              # 解析器模块
    │   ├── __init__.py
    │   ├── markdown_parser.py
    │   └── latex_parser.py
    ├── rules/               # 规则引擎
    │   ├── __init__.py
    │   ├── symbol_rules.py
    │   ├── proof_rules.py
    │   └── assumption_rules.py
    ├── reporter/            # 报告生成器
    │   ├── __init__.py
    │   ├── json_reporter.py
    │   ├── markdown_reporter.py
    │   └── html_reporter.py
    └── utils/               # 工具函数
        ├── __init__.py
        └── helpers.py
```

## 开发指南

### 设置开发环境

```bash
# 安装开发依赖
pip install -r requirements-dev.txt

# 运行测试
pytest
```

### 添加新规则

1. 在 `src/rules/` 目录下创建规则文件
2. 实现 `Rule` 接口
3. 在规则注册表中注册新规则

示例:

```python
from src.rules.base import Rule

class NewSymbolRule(Rule):
    def __init__(self):
        self.id = "SYM_004"
        self.name = "新符号规则"
        self.severity = "WARNING"
    
    def check(self, document):
        # 实现检查逻辑
        issues = []
        # ...
        return issues
```

## API参考

### 主要类

- `DocumentParser`: 解析文档内容
- `RuleEngine`: 执行规则检查
- `Reporter`: 生成检查报告
- `Fixer`: 自动修正问题

### 关键方法

```python
# 解析文档
parser = DocumentParser()
document = parser.parse("document.md")

# 执行规则检查
engine = RuleEngine()
issues = engine.check(document)

# 生成报告
reporter = Reporter()
report = reporter.generate(issues)

# 自动修正
fixer = Fixer()
fixed_document = fixer.fix(document, issues)
```

## 贡献指南

1. Fork 仓库
2. 创建功能分支 (`git checkout -b feature/amazing-feature`)
3. 提交更改 (`git commit -m 'Add amazing feature'`)
4. 推送到分支 (`git push origin feature/amazing-feature`)
5. 创建 Pull Request

## 许可证

MIT License
