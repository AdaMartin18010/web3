# Web3 Analysis 目录命名规范化指南

## 目的

本指南旨在提供一套统一的命名规则，以规范化 Web3 Analysis 文档库中的目录和文件命名，提高资源组织的一致性和可导航性。

## 命名原则

1. **一致性**: 相同类型的资源应使用相同的命名风格
2. **描述性**: 名称应清晰描述内容
3. **层次性**: 名称应反映资源在知识体系中的层次
4. **简洁性**: 名称应尽可能简洁明了
5. **可扩展性**: 命名方式应考虑未来扩展

## 目录命名规范

### 1. 主目录命名

主目录应使用两位数字前缀，表示主题类别和优先级：

```
XX_主题名称/
```

示例:

- `01_Foundations/` - 基础理论
- `02_Consensus_Theory/` - 共识理论
- `03_Architecture/` - 架构设计

### 2. 子目录命名

子目录应使用两位数字前缀，表示子主题类别和优先级：

```
XX_子主题名称/
```

示例:

- `01_Set_Theory_and_Logic/` - 集合论与逻辑
- `02_Algebraic_Structures/` - 代数结构
- `03_Cryptographic_Mathematics/` - 密码学数学

### 3. 特殊目录命名

特殊用途的目录应使用特定前缀：

- `99_Recycle_Bin/` - 回收站
- `00_Meta/` - 元文档（关于文档库本身的文档）

## 当前子目录命名问题修复指南

### 1. 01_Foundations/ 目录

**当前存在问题**:

- 混合使用了有前缀和无前缀的子目录
- 存在重复的主题目录

**修复建议**:

将以下无前缀目录重命名:

- `Consensus_Theory/` → `05_Consensus_Theory/`
- `Mathematical/` → `06_Mathematics/`
- `Control_Theory/` → `07_Control_Theory/`
- `Cryptography/` → `08_Cryptography/`
- `Distributed_Systems/` → `09_Distributed_Systems/`
- `Type_Theory/` → `10_Type_Theory/`

**合并重复目录**:

- 合并 `01_Type_Theory/` 和 `10_Type_Theory/`
- 合并 `02_Mathematics/` 和 `06_Mathematics/`

### 2. 02_Consensus_Theory/ 目录

**修复建议**:

- 确保子目录使用数字前缀: `01_Consensus_Mechanisms/` → `01_Consensus_Mechanisms/`

### 3. 03_Architecture/ 目录

**当前存在问题**:

- 包含应归属于其他主目录的文件
- 子目录命名不一致

**修复建议**:

- 将共识相关文件移至 `02_Consensus_Theory/`:
  - `75_Advanced_Web3_Consensus_Theory_Deep_Dive_v3.md` → `02_Consensus_Theory/`
  - `66_Advanced_Web3_Consensus_Theory_Deep_Dive.md` → `02_Consensus_Theory/`
- 子目录添加数字前缀:
  - `06_Integration_Models/` → `01_Integration_Models/`

## 文件命名规范

### 1. 基础文档命名

基础文档应使用描述性名称，无需数字前缀：

```
主题_详细描述.md
```

示例:

- `README.md` - 目录说明文档
- `Consensus_Protocols.md` - 共识协议文档
- `System_Architecture.md` - 系统架构文档

### 2. 编号文档命名

研究论文和深入分析类文档应使用编号:

```
XX_主题_详细描述.md
```

示例:

- `01_Web3_Core_Theoretical_Framework.md`
- `02_Consensus_Theory_Formal_Analysis.md`

### 3. 高级研究文档命名

高级研究文档可添加描述性前缀:

```
Advanced_主题_详细描述.md
```

或带编号:

```
XX_Advanced_主题_详细描述.md
```

示例:

- `64_Advanced_Web3_Blockchain_Architecture_Theory.md`
- `Advanced_Proxy_Framework_Theory_Comprehensive_v2.md`

### 4. 版本标记

需要标记版本的文档使用以下格式:

```
主题_详细描述_vX.md
```

或:

```
XX_主题_详细描述_vX.md
```

示例:

- `Progress_Tracking_Comprehensive_v10.md`
- `75_Advanced_Web3_Consensus_Theory_Deep_Dive_v3.md`

## 规范化实施计划

### 第一阶段: 子目录规范化

1. 在每个主目录下创建临时工作文档
2. 按照规范重命名所有子目录
3. 确保子目录之间没有主题重叠

### 第二阶段: 文件迁移与重组

1. 将文件移动到正确的主题目录
2. 重命名不符合规范的文件
3. 合并重复或高度相似的文件

### 第三阶段: 索引更新

1. 更新所有README文件
2. 更新主索引文档
3. 验证所有链接和引用

## 命名转换表

为便于实施，提供以下命名转换参考表:

| 当前命名 | 规范化命名 | 类型 |
|----------|------------|------|
| `Control_Theory/` | `07_Control_Theory/` | 子目录 |
| `Type_Theory/` | `10_Type_Theory/` | 子目录 |
| `Advanced_Web3_Architecture_Theory.md` | `01_Advanced_Web3_Architecture_Theory.md` | 文件 |
| `Progress_tracking_v11.md` | `Progress_Tracking_v11.md` | 文件 |
| `01_01_Web3_Core_Theoretical_Framework.md` | `01_Web3_Core_Theoretical_Framework.md` | 文件 |

## 维护责任

1. 所有新增的目录和文件必须遵循本规范
2. 定期检查文档库结构，确保符合规范
3. 规范本身应随文档库演进进行更新

## 结论

统一的命名规范将显著提升Web3 Analysis文档库的可维护性和可用性。虽然初期规范化工作需要投入一定时间，但长期收益将超过这一投入，使文档库成为更加有价值的知识资源。
