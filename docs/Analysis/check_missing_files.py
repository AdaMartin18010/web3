#!/usr/bin/env python3
"""
检查Web3理论分析文档库中的缺失文件
分析所有Markdown文件中的链接，找出指向但不存在的文件
"""

import os
import re
import glob
from pathlib import Path
from collections import defaultdict

class MissingFileChecker:
    def __init__(self, base_dir="docs/Analysis"):
        self.base_dir = Path(base_dir)
        self.missing_files = defaultdict(list)  # {missing_file: [referring_files]}
        # 更全面的链接模式匹配
        self.link_patterns = [
            re.compile(r'\[([^\]]*)\]\(([^)]*\.md)\)'),  # 标准链接
            re.compile(r'\[([^\]]*)\]\(([^)]*)/\)'),     # 目录链接
            re.compile(r'- \[([^\]]*)\]\(([^)]*\.md)\)'), # 列表中的链接
            re.compile(r'### \[([^\]]*)\]\(([^)]*\.md)\)'), # 标题链接
        ]
        
    def scan_all_files(self):
        """扫描所有Markdown文件，提取链接"""
        print("🔍 扫描所有Markdown文件...")
        
        for md_file in self.base_dir.rglob("*.md"):
            self.analyze_file(md_file)
            
    def analyze_file(self, file_path):
        """分析单个文件中的链接"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # 使用所有模式找出Markdown链接
            all_links = []
            for pattern in self.link_patterns:
                links = pattern.findall(content)
                all_links.extend(links)
            
            for link_text, link_path in all_links:
                # 跳过外部链接
                if link_path.startswith(('http://', 'https://', 'mailto:')):
                    continue
                    
                # 处理目录链接
                if link_path.endswith('/'):
                    link_path = link_path + 'README.md'
                    
                # 解析相对路径
                target_path = self.resolve_path(file_path, link_path)
                
                # 检查文件是否存在
                if not target_path.exists():
                    self.missing_files[str(target_path)].append(str(file_path))
                    
        except Exception as e:
            print(f"⚠️  读取文件错误 {file_path}: {e}")
            
    def resolve_path(self, current_file, link_path):
        """解析相对路径为绝对路径"""
        current_dir = current_file.parent
        
        # 处理相对路径
        if link_path.startswith('./'):
            link_path = link_path[2:]
        
        target_path = (current_dir / link_path).resolve()
        return target_path
        
    def categorize_missing_files(self):
        """按类型分类缺失文件"""
        categories = {
            'README文件': [],
            '理论文档': [],
            '基础文档': [],
            '应用文档': [],
            '其他': []
        }
        
        for missing_file in self.missing_files.keys():
            if 'README.md' in missing_file:
                categories['README文件'].append(missing_file)
            elif any(x in missing_file for x in ['Theory', 'Foundation', 'Mathematical', 'Cryptographic']):
                categories['理论文档'].append(missing_file)
            elif any(x in missing_file for x in ['01_', '02_', '03_', '04_', '05_']):
                categories['基础文档'].append(missing_file)
            elif any(x in missing_file for x in ['Application', 'DeFi', 'Industry']):
                categories['应用文档'].append(missing_file)
            else:
                categories['其他'].append(missing_file)
                
        return categories
        
    def generate_report(self):
        """生成缺失文件报告"""
        print("\n📊 缺失文件分析报告")
        print("=" * 60)
        
        if not self.missing_files:
            print("✅ 恭喜！没有发现缺失的文件。")
            return
            
        categories = self.categorize_missing_files()
        
        for category, files in categories.items():
            if files:
                print(f"\n## {category} ({len(files)}个)")
                print("-" * 40)
                for file in sorted(files):
                    print(f"📝 {file}")
                    referring_files = self.missing_files[file]
                    print(f"   被引用于: {len(referring_files)}个文件")
                    for ref_file in referring_files[:3]:  # 只显示前3个引用文件
                        print(f"     - {ref_file}")
                    if len(referring_files) > 3:
                        print(f"     - ... 还有{len(referring_files)-3}个文件")
                    print()
                    
        print(f"\n📈 总计: {len(self.missing_files)}个缺失文件")
        
    def generate_creation_plan(self):
        """生成文件创建计划"""
        print("\n🔧 文件创建计划")
        print("=" * 60)
        
        categories = self.categorize_missing_files()
        priority_order = ['README文件', '理论文档', '基础文档', '应用文档', '其他']
        
        for category in priority_order:
            files = categories.get(category, [])
            if files:
                print(f"\n### 第{priority_order.index(category)+1}优先级: {category}")
                for file in sorted(files):
                    print(f"- [ ] {file}")
                    
    def create_template_files(self, dry_run=True):
        """创建模板文件（可选择是否实际创建）"""
        print(f"\n{'🔍 预览' if dry_run else '📝 创建'}模板文件")
        print("=" * 60)
        
        for missing_file, referring_files in self.missing_files.items():
            file_path = Path(missing_file)
            
            if dry_run:
                print(f"将创建: {file_path}")
            else:
                # 确保目录存在
                file_path.parent.mkdir(parents=True, exist_ok=True)
                
                # 生成基础模板内容
                template_content = self.generate_template_content(file_path, referring_files)
                
                try:
                    with open(file_path, 'w', encoding='utf-8') as f:
                        f.write(template_content)
                    print(f"✅ 已创建: {file_path}")
                except Exception as e:
                    print(f"❌ 创建失败 {file_path}: {e}")
                    
    def generate_template_content(self, file_path, referring_files):
        """生成模板文件内容"""
        file_name = file_path.stem
        
        if 'README' in file_name:
            return self.generate_readme_template(file_path, referring_files)
        else:
            return self.generate_document_template(file_path, referring_files)
            
    def generate_readme_template(self, file_path, referring_files):
        """生成README模板"""
        dir_name = file_path.parent.name
        
        return f"""# {dir_name}

## 概述

本目录包含{dir_name}相关的理论文档和分析内容。

## 目录结构

```
{dir_name}/
├── README.md                    # 本文件
└── (待添加具体文档)
```

## 主要内容

### 核心理论

(待完善)

### 应用场景

(待完善)

## 参考文献

(待添加)

## 相关链接

被以下文档引用:
{chr(10).join(f'- [{ref}]({ref})' for ref in referring_files[:5])}

---

*本文档由Web3理论分析文档库自动生成*
"""

    def generate_document_template(self, file_path, referring_files):
        """生成普通文档模板"""
        file_name = file_path.stem.replace('_', ' ').title()
        
        return f"""# {file_name}

## 摘要

本文档探讨{file_name}相关的理论基础和应用分析。

## 目录

1. [理论基础](#理论基础)
2. [核心概念](#核心概念)
3. [数学模型](#数学模型)
4. [应用场景](#应用场景)
5. [实现挑战](#实现挑战)
6. [未来发展](#未来发展)

## 理论基础

### 基本定义

**定义 1.1** ({file_name}基础定义)

(待完善)

### 核心原理

(待完善)

## 核心概念

### 概念框架

(待完善)

### 关键特性

(待完善)

## 数学模型

### 形式化描述

(待完善)

$$
\\text{{待添加数学公式}}
$$

## 应用场景

### Web3应用

(待完善)

### 实际案例

(待完善)

## 实现挑战

### 技术挑战

(待完善)

### 理论挑战

(待完善)

## 未来发展

### 研究方向

(待完善)

### 发展趋势

(待完善)

## 参考文献

(待添加)

## 相关文档

本文档被以下文档引用:
{chr(10).join(f'- [{ref}]({ref})' for ref in referring_files[:5])}

---

*本文档是Web3理论分析文档库的一部分*
"""

def main():
    print("🚀 Web3理论分析文档库 - 缺失文件检查器")
    print("=" * 60)
    
    checker = MissingFileChecker()
    
    # 扫描所有文件
    checker.scan_all_files()
    
    # 生成报告
    checker.generate_report()
    
    # 生成创建计划
    checker.generate_creation_plan()
    
    # 预览将要创建的文件
    checker.create_template_files(dry_run=True)
    
    # 询问是否实际创建文件
    print("\n❓ 是否要创建这些模板文件？")
    print("1. 是 - 创建所有缺失文件的模板")
    print("2. 否 - 仅显示报告")
    
    # 暂时设为False，避免自动创建
    create_files = False
    
    if create_files:
        print("\n🚀 开始创建模板文件...")
        checker.create_template_files(dry_run=False)
        print("\n✅ 模板文件创建完成！")
    else:
        print("\n📋 报告生成完成。请手动创建需要的文件。")

if __name__ == "__main__":
    main() 