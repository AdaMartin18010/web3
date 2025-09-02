#!/usr/bin/env python3
"""
Web3文档质量验证工具
自动检查文档的数学内容、代码实现和安全性分析
"""

import os
import re
import json
import hashlib
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from datetime import datetime
import argparse

@dataclass
class ValidationResult:
    """验证结果数据结构"""
    file_path: str
    mathematical_content: bool
    code_implementation: bool
    security_analysis: bool
    academic_format: bool
    total_score: int
    issues: List[str]
    recommendations: List[str]

class DocumentValidator:
    """文档质量验证器"""
    
    def __init__(self, base_dir: str):
        self.base_dir = Path(base_dir)
        self.results: List[ValidationResult] = []
        
        # 数学内容检测模式
        self.math_patterns = {
            'latex_formula': r'\\\w+{.*?}|\\[a-zA-Z]+|\\[a-zA-Z]+\{.*?\}',
            'math_definition': r'\\begin\{definition\}|\\begin\{theorem\}|\\begin\{proof\}',
            'math_symbols': r'\$.*?\$|\$\$.*?\$\$',
            'mathematical_notation': r'\\mathbb\{[A-Z]\}|\\mathcal\{[A-Z]\}|\\mathfrak\{[A-Z]\}'
        }
        
        # 代码实现检测模式
        self.code_patterns = {
            'rust_code': r'```rust\s*\n.*?\n```',
            'typescript_code': r'```typescript\s*\n.*?\n```',
            'python_code': r'```python\s*\n.*?\n```',
            'solidity_code': r'```solidity\s*\n.*?\n```',
            'pseudocode': r'```pseudocode\s*\n.*?\n```'
        }
        
        # 安全性分析检测模式
        self.security_patterns = {
            'threat_model': r'威胁模型|threat model|攻击向量|attack vector',
            'security_analysis': r'安全性分析|security analysis|安全证明|security proof',
            'vulnerability': r'漏洞|vulnerability|攻击|attack|防护|protection',
            'risk_assessment': r'风险评估|risk assessment|威胁评估|threat assessment'
        }
        
        # 学术格式检测模式
        self.academic_patterns = {
            'abstract': r'## 📝 摘要|## 摘要|## Abstract',
            'introduction': r'## 1\. 引言|## 1\. Introduction|## 1\. 理论基础',
            'conclusion': r'## 结论|## Conclusion|## 6\. 结论与展望',
            'references': r'## 参考文献|## References|## 7\. 参考文献',
            'mathematical_content': r'## .*数学|## .*理论|## .*算法'
        }
    
    def validate_mathematical_content(self, content: str) -> Tuple[bool, List[str]]:
        """验证文档是否包含数学内容"""
        issues = []
        score = 0
        max_score = 40
        
        # 检查LaTeX公式
        latex_count = len(re.findall(self.math_patterns['latex_formula'], content, re.DOTALL))
        if latex_count >= 5:
            score += 10
        elif latex_count >= 2:
            score += 5
        else:
            issues.append("缺少LaTeX数学公式")
        
        # 检查数学定义和定理
        definition_count = len(re.findall(self.math_patterns['math_definition'], content, re.DOTALL))
        if definition_count >= 3:
            score += 10
        elif definition_count >= 1:
            score += 5
        else:
            issues.append("缺少数学定义和定理")
        
        # 检查数学符号
        symbol_count = len(re.findall(self.math_patterns['math_symbols'], content, re.DOTALL))
        if symbol_count >= 10:
            score += 10
        elif symbol_count >= 5:
            score += 5
        else:
            issues.append("缺少数学符号表示")
        
        # 检查数学记号
        notation_count = len(re.findall(self.math_patterns['mathematical_notation'], content, re.DOTALL))
        if notation_count >= 3:
            score += 10
        elif notation_count >= 1:
            score += 5
        else:
            issues.append("缺少数学记号")
        
        return score >= 20, issues
    
    def validate_code_implementation(self, content: str) -> Tuple[bool, List[str]]:
        """验证文档是否包含代码实现"""
        issues = []
        score = 0
        max_score = 30
        
        # 检查Rust代码
        rust_code = re.findall(self.code_patterns['rust_code'], content, re.DOTALL)
        if rust_code:
            score += 10
            # 检查代码质量
            for code in rust_code:
                if 'pub fn' in code or 'impl' in code:
                    score += 5
                    break
        else:
            issues.append("缺少Rust代码实现")
        
        # 检查TypeScript代码
        ts_code = re.findall(self.code_patterns['typescript_code'], content, re.DOTALL)
        if ts_code:
            score += 5
        else:
            issues.append("缺少TypeScript代码实现")
        
        # 检查伪代码
        pseudo_code = re.findall(self.code_patterns['pseudocode'], content, re.DOTALL)
        if pseudo_code:
            score += 5
        else:
            issues.append("缺少算法伪代码")
        
        # 检查代码注释和文档
        if '///' in content or '//!' in content or '/*' in content:
            score += 5
        else:
            issues.append("代码缺少注释和文档")
        
        return score >= 15, issues
    
    def validate_security_analysis(self, content: str) -> Tuple[bool, List[str]]:
        """验证文档是否包含安全分析"""
        issues = []
        score = 0
        max_score = 20
        
        # 检查威胁模型
        if re.search(self.security_patterns['threat_model'], content, re.IGNORECASE):
            score += 5
        else:
            issues.append("缺少威胁模型")
        
        # 检查安全性分析
        if re.search(self.security_patterns['security_analysis'], content, re.IGNORECASE):
            score += 5
        else:
            issues.append("缺少安全性分析")
        
        # 检查漏洞分析
        if re.search(self.security_patterns['vulnerability'], content, re.IGNORECASE):
            score += 5
        else:
            issues.append("缺少漏洞分析")
        
        # 检查风险评估
        if re.search(self.security_patterns['risk_assessment'], content, re.IGNORECASE):
            score += 5
        else:
            issues.append("缺少风险评估")
        
        return score >= 10, issues
    
    def validate_academic_format(self, content: str) -> Tuple[bool, List[str]]:
        """验证文档是否符合学术格式"""
        issues = []
        score = 0
        max_score = 10
        
        # 检查摘要
        if re.search(self.academic_patterns['abstract'], content, re.IGNORECASE):
            score += 2
        else:
            issues.append("缺少摘要部分")
        
        # 检查引言
        if re.search(self.academic_patterns['introduction'], content, re.IGNORECASE):
            score += 2
        else:
            issues.append("缺少引言部分")
        
        # 检查结论
        if re.search(self.academic_patterns['conclusion'], content, re.IGNORECASE):
            score += 2
        else:
            issues.append("缺少结论部分")
        
        # 检查参考文献
        if re.search(self.academic_patterns['references'], content, re.IGNORECASE):
            score += 2
        else:
            issues.append("缺少参考文献")
        
        # 检查数学内容结构
        if re.search(self.academic_patterns['mathematical_content'], content, re.IGNORECASE):
            score += 2
        else:
            issues.append("缺少数学内容结构")
        
        return score >= 5, issues
    
    def generate_recommendations(self, issues: List[str]) -> List[str]:
        """根据问题生成改进建议"""
        recommendations = []
        
        for issue in issues:
            if "缺少LaTeX数学公式" in issue:
                recommendations.append("添加LaTeX数学公式，使用\\begin{equation}环境")
            elif "缺少数学定义和定理" in issue:
                recommendations.append("添加数学定义和定理，使用\\begin{definition}和\\begin{theorem}环境")
            elif "缺少Rust代码实现" in issue:
                recommendations.append("添加Rust代码实现，包含完整的结构定义和方法实现")
            elif "缺少威胁模型" in issue:
                recommendations.append("添加威胁模型，明确攻击者能力和攻击目标")
            elif "缺少安全性分析" in issue:
                recommendations.append("添加安全性分析，包括攻击向量和防护措施")
            elif "缺少摘要部分" in issue:
                recommendations.append("添加摘要部分，简要说明研究内容和贡献")
            elif "缺少参考文献" in issue:
                recommendations.append("添加参考文献，遵循学术引用规范")
        
        return recommendations
    
    def validate_file(self, file_path: Path) -> ValidationResult:
        """验证单个文件"""
        try:
            content = file_path.read_text(encoding='utf-8')
        except UnicodeDecodeError:
            try:
                content = file_path.read_text(encoding='gbk')
            except:
                content = ""
        
        # 执行各项验证
        math_valid, math_issues = self.validate_mathematical_content(content)
        code_valid, code_issues = self.validate_code_implementation(content)
        security_valid, security_issues = self.validate_security_analysis(content)
        academic_valid, academic_issues = self.validate_academic_format(content)
        
        # 合并所有问题
        all_issues = math_issues + code_issues + security_issues + academic_issues
        
        # 计算总分
        total_score = 0
        if math_valid:
            total_score += 40
        if code_valid:
            total_score += 30
        if security_valid:
            total_score += 20
        if academic_valid:
            total_score += 10
        
        # 生成改进建议
        recommendations = self.generate_recommendations(all_issues)
        
        return ValidationResult(
            file_path=str(file_path),
            mathematical_content=math_valid,
            code_implementation=code_valid,
            security_analysis=security_valid,
            academic_format=academic_valid,
            total_score=total_score,
            issues=all_issues,
            recommendations=recommendations
        )
    
    def validate_directory(self) -> Dict:
        """验证整个目录"""
        print(f"开始验证目录: {self.base_dir}")
        
        markdown_files = list(self.base_dir.rglob('*.md'))
        print(f"找到 {len(markdown_files)} 个Markdown文件")
        
        for file_path in markdown_files:
            if file_path.name.startswith('.'):
                continue
            
            print(f"验证文件: {file_path.name}")
            result = self.validate_file(file_path)
            self.results.append(result)
        
        return self.generate_summary()
    
    def generate_summary(self) -> Dict:
        """生成验证摘要"""
        total_files = len(self.results)
        if total_files == 0:
            return {"error": "没有找到可验证的文件"}
        
        # 统计各项指标
        math_count = sum(1 for r in self.results if r.mathematical_content)
        code_count = sum(1 for r in self.results if r.code_implementation)
        security_count = sum(1 for r in self.results if r.security_analysis)
        academic_count = sum(1 for r in self.results if r.academic_format)
        
        # 计算平均分
        avg_score = sum(r.total_score for r in self.results) / total_files
        
        # 质量分布
        excellent = sum(1 for r in self.results if r.total_score >= 90)
        good = sum(1 for r in self.results if 80 <= r.total_score < 90)
        fair = sum(1 for r in self.results if 70 <= r.total_score < 80)
        poor = sum(1 for r in self.results if r.total_score < 70)
        
        summary = {
            "validation_date": datetime.now().isoformat(),
            "total_files": total_files,
            "quality_distribution": {
                "excellent": excellent,
                "good": good,
                "fair": fair,
                "poor": poor
            },
            "component_scores": {
                "mathematical_content": f"{math_count}/{total_files} ({math_count/total_files*100:.1f}%)",
                "code_implementation": f"{code_count}/{total_files} ({code_count/total_files*100:.1f}%)",
                "security_analysis": f"{security_count}/{total_files} ({security_count/total_files*100:.1f}%)",
                "academic_format": f"{academic_count}/{total_files} ({academic_count/total_files*100:.1f}%)"
            },
            "average_score": round(avg_score, 1),
            "files_need_improvement": [r.file_path for r in self.results if r.total_score < 70],
            "top_files": sorted(self.results, key=lambda x: x.total_score, reverse=True)[:5]
        }
        
        return summary
    
    def save_results(self, output_file: str):
        """保存验证结果"""
        summary = self.generate_summary()
        
        # 准备详细结果
        detailed_results = []
        for result in self.results:
            detailed_results.append({
                "file_path": result.file_path,
                "mathematical_content": result.mathematical_content,
                "code_implementation": result.code_implementation,
                "security_analysis": result.security_analysis,
                "academic_format": result.academic_format,
                "total_score": result.total_score,
                "issues": result.issues,
                "recommendations": result.recommendations
            })
        
        output_data = {
            "summary": summary,
            "detailed_results": detailed_results
        }
        
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(output_data, f, ensure_ascii=False, indent=2)
        
        print(f"验证结果已保存到: {output_file}")
    
    def print_summary(self):
        """打印验证摘要"""
        summary = self.generate_summary()
        
        print("\n" + "="*60)
        print("Web3文档质量验证报告")
        print("="*60)
        print(f"验证时间: {summary['validation_date']}")
        print(f"总文件数: {summary['total_files']}")
        print(f"平均质量分数: {summary['average_score']}/100")
        
        print("\n质量分布:")
        dist = summary['quality_distribution']
        print(f"  优秀 (90-100分): {dist['excellent']} 个文件")
        print(f"  良好 (80-89分): {dist['good']} 个文件")
        print(f"  合格 (70-79分): {dist['fair']} 个文件")
        print(f"  不合格 (<70分): {dist['poor']} 个文件")
        
        print("\n组件得分:")
        for component, score in summary['component_scores'].items():
            print(f"  {component}: {score}")
        
        if summary['files_need_improvement']:
            print(f"\n需要改进的文件 ({len(summary['files_need_improvement'])} 个):")
            for file_path in summary['files_need_improvement'][:10]:  # 只显示前10个
                print(f"  - {file_path}")
        
        print("\n质量最高的文件:")
        for i, result in enumerate(summary['top_files'], 1):
            print(f"  {i}. {Path(result.file_path).name} ({result.total_score}/100)")

def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='Web3文档质量验证工具')
    parser.add_argument('directory', help='要验证的目录路径')
    parser.add_argument('-o', '--output', default='validation_results.json', help='输出文件路径')
    parser.add_argument('--verbose', action='store_true', help='显示详细输出')
    
    args = parser.parse_args()
    
    if not os.path.exists(args.directory):
        print(f"错误: 目录不存在: {args.directory}")
        return
    
    validator = DocumentValidator(args.directory)
    validator.validate_directory()
    validator.save_results(args.output)
    validator.print_summary()

if __name__ == "__main__":
    main()
