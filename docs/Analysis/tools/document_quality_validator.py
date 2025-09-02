#!/usr/bin/env python3
"""
文档质量验证工具
用于自动检查Analysis文件夹中文档的质量，包括数学内容、代码实现和安全分析
"""

import os
import re
import json
import argparse
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from datetime import datetime

@dataclass
class QualityMetrics:
    """文档质量指标"""
    has_mathematical_content: bool = False
    has_code_implementation: bool = False
    has_security_analysis: bool = False
    has_references: bool = False
    has_theorems: bool = False
    has_definitions: bool = False
    has_proofs: bool = False
    latex_formula_count: int = 0
    code_block_count: int = 0
    security_keyword_count: int = 0
    total_lines: int = 0
    quality_score: float = 0.0

class DocumentQualityValidator:
    """文档质量验证器"""
    
    def __init__(self, base_dir: str):
        self.base_dir = Path(base_dir)
        self.security_keywords = [
            'threat', 'attack', 'vulnerability', 'security', 'risk',
            '威胁', '攻击', '漏洞', '安全', '风险',
            'protection', 'defense', 'mitigation', '防护', '防御'
        ]
        
        self.mathematical_keywords = [
            'theorem', 'definition', 'proof', 'lemma', 'corollary',
            '定理', '定义', '证明', '引理', '推论',
            'formula', 'equation', 'mathematical', '数学', '公式'
        ]
        
        self.code_languages = [
            'rust', 'typescript', 'python', 'javascript', 'solidity',
            'go', 'java', 'cpp', 'csharp', 'kotlin'
        ]
    
    def validate_document(self, file_path: Path) -> QualityMetrics:
        """验证单个文档的质量"""
        try:
            content = file_path.read_text(encoding='utf-8')
        except UnicodeDecodeError:
            try:
                content = file_path.read_text(encoding='gbk')
            except:
                return QualityMetrics()
        
        metrics = QualityMetrics()
        metrics.total_lines = len(content.split('\n'))
        
        # 检查数学内容
        metrics.has_mathematical_content = self._check_mathematical_content(content)
        metrics.latex_formula_count = self._count_latex_formulas(content)
        metrics.has_theorems = self._check_theorems(content)
        metrics.has_definitions = self._check_definitions(content)
        metrics.has_proofs = self._check_proofs(content)
        
        # 检查代码实现
        metrics.has_code_implementation = self._check_code_implementation(content)
        metrics.code_block_count = self._count_code_blocks(content)
        
        # 检查安全分析
        metrics.has_security_analysis = self._check_security_analysis(content)
        metrics.security_keyword_count = self._count_security_keywords(content)
        
        # 检查参考文献
        metrics.has_references = self._check_references(content)
        
        # 计算质量分数
        metrics.quality_score = self._calculate_quality_score(metrics)
        
        return metrics
    
    def _check_mathematical_content(self, content: str) -> bool:
        """检查是否包含数学内容"""
        # 检查LaTeX公式
        if re.search(r'\\\w+{.*?}', content):
            return True
        
        # 检查数学关键词
        for keyword in self.mathematical_keywords:
            if keyword.lower() in content.lower():
                return True
        
        # 检查数学符号
        math_symbols = ['∑', '∏', '∫', '√', '∞', '≤', '≥', '≠', '∈', '∉', '⊂', '⊃']
        for symbol in math_symbols:
            if symbol in content:
                return True
        
        return False
    
    def _count_latex_formulas(self, content: str) -> int:
        """统计LaTeX公式数量"""
        # 行内公式
        inline_formulas = len(re.findall(r'\$.*?\$', content))
        # 块级公式
        block_formulas = len(re.findall(r'\$\$.*?\$\$', content))
        # 其他LaTeX命令
        latex_commands = len(re.findall(r'\\\w+{.*?}', content))
        
        return inline_formulas + block_formulas + latex_commands
    
    def _check_theorems(self, content: str) -> bool:
        """检查是否包含定理"""
        theorem_patterns = [
            r'\\begin{theorem}',
            r'定理\s*\d+',
            r'Theorem\s*\d+',
            r'#### 定理',
            r'### 定理'
        ]
        
        for pattern in theorem_patterns:
            if re.search(pattern, content, re.IGNORECASE):
                return True
        
        return False
    
    def _check_definitions(self, content: str) -> bool:
        """检查是否包含定义"""
        definition_patterns = [
            r'\\begin{definition}',
            r'定义\s*\d+',
            r'Definition\s*\d+',
            r'#### 定义',
            r'### 定义'
        ]
        
        for pattern in definition_patterns:
            if re.search(pattern, content, re.IGNORECASE):
                return True
        
        return False
    
    def _check_proofs(self, content: str) -> bool:
        """检查是否包含证明"""
        proof_patterns = [
            r'\\begin{proof}',
            r'证明',
            r'Proof',
            r'#### 证明',
            r'### 证明'
        ]
        
        for pattern in proof_patterns:
            if re.search(pattern, content, re.IGNORECASE):
                return True
        
        return False
    
    def _check_code_implementation(self, content: str) -> bool:
        """检查是否包含代码实现"""
        # 检查代码块
        for language in self.code_languages:
            if re.search(f'```{language}', content, re.IGNORECASE):
                return True
        
        # 检查通用代码块
        if re.search(r'```\w*\n', content):
            return True
        
        return False
    
    def _count_code_blocks(self, content: str) -> int:
        """统计代码块数量"""
        return len(re.findall(r'```\w*\n.*?```', content, re.DOTALL))
    
    def _check_security_analysis(self, content: str) -> bool:
        """检查是否包含安全分析"""
        for keyword in self.security_keywords:
            if keyword.lower() in content.lower():
                return True
        
        return False
    
    def _count_security_keywords(self, content: str) -> int:
        """统计安全关键词数量"""
        count = 0
        for keyword in self.security_keywords:
            count += len(re.findall(keyword, content, re.IGNORECASE))
        return count
    
    def _check_references(self, content: str) -> bool:
        """检查是否包含参考文献"""
        reference_patterns = [
            r'参考文献',
            r'References',
            r'Bibliography',
            r'## 参考文献',
            r'## References'
        ]
        
        for pattern in reference_patterns:
            if re.search(pattern, content, re.IGNORECASE):
                return True
        
        return False
    
    def _calculate_quality_score(self, metrics: QualityMetrics) -> float:
        """计算质量分数"""
        score = 0.0
        
        # 数学内容 (40分)
        if metrics.has_mathematical_content:
            score += 20
        if metrics.has_theorems:
            score += 10
        if metrics.has_definitions:
            score += 5
        if metrics.has_proofs:
            score += 5
        
        # 代码实现 (30分)
        if metrics.has_code_implementation:
            score += 20
        if metrics.code_block_count > 0:
            score += min(10, metrics.code_block_count * 2)
        
        # 安全分析 (20分)
        if metrics.has_security_analysis:
            score += 15
        if metrics.security_keyword_count > 0:
            score += min(5, metrics.security_keyword_count)
        
        # 参考文献 (10分)
        if metrics.has_references:
            score += 10
        
        return min(100.0, score)
    
    def validate_all_documents(self) -> Dict[str, QualityMetrics]:
        """验证所有文档"""
        results = {}
        
        for file_path in self.base_dir.rglob('*.md'):
            if file_path.name.startswith('.'):
                continue
            
            relative_path = file_path.relative_to(self.base_dir)
            print(f"验证文档: {relative_path}")
            
            try:
                metrics = self.validate_document(file_path)
                results[str(relative_path)] = metrics
            except Exception as e:
                print(f"验证失败 {relative_path}: {e}")
                continue
        
        return results
    
    def generate_report(self, results: Dict[str, QualityMetrics]) -> str:
        """生成质量报告"""
        total_docs = len(results)
        if total_docs == 0:
            return "没有找到文档"
        
        # 统计质量分布
        excellent = sum(1 for m in results.values() if m.quality_score >= 90)
        good = sum(1 for m in results.values() if 80 <= m.quality_score < 90)
        fair = sum(1 for m in results.values() if 70 <= m.quality_score < 80)
        poor = sum(1 for m in results.values() if m.quality_score < 70)
        
        # 统计内容类型
        has_math = sum(1 for m in results.values() if m.has_mathematical_content)
        has_code = sum(1 for m in results.values() if m.has_code_implementation)
        has_security = sum(1 for m in results.values() if m.has_security_analysis)
        has_refs = sum(1 for m in results.values() if m.has_references)
        
        # 计算平均分数
        avg_score = sum(m.quality_score for m in results.values()) / total_docs
        
        report = f"""
# 文档质量验证报告

**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
**总文档数**: {total_docs}

## 质量分布

- **优秀 (90-100分)**: {excellent} 个 ({excellent/total_docs*100:.1f}%)
- **良好 (80-89分)**: {good} 个 ({good/total_docs*100:.1f}%)
- **合格 (70-79分)**: {fair} 个 ({fair/total_docs*100:.1f}%)
- **不合格 (<70分)**: {poor} 个 ({poor/total_docs*100:.1f}%)

## 内容类型统计

- **包含数学内容**: {has_math} 个 ({has_math/total_docs*100:.1f}%)
- **包含代码实现**: {has_code} 个 ({has_code/total_docs*100:.1f}%)
- **包含安全分析**: {has_security} 个 ({has_security/total_docs*100:.1f}%)
- **包含参考文献**: {has_refs} 个 ({has_refs/total_docs*100:.1f}%)

## 平均质量分数

**{avg_score:.1f}/100**

## 详细结果

"""
        
        # 按质量分数排序
        sorted_results = sorted(results.items(), key=lambda x: x[1].quality_score, reverse=True)
        
        for file_path, metrics in sorted_results:
            report += f"""
### {file_path}

- **质量分数**: {metrics.quality_score:.1f}/100
- **总行数**: {metrics.total_lines}
- **LaTeX公式**: {metrics.latex_formula_count}
- **代码块**: {metrics.code_block_count}
- **安全关键词**: {metrics.security_keyword_count}
- **数学内容**: {'✅' if metrics.has_mathematical_content else '❌'}
- **代码实现**: {'✅' if metrics.has_code_implementation else '❌'}
- **安全分析**: {'✅' if metrics.has_security_analysis else '❌'}
- **参考文献**: {'✅' if metrics.has_references else '❌'}
"""
        
        return report
    
    def save_report(self, report: str, output_file: str):
        """保存报告到文件"""
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(report)
        print(f"报告已保存到: {output_file}")
    
    def export_json(self, results: Dict[str, QualityMetrics], output_file: str):
        """导出结果为JSON格式"""
        json_data = {}
        for file_path, metrics in results.items():
            json_data[file_path] = {
                'has_mathematical_content': metrics.has_mathematical_content,
                'has_code_implementation': metrics.has_code_implementation,
                'has_security_analysis': metrics.has_security_analysis,
                'has_references': metrics.has_references,
                'has_theorems': metrics.has_theorems,
                'has_definitions': metrics.has_definitions,
                'has_proofs': metrics.has_proofs,
                'latex_formula_count': metrics.latex_formula_count,
                'code_block_count': metrics.code_block_count,
                'security_keyword_count': metrics.security_keyword_count,
                'total_lines': metrics.total_lines,
                'quality_score': metrics.quality_score
            }
        
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(json_data, f, ensure_ascii=False, indent=2)
        print(f"JSON结果已保存到: {output_file}")

def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='文档质量验证工具')
    parser.add_argument('--base-dir', default='.', help='基础目录路径')
    parser.add_argument('--output', default='quality_report.md', help='输出报告文件名')
    parser.add_argument('--json', help='输出JSON结果文件名')
    parser.add_argument('--verbose', '-v', action='store_true', help='详细输出')
    
    args = parser.parse_args()
    
    # 创建验证器
    validator = DocumentQualityValidator(args.base_dir)
    
    print("开始验证文档质量...")
    
    # 验证所有文档
    results = validator.validate_all_documents()
    
    if not results:
        print("没有找到文档")
        return
    
    # 生成报告
    report = validator.generate_report(results)
    
    # 保存报告
    validator.save_report(report, args.output)
    
    # 导出JSON结果
    if args.json:
        validator.export_json(results, args.json)
    
    # 详细输出
    if args.verbose:
        print("\n" + "="*50)
        print("验证完成！")
        print(f"总文档数: {len(results)}")
        avg_score = sum(m.quality_score for m in results.values()) / len(results)
        print(f"平均质量分数: {avg_score:.1f}/100")

if __name__ == '__main__':
    main()
