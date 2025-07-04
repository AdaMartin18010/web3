#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
文档质量验证脚本
检查Analysis文件夹中文档的学术标准和质量
"""

import os
import re
from pathlib import Path
from typing import Dict, List, Tuple
import json

class DocumentQualityValidator:
    """文档质量验证器"""
    
    def __init__(self, base_dir: str = "docs/Analysis"):
        self.base_dir = Path(base_dir)
        self.quality_metrics = {
            'mathematical_content': 0,
            'code_implementation': 0,
            'security_analysis': 0,
            'references': 0,
            'structure_quality': 0
        }
        
    def validate_mathematical_content(self, content: str) -> bool:
        """验证是否包含数学内容"""
        # 检查LaTeX公式
        latex_patterns = [
            r'\\begin\{definition\}',
            r'\\begin\{theorem\}',
            r'\\begin\{proof\}',
            r'\\[.*?\\]',
            r'\$.*?\$'
        ]
        
        for pattern in latex_patterns:
            if re.search(pattern, content):
                return True
        return False
    
    def validate_code_implementation(self, content: str) -> bool:
        """验证是否包含代码实现"""
        code_patterns = [
            r'```rust',
            r'```typescript',
            r'```python',
            r'```solidity',
            r'pub struct',
            r'impl ',
            r'function ',
            r'class '
        ]
        
        for pattern in code_patterns:
            if re.search(pattern, content):
                return True
        return False
    
    def validate_security_analysis(self, content: str) -> bool:
        """验证是否包含安全分析"""
        security_keywords = [
            'threat', 'attack', 'vulnerability', 'security',
            '威胁', '攻击', '漏洞', '安全', '防护'
        ]
        
        for keyword in security_keywords:
            if keyword.lower() in content.lower():
                return True
        return False
    
    def validate_references(self, content: str) -> bool:
        """验证是否包含参考文献"""
        reference_patterns = [
            r'参考文献',
            r'References',
            r'\[.*?\]\(.*?\)',
            r'作者.*?年份'
        ]
        
        for pattern in reference_patterns:
            if re.search(pattern, content):
                return True
        return False
    
    def validate_structure_quality(self, content: str) -> bool:
        """验证文档结构质量"""
        structure_indicators = [
            r'## \d+\.',
            r'### \d+\.\d+',
            r'摘要',
            r'引言',
            r'结论'
        ]
        
        count = 0
        for pattern in structure_indicators:
            if re.search(pattern, content):
                count += 1
        
        return count >= 3  # 至少包含3个结构元素
    
    def calculate_quality_score(self, file_path: Path) -> Dict[str, any]:
        """计算文档质量分数"""
        try:
            content = file_path.read_text(encoding='utf-8')
        except Exception as e:
            return {
                'file': str(file_path),
                'error': str(e),
                'score': 0,
                'details': {}
            }
        
        # 检查各项指标
        has_math = self.validate_mathematical_content(content)
        has_code = self.validate_code_implementation(content)
        has_security = self.validate_security_analysis(content)
        has_refs = self.validate_references(content)
        has_structure = self.validate_structure_quality(content)
        
        # 计算总分
        score = 0
        details = {}
        
        if has_math:
            score += 20
            details['mathematical_content'] = True
        else:
            details['mathematical_content'] = False
            
        if has_code:
            score += 20
            details['code_implementation'] = True
        else:
            details['code_implementation'] = False
            
        if has_security:
            score += 20
            details['security_analysis'] = True
        else:
            details['security_analysis'] = False
            
        if has_refs:
            score += 20
            details['references'] = True
        else:
            details['references'] = False
            
        if has_structure:
            score += 20
            details['structure_quality'] = True
        else:
            details['structure_quality'] = False
        
        return {
            'file': str(file_path),
            'score': score,
            'details': details,
            'word_count': len(content.split())
        }
    
    def analyze_all_documents(self) -> Dict[str, any]:
        """分析所有文档"""
        results = {
            'total_files': 0,
            'quality_distribution': {
                'excellent': 0,  # 90-100
                'good': 0,       # 80-89
                'fair': 0,       # 70-79
                'poor': 0,       # <70
                'template_only': 0  # 只有模板
            },
            'detailed_results': [],
            'recommendations': []
        }
        
        for file_path in self.base_dir.rglob('*.md'):
            if file_path.name.startswith('.'):
                continue
                
            results['total_files'] += 1
            result = self.calculate_quality_score(file_path)
            results['detailed_results'].append(result)
            
            # 分类质量等级
            score = result['score']
            if score >= 90:
                results['quality_distribution']['excellent'] += 1
            elif score >= 80:
                results['quality_distribution']['good'] += 1
            elif score >= 70:
                results['quality_distribution']['fair'] += 1
            elif score > 0:
                results['quality_distribution']['poor'] += 1
            else:
                results['quality_distribution']['template_only'] += 1
        
        # 生成建议
        results['recommendations'] = self.generate_recommendations(results)
        
        return results
    
    def generate_recommendations(self, results: Dict) -> List[str]:
        """生成改进建议"""
        recommendations = []
        
        total_files = results['total_files']
        template_only = results['quality_distribution']['template_only']
        poor_quality = results['quality_distribution']['poor']
        
        if template_only > total_files * 0.5:
            recommendations.append(f"⚠️  严重问题: {template_only}/{total_files} 个文件只包含模板内容")
            recommendations.append("建议: 立即开始内容重构，优先处理核心文档")
        
        if poor_quality > total_files * 0.3:
            recommendations.append(f"⚠️  质量问题: {poor_quality}/{total_files} 个文件质量较差")
            recommendations.append("建议: 添加数学定义、代码实现和安全分析")
        
        if results['quality_distribution']['excellent'] < total_files * 0.1:
            recommendations.append("📈 改进机会: 优秀文档比例过低")
            recommendations.append("建议: 选择10个核心文档进行深度重构")
        
        # 具体建议
        recommendations.extend([
            "🔧 立即行动:",
            "  1. 删除重复的模板文件",
            "  2. 重命名夸张的文件名",
            "  3. 为每个文档添加数学定义",
            "  4. 实现可运行的代码示例",
            "  5. 添加安全性分析",
            "",
            "📚 学术标准:",
            "  1. 使用LaTeX格式的数学公式",
            "  2. 提供完整的定理证明",
            "  3. 包含详细的参考文献",
            "  4. 添加性能基准测试",
            "  5. 建立威胁模型"
        ])
        
        return recommendations
    
    def generate_report(self):
        """生成质量报告"""
        print("🔍 Web3理论分析文档库质量评估报告")
        print("=" * 60)
        
        results = self.analyze_all_documents()
        
        print(f"\n📊 总体统计")
        print(f"   总文件数: {results['total_files']}")
        
        print(f"\n📈 质量分布")
        for level, count in results['quality_distribution'].items():
            percentage = (count / results['total_files']) * 100 if results['total_files'] > 0 else 0
            print(f"   {level.capitalize()}: {count} 个 ({percentage:.1f}%)")
        
        print(f"\n🏆 优秀文档 (90-100分)")
        excellent_files = [r for r in results['detailed_results'] if r['score'] >= 90]
        for file_result in excellent_files[:5]:  # 显示前5个
            print(f"   ✅ {file_result['file']} ({file_result['score']}分)")
        
        print(f"\n⚠️  需要改进的文档 (<70分)")
        poor_files = [r for r in results['detailed_results'] if r['score'] < 70]
        for file_result in poor_files[:10]:  # 显示前10个
            print(f"   ❌ {file_result['file']} ({file_result['score']}分)")
        
        print(f"\n💡 改进建议")
        for recommendation in results['recommendations']:
            print(f"   {recommendation}")
        
        # 保存详细结果
        report_file = self.base_dir / "quality_assessment_report.json"
        with open(report_file, 'w', encoding='utf-8') as f:
            json.dump(results, f, ensure_ascii=False, indent=2)
        
        print(f"\n📄 详细报告已保存到: {report_file}")
        print("=" * 60)

def main():
    validator = DocumentQualityValidator()
    validator.generate_report()

if __name__ == "__main__":
    main() 