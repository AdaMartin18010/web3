#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Web3文档体系清理与整合脚本
用于自动化处理docs文件夹下的文档清理、合并和重组
"""

import os
import shutil
import re
import json
from pathlib import Path
from typing import Dict, List, Tuple, Set
import hashlib
from datetime import datetime

class Web3DocProcessor:
    def __init__(self, docs_path: str = "docs"):
        self.docs_path = Path(docs_path)
        self.backup_path = self.docs_path / "backup_before_cleanup"
        self.analysis_results = {
            "total_files": 0,
            "empty_files": [],
            "duplicate_content": [],
            "large_files": [],
            "broken_links": [],
            "merge_candidates": []
        }
        
    def create_backup(self):
        """创建文档备份"""
        if self.backup_path.exists():
            shutil.rmtree(self.backup_path)
        shutil.copytree(self.docs_path, self.backup_path, ignore=shutil.ignore_patterns('backup_*'))
        print(f"备份已创建: {self.backup_path}")
        
    def analyze_document_structure(self) -> Dict:
        """分析文档结构"""
        structure = {
            "directories": [],
            "files": [],
            "file_sizes": {},
            "content_hashes": {},
            "potential_duplicates": []
        }
        
        for root, dirs, files in os.walk(self.docs_path):
            # 跳过备份目录
            if "backup" in root:
                continue
                
            for file in files:
                if file.endswith('.md'):
                    file_path = Path(root) / file
                    relative_path = file_path.relative_to(self.docs_path)
                    
                    # 获取文件大小
                    size = file_path.stat().st_size
                    structure["files"].append(str(relative_path))
                    structure["file_sizes"][str(relative_path)] = size
                    
                    # 计算内容哈希
                    if size > 0:
                        with open(file_path, 'r', encoding='utf-8') as f:
                            content = f.read()
                            content_hash = hashlib.md5(content.encode()).hexdigest()
                            structure["content_hashes"][str(relative_path)] = content_hash
                            
                            # 检查重复内容
                            for existing_file, existing_hash in structure["content_hashes"].items():
                                if existing_file != str(relative_path) and existing_hash == content_hash:
                                    structure["potential_duplicates"].append({
                                        "file1": existing_file,
                                        "file2": str(relative_path),
                                        "hash": content_hash
                                    })
                    
                    # 记录空文件
                    if size == 0:
                        self.analysis_results["empty_files"].append(str(relative_path))
                        
                    # 记录大文件
                    if size > 100 * 1024:  # 100KB
                        self.analysis_results["large_files"].append({
                            "file": str(relative_path),
                            "size": size
                        })
        
        return structure
    
    def identify_merge_candidates(self) -> List[Dict]:
        """识别可合并的文档"""
        merge_candidates = []
        
        # 技术栈文档合并
        tech_stack_files = []
        for file in self.analysis_results.get("files", []):
            if "Technology_Stack" in file or "tech_stack" in file.lower():
                tech_stack_files.append(file)
        
        if len(tech_stack_files) > 5:
            merge_candidates.append({
                "category": "Technology_Stack",
                "files": tech_stack_files,
                "target_file": "03_Technology_Stacks/Consolidated_Technology_Stacks.md",
                "priority": "high"
            })
        
        # 镜像理论文档合并
        mirror_theory_files = []
        for file in self.analysis_results.get("files", []):
            if "Mirror" in file or "mirror" in file.lower():
                mirror_theory_files.append(file)
        
        if len(mirror_theory_files) > 3:
            merge_candidates.append({
                "category": "Mirror_Theory",
                "files": mirror_theory_files,
                "target_file": "04_Advanced_Theories/Mirror_Theory_Consolidated.md",
                "priority": "high"
            })
        
        # 理论基础文档合并
        theoretical_files = []
        for file in self.analysis_results.get("files", []):
            if any(keyword in file for keyword in ["Mathematical", "Cryptographic", "Distributed", "Formal"]):
                theoretical_files.append(file)
        
        if len(theoretical_files) > 10:
            merge_candidates.append({
                "category": "Theoretical_Foundations",
                "files": theoretical_files,
                "target_file": "01_Theoretical_Foundations/Consolidated_Theoretical_Foundations.md",
                "priority": "medium"
            })
        
        return merge_candidates
    
    def merge_documents(self, merge_candidate: Dict) -> bool:
        """合并文档"""
        try:
            target_path = self.docs_path / merge_candidate["target_file"]
            target_path.parent.mkdir(parents=True, exist_ok=True)
            
            merged_content = f"# {merge_candidate['category']} 整合文档\n\n"
            merged_content += f"**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n"
            merged_content += f"**合并文件数**: {len(merge_candidate['files'])}\n\n"
            merged_content += "## 目录\n\n"
            
            # 添加目录
            for i, file in enumerate(merge_candidate["files"], 1):
                merged_content += f"{i}. [{Path(file).stem}](#section-{i})\n"
            
            merged_content += "\n---\n\n"
            
            # 合并内容
            for i, file in enumerate(merge_candidate["files"], 1):
                file_path = self.docs_path / file
                if file_path.exists():
                    merged_content += f"## {Path(file).stem} {{#section-{i}}}\n\n"
                    merged_content += f"**源文件**: `{file}`\n\n"
                    
                    with open(file_path, 'r', encoding='utf-8') as f:
                        content = f.read()
                        # 移除标题，保留内容
                        lines = content.split('\n')
                        content_lines = []
                        skip_header = False
                        for line in lines:
                            if line.startswith('#') and not skip_header:
                                skip_header = True
                                continue
                            if skip_header:
                                content_lines.append(line)
                        
                        merged_content += '\n'.join(content_lines) + '\n\n'
                        merged_content += "---\n\n"
            
            # 写入合并文件
            with open(target_path, 'w', encoding='utf-8') as f:
                f.write(merged_content)
            
            print(f"成功合并文档: {target_path}")
            return True
            
        except Exception as e:
            print(f"合并文档失败: {e}")
            return False
    
    def remove_empty_files(self) -> int:
        """删除空文件"""
        removed_count = 0
        for file_path in self.analysis_results["empty_files"]:
            full_path = self.docs_path / file_path
            if full_path.exists():
                full_path.unlink()
                removed_count += 1
                print(f"删除空文件: {file_path}")
        
        return removed_count
    
    def create_new_structure(self):
        """创建新的目录结构"""
        new_structure = [
            "01_Theoretical_Foundations",
            "02_Core_Technologies", 
            "03_Technology_Stacks",
            "04_Advanced_Theories",
            "05_Applications",
            "06_Research_Reports"
        ]
        
        for dir_name in new_structure:
            dir_path = self.docs_path / dir_name
            dir_path.mkdir(exist_ok=True)
            
            # 创建README文件
            readme_path = dir_path / "README.md"
            if not readme_path.exists():
                with open(readme_path, 'w', encoding='utf-8') as f:
                    f.write(f"# {dir_name}\n\n")
                    f.write(f"本目录包含{dir_name}相关的文档。\n\n")
                    f.write(f"**创建时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
    
    def generate_analysis_report(self) -> str:
        """生成分析报告"""
        report = f"""# Web3文档体系分析报告

**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

## 统计信息

- **总文件数**: {len(self.analysis_results.get('files', []))}
- **空文件数**: {len(self.analysis_results['empty_files'])}
- **大文件数**: {len(self.analysis_results['large_files'])}
- **重复内容数**: {len(self.analysis_results['duplicate_content'])}

## 空文件列表

"""
        
        for file in self.analysis_results['empty_files']:
            report += f"- {file}\n"
        
        report += "\n## 大文件列表\n\n"
        for item in self.analysis_results['large_files']:
            size_mb = item['size'] / (1024 * 1024)
            report += f"- {item['file']} ({size_mb:.2f}MB)\n"
        
        report += "\n## 建议的合并操作\n\n"
        merge_candidates = self.identify_merge_candidates()
        for candidate in merge_candidates:
            report += f"### {candidate['category']}\n"
            report += f"- 优先级: {candidate['priority']}\n"
            report += f"- 目标文件: {candidate['target_file']}\n"
            report += f"- 源文件数: {len(candidate['files'])}\n\n"
        
        return report
    
    def run_full_cleanup(self):
        """执行完整的清理流程"""
        print("开始Web3文档体系清理...")
        
        # 1. 创建备份
        self.create_backup()
        
        # 2. 分析文档结构
        print("分析文档结构...")
        structure = self.analyze_document_structure()
        self.analysis_results.update(structure)
        
        # 3. 删除空文件
        print("删除空文件...")
        removed_count = self.remove_empty_files()
        print(f"删除了 {removed_count} 个空文件")
        
        # 4. 识别合并候选
        print("识别合并候选...")
        merge_candidates = self.identify_merge_candidates()
        
        # 5. 执行合并
        print("执行文档合并...")
        for candidate in merge_candidates:
            if candidate['priority'] == 'high':
                self.merge_documents(candidate)
        
        # 6. 创建新结构
        print("创建新的目录结构...")
        self.create_new_structure()
        
        # 7. 生成报告
        print("生成分析报告...")
        report = self.generate_analysis_report()
        report_path = self.docs_path / "CLEANUP_ANALYSIS_REPORT.md"
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write(report)
        
        print(f"清理完成！报告已保存到: {report_path}")

def main():
    """主函数"""
    processor = Web3DocProcessor()
    
    # 检查是否在正确的目录
    if not processor.docs_path.exists():
        print(f"错误: {processor.docs_path} 目录不存在")
        return
    
    # 执行清理
    processor.run_full_cleanup()

if __name__ == "__main__":
    main()
