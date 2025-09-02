#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
多线程文档清理工具
用于删除重复文件和重命名夸张文件名
"""

import os
import re
import hashlib
import asyncio
import aiofiles
from pathlib import Path
from typing import List, Dict, Tuple, Set
from concurrent.futures import ThreadPoolExecutor, as_completed
import logging
from dataclasses import dataclass
from datetime import datetime
import json

# 配置日志
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

@dataclass
class CleanupTask:
    """清理任务"""
    task_type: str  # 'delete' 或 'rename'
    file_path: Path
    target_name: str = None
    reason: str = ""

class DocumentCleanupTool:
    """文档清理工具"""
    
    def __init__(self, base_dir: str, max_workers: int = 8):
        self.base_dir = Path(base_dir)
        self.max_workers = max_workers
        self.duplicate_patterns = self._load_duplicate_patterns()
        self.exaggerated_patterns = self._load_exaggerated_patterns()
        
    def _load_duplicate_patterns(self) -> List[str]:
        """加载重复文件模式"""
        return [
            r'COMPREHENSIVE_.*_REPORT\.md',
            r'FINAL_.*_SUMMARY\.md',
            r'PROJECT_.*_FINAL\.md',
            r'ULTIMATE_.*_COMPLETION\.md',
            r'ETERNAL_.*_RECORD\.md',
            r'COSMIC_.*_FEDERATION\.md',
            r'UNIVERSAL_.*_NETWORK\.md',
            r'ABSOLUTE_.*_ENGINE\.md',
            r'QUANTUM_.*_SYSTEM\.md',
            r'DIMENSIONAL_.*_TECHNOLOGY\.md'
        ]
    
    def _load_exaggerated_patterns(self) -> List[Tuple[str, str]]:
        """加载夸张文件名模式及其建议的新名称"""
        return [
            (r'ABSOLUTE_REALITY_MASTERY_ENGINE', 'reality_manipulation_theory'),
            (r'COSMIC_INTELLIGENCE_FEDERATION', 'distributed_intelligence_system'),
            (r'QUANTUM_CONSCIOUSNESS_INTEGRATION_SYSTEM', 'quantum_consciousness_theory'),
            (r'UNIVERSAL_CONSCIOUSNESS_NETWORK', 'consciousness_network_theory'),
            (r'DIMENSIONAL_TRANSCENDENCE_TECHNOLOGY', 'dimensional_transcendence_theory'),
            (r'ETERNAL_MONUMENT_RECORD', 'monument_record_system'),
            (r'ULTIMATE_PROJECT_COMPLETION_SHOWCASE', 'project_completion_showcase'),
            (r'FINAL_ACHIEVEMENT_CHRONICLE', 'achievement_chronicle'),
            (r'PROJECT_CELEBRATION_FINAL_DELIVERY', 'project_celebration_delivery'),
            (r'FINAL_PROJECT_COMPLETION_DECLARATION', 'project_completion_declaration'),
            (r'WEB3_.*_FINAL_REPORT', 'web3_final_report'),
            (r'WEB3_.*_COMPLETION_REPORT', 'web3_completion_report'),
            (r'WEB3_.*_FINAL_ANALYSIS', 'web3_final_analysis'),
            (r'PROJECT_.*_FINAL_SHOWCASE', 'project_final_showcase'),
            (r'PROJECT_.*_LEGACY_KNOWLEDGE', 'project_legacy_knowledge'),
            (r'PROJECT_.*_DELIVERY_CHECKLIST', 'project_delivery_checklist'),
            (r'PROJECT_.*_FINAL_CHRONICLE', 'project_final_chronicle'),
            (r'PROJECT_.*_COMPLETION_SUMMARY', 'project_completion_summary'),
            (r'PROJECT_.*_FINAL_DECLARATION', 'project_final_declaration'),
            (r'PROJECT_.*_FINAL_ACHIEVEMENT', 'project_final_achievement')
        ]
    
    def _calculate_file_hash(self, file_path: Path) -> str:
        """计算文件哈希值"""
        try:
            with open(file_path, 'rb') as f:
                content = f.read()
                return hashlib.md5(content).hexdigest()
        except Exception as e:
            logger.error(f"计算文件哈希时出错 {file_path}: {e}")
            return ""
    
    def _is_duplicate_file(self, file_path: Path) -> bool:
        """判断是否为重复文件"""
        filename = file_path.name
        
        # 检查是否匹配重复模式
        for pattern in self.duplicate_patterns:
            if re.match(pattern, filename, re.IGNORECASE):
                return True
        
        return False
    
    def _should_rename_file(self, file_path: Path) -> Tuple[bool, str]:
        """判断是否应该重命名文件"""
        filename = file_path.name
        
        for pattern, new_name in self.exaggerated_patterns:
            if re.search(pattern, filename, re.IGNORECASE):
                return True, new_name
        
        return False, ""
    
    async def scan_files(self) -> Tuple[List[Path], List[Path]]:
        """扫描文件，识别重复文件和需要重命名的文件"""
        duplicate_files = []
        rename_files = []
        
        all_files = list(self.base_dir.rglob('*.md'))
        logger.info(f"扫描到 {len(all_files)} 个文档文件")
        
        for file_path in all_files:
            # 检查重复文件
            if self._is_duplicate_file(file_path):
                duplicate_files.append(file_path)
                logger.info(f"发现重复文件: {file_path}")
            
            # 检查需要重命名的文件
            should_rename, new_name = self._should_rename_file(file_path)
            if should_rename:
                rename_files.append(file_path)
                logger.info(f"发现需要重命名的文件: {file_path} -> {new_name}")
        
        return duplicate_files, rename_files
    
    async def delete_duplicate_files(self, duplicate_files: List[Path]) -> Dict[str, any]:
        """删除重复文件"""
        results = {
            'total': len(duplicate_files),
            'successful': 0,
            'failed': 0,
            'deleted_files': [],
            'errors': []
        }
        
        logger.info(f"开始删除 {len(duplicate_files)} 个重复文件")
        
        # 使用线程池并发删除
        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            future_to_path = {
                executor.submit(self._delete_single_file, path): path
                for path in duplicate_files
            }
            
            for future in as_completed(future_to_path):
                path = future_to_path[future]
                try:
                    success = future.result()
                    if success:
                        results['successful'] += 1
                        results['deleted_files'].append(str(path))
                        logger.info(f"成功删除: {path}")
                    else:
                        results['failed'] += 1
                        results['errors'].append(f"删除失败: {path}")
                except Exception as e:
                    results['failed'] += 1
                    results['errors'].append(f"删除错误 {path}: {e}")
        
        return results
    
    def _delete_single_file(self, file_path: Path) -> bool:
        """删除单个文件"""
        try:
            file_path.unlink()
            return True
        except Exception as e:
            logger.error(f"删除文件 {file_path} 时出错: {e}")
            return False
    
    async def rename_files(self, rename_files: List[Path]) -> Dict[str, any]:
        """重命名文件"""
        results = {
            'total': len(rename_files),
            'successful': 0,
            'failed': 0,
            'renamed_files': [],
            'errors': []
        }
        
        logger.info(f"开始重命名 {len(rename_files)} 个文件")
        
        # 使用线程池并发重命名
        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            future_to_path = {
                executor.submit(self._rename_single_file, path): path
                for path in rename_files
            }
            
            for future in as_completed(future_to_path):
                path = future_to_path[future]
                try:
                    success, new_name = future.result()
                    if success:
                        results['successful'] += 1
                        results['renamed_files'].append({
                            'old_name': str(path),
                            'new_name': new_name
                        })
                        logger.info(f"成功重命名: {path} -> {new_name}")
                    else:
                        results['failed'] += 1
                        results['errors'].append(f"重命名失败: {path}")
                except Exception as e:
                    results['failed'] += 1
                    results['errors'].append(f"重命名错误 {path}: {e}")
        
        return results
    
    def _rename_single_file(self, file_path: Path) -> Tuple[bool, str]:
        """重命名单个文件"""
        try:
            should_rename, new_name = self._should_rename_file(file_path)
            if not should_rename:
                return False, ""
            
            # 构建新的文件名
            new_filename = file_path.name
            for pattern, replacement in self.exaggerated_patterns:
                new_filename = re.sub(pattern, replacement, new_filename, flags=re.IGNORECASE)
            
            new_path = file_path.parent / new_filename
            
            # 检查新文件名是否已存在
            counter = 1
            while new_path.exists():
                name_parts = new_filename.rsplit('.', 1)
                if len(name_parts) == 2:
                    new_filename = f"{name_parts[0]}_{counter}.{name_parts[1]}"
                else:
                    new_filename = f"{new_filename}_{counter}"
                new_path = file_path.parent / new_filename
                counter += 1
            
            # 重命名文件
            file_path.rename(new_path)
            return True, str(new_path)
            
        except Exception as e:
            logger.error(f"重命名文件 {file_path} 时出错: {e}")
            return False, ""
    
    async def run_full_cleanup(self) -> Dict[str, any]:
        """运行完整的清理流程"""
        logger.info("开始运行完整文档清理流程")
        
        # 1. 扫描文件
        duplicate_files, rename_files = await self.scan_files()
        
        # 2. 删除重复文件
        delete_results = await self.delete_duplicate_files(duplicate_files)
        
        # 3. 重命名文件
        rename_results = await self.rename_files(rename_files)
        
        # 4. 生成清理报告
        cleanup_report = {
            'timestamp': datetime.now().isoformat(),
            'scan_results': {
                'duplicate_files_found': len(duplicate_files),
                'rename_files_found': len(rename_files)
            },
            'delete_results': delete_results,
            'rename_results': rename_results,
            'summary': {
                'total_processed': len(duplicate_files) + len(rename_files),
                'total_successful': delete_results['successful'] + rename_results['successful'],
                'total_failed': delete_results['failed'] + rename_results['failed']
            }
        }
        
        logger.info("文档清理流程完成")
        return cleanup_report
    
    async def generate_cleanup_plan(self) -> Dict[str, any]:
        """生成清理计划（不执行实际操作）"""
        logger.info("生成清理计划")
        
        duplicate_files, rename_files = await self.scan_files()
        
        plan = {
            'timestamp': datetime.now().isoformat(),
            'actions': {
                'delete_files': [
                    {
                        'file_path': str(path),
                        'reason': '重复文件',
                        'size': path.stat().st_size if path.exists() else 0
                    }
                    for path in duplicate_files
                ],
                'rename_files': [
                    {
                        'old_name': str(path),
                        'new_name': self._should_rename_file(path)[1],
                        'reason': '夸张文件名'
                    }
                    for path in rename_files
                ]
            },
            'summary': {
                'files_to_delete': len(duplicate_files),
                'files_to_rename': len(rename_files),
                'estimated_space_saved': sum(
                    path.stat().st_size if path.exists() else 0 
                    for path in duplicate_files
                )
            }
        }
        
        return plan

async def main():
    """主函数"""
    # 设置基础目录
    base_dir = "docs/Analysis"
    
    # 创建清理工具实例
    cleanup_tool = DocumentCleanupTool(base_dir, max_workers=8)
    
    # 生成清理计划
    plan = await cleanup_tool.generate_cleanup_plan()
    
    print("\n=== 文档清理计划 ===")
    print(f"需要删除的文件: {plan['summary']['files_to_delete']}")
    print(f"需要重命名的文件: {plan['summary']['files_to_rename']}")
    print(f"预计节省空间: {plan['summary']['estimated_space_saved']} 字节")
    
    # 保存清理计划
    plan_file = Path(base_dir) / "cleanup_plan.json"
    with open(plan_file, 'w', encoding='utf-8') as f:
        json.dump(plan, f, ensure_ascii=False, indent=2)
    
    print(f"\n清理计划已保存到: {plan_file}")
    
    # 询问是否执行清理
    response = input("\n是否执行清理操作？(y/N): ").strip().lower()
    
    if response == 'y':
        print("\n开始执行清理操作...")
        cleanup_results = await cleanup_tool.run_full_cleanup()
        
        print("\n=== 清理完成报告 ===")
        print(f"总处理文件: {cleanup_results['summary']['total_processed']}")
        print(f"成功处理: {cleanup_results['summary']['total_successful']}")
        print(f"处理失败: {cleanup_results['summary']['total_failed']}")
        
        # 保存清理结果
        results_file = Path(base_dir) / "cleanup_results.json"
        with open(results_file, 'w', encoding='utf-8') as f:
            json.dump(cleanup_results, f, ensure_ascii=False, indent=2)
        
        print(f"\n清理结果已保存到: {results_file}")
    else:
        print("清理操作已取消")

if __name__ == "__main__":
    asyncio.run(main())
