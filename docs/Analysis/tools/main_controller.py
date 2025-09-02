#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
主控制脚本
协调多线程处理流程，加速Analysis目录完善
"""

import asyncio
import logging
from pathlib import Path
from datetime import datetime
import json
from typing import Dict, List

# 导入工具模块
from automated_enhancement import AutomatedDocumentEnhancer
from document_cleanup import DocumentCleanupTool
from document_refactor import DocumentRefactorTool

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('analysis_enhancement.log', encoding='utf-8'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

class AnalysisEnhancementController:
    """Analysis目录增强控制器"""
    
    def __init__(self, base_dir: str = "docs/Analysis", max_workers: int = 8):
        self.base_dir = Path(base_dir)
        self.max_workers = max_workers
        self.start_time = datetime.now()
        
        # 初始化工具
        self.enhancer = AutomatedDocumentEnhancer(base_dir, max_workers)
        self.cleanup_tool = DocumentCleanupTool(base_dir, max_workers)
        self.refactor_tool = DocumentRefactorTool(base_dir, max_workers)
        
        # 进度跟踪
        self.progress = {
            'phase': 'initialized',
            'completed_tasks': 0,
            'total_tasks': 0,
            'current_task': '',
            'errors': [],
            'warnings': []
        }
    
    async def run_full_enhancement_pipeline(self) -> Dict:
        """运行完整的增强流水线"""
        logger.info("开始运行完整的Analysis目录增强流水线")
        
        try:
            # 阶段1: 文档清理
            await self._run_cleanup_phase()
            
            # 阶段2: 文档重构
            await self._run_refactor_phase()
            
            # 阶段3: 文档增强
            await self._run_enhancement_phase()
            
            # 阶段4: 质量评估
            await self._run_quality_assessment_phase()
            
            # 生成最终报告
            final_report = await self._generate_final_report()
            
            logger.info("Analysis目录增强流水线完成")
            return final_report
            
        except Exception as e:
            logger.error(f"增强流水线执行失败: {e}")
            self.progress['errors'].append(str(e))
            raise
    
    async def _run_cleanup_phase(self):
        """运行清理阶段"""
        logger.info("=== 阶段1: 文档清理 ===")
        self.progress['phase'] = 'cleanup'
        self.progress['current_task'] = '文档清理'
        
        try:
            # 生成清理计划
            cleanup_plan = await self.cleanup_tool.generate_cleanup_plan()
            logger.info(f"清理计划: 删除{cleanup_plan['summary']['files_to_delete']}个文件，重命名{cleanup_plan['summary']['files_to_rename']}个文件")
            
            # 执行清理
            cleanup_results = await self.cleanup_tool.run_full_cleanup()
            logger.info(f"清理完成: 成功{cleanup_results['summary']['total_successful']}个，失败{cleanup_results['summary']['total_failed']}个")
            
            # 保存清理结果
            cleanup_file = self.base_dir / "cleanup_results.json"
            with open(cleanup_file, 'w', encoding='utf-8') as f:
                json.dump(cleanup_results, f, ensure_ascii=False, indent=2)
            
            self.progress['completed_tasks'] += 1
            
        except Exception as e:
            logger.error(f"清理阶段失败: {e}")
            self.progress['errors'].append(f"清理阶段: {e}")
            raise
    
    async def _run_refactor_phase(self):
        """运行重构阶段"""
        logger.info("=== 阶段2: 文档重构 ===")
        self.progress['phase'] = 'refactor'
        self.progress['current_task'] = '文档重构'
        
        try:
            # 定义重构任务
            refactor_tasks = [
                {
                    'file_path': self.base_dir / "01_Theoretical_Foundations/02_Cryptographic_Foundations/elliptic_curve_cryptography_web3.md",
                    'refactor_type': "elliptic_curve",
                    'priority': 1,
                    'target_quality': 90
                },
                {
                    'file_path': self.base_dir / "02_Core_Technologies/01_Blockchain_Fundamentals/blockchain_consensus_mechanisms_web3.md",
                    'refactor_type': "consensus_mechanism",
                    'priority': 1,
                    'target_quality': 90
                },
                {
                    'file_path': self.base_dir / "11_Advanced_Technologies/01_AI_Integration/ai_blockchain_integration_web3.md",
                    'refactor_type': "ai_integration",
                    'priority': 2,
                    'target_quality': 85
                },
                {
                    'file_path': self.base_dir / "12_Security_And_Verification/Security_And_Privacy/zero_knowledge_proof_theory_web3.md",
                    'refactor_type': "zero_knowledge",
                    'priority': 1,
                    'target_quality': 90
                }
            ]
            
            # 执行重构
            for task in refactor_tasks:
                if task['file_path'].exists():
                    logger.info(f"重构文档: {task['file_path']}")
                    success = await self.refactor_tool.refactor_document(
                        task['file_path'], 
                        task['refactor_type']
                    )
                    if success:
                        logger.info(f"重构成功: {task['file_path']}")
                    else:
                        logger.warning(f"重构失败: {task['file_path']}")
                        self.progress['warnings'].append(f"重构失败: {task['file_path']}")
                else:
                    logger.warning(f"文档不存在: {task['file_path']}")
                    self.progress['warnings'].append(f"文档不存在: {task['file_path']}")
            
            self.progress['completed_tasks'] += 1
            
        except Exception as e:
            logger.error(f"重构阶段失败: {e}")
            self.progress['errors'].append(f"重构阶段: {e}")
            raise
    
    async def _run_enhancement_phase(self):
        """运行增强阶段"""
        logger.info("=== 阶段3: 文档增强 ===")
        self.progress['phase'] = 'enhancement'
        self.progress['current_task'] = '文档增强'
        
        try:
            # 运行文档增强
            enhancement_results = await self.enhancer.run_full_enhancement()
            logger.info(f"增强完成: 总文档{enhancement_results['total_documents']}个，需要增强{enhancement_results['needs_enhancement']}个")
            
            # 保存增强结果
            enhancement_file = self.base_dir / "enhancement_results.json"
            with open(enhancement_file, 'w', encoding='utf-8') as f:
                json.dump(enhancement_results, f, ensure_ascii=False, indent=2)
            
            self.progress['completed_tasks'] += 1
            
        except Exception as e:
            logger.error(f"增强阶段失败: {e}")
            self.progress['errors'].append(f"增强阶段: {e}")
            raise
    
    async def _run_quality_assessment_phase(self):
        """运行质量评估阶段"""
        logger.info("=== 阶段4: 质量评估 ===")
        self.progress['phase'] = 'quality_assessment'
        self.progress['current_task'] = '质量评估'
        
        try:
            # 扫描所有文档进行质量评估
            all_files = list(self.base_dir.rglob('*.md'))
            quality_results = []
            
            for file_path in all_files:
                quality_result = await self.enhancer.analyze_document_quality(file_path)
                quality_results.append(quality_result)
            
            # 生成质量报告
            quality_report = {
                'timestamp': datetime.now().isoformat(),
                'total_documents': len(all_files),
                'quality_distribution': {
                    'excellent': len([r for r in quality_results if r['quality_score'] >= 90]),
                    'good': len([r for r in quality_results if 80 <= r['quality_score'] < 90]),
                    'fair': len([r for r in quality_results if 70 <= r['quality_score'] < 80]),
                    'poor': len([r for r in quality_results if r['quality_score'] < 70])
                },
                'average_score': sum(r['quality_score'] for r in quality_results) / len(quality_results),
                'detailed_results': quality_results
            }
            
            # 保存质量报告
            quality_file = self.base_dir / "quality_assessment.json"
            with open(quality_file, 'w', encoding='utf-8') as f:
                json.dump(quality_report, f, ensure_ascii=False, indent=2)
            
            logger.info(f"质量评估完成: 平均分数{quality_report['average_score']:.2f}")
            self.progress['completed_tasks'] += 1
            
        except Exception as e:
            logger.error(f"质量评估阶段失败: {e}")
            self.progress['errors'].append(f"质量评估阶段: {e}")
            raise
    
    async def _generate_final_report(self) -> Dict:
        """生成最终报告"""
        end_time = datetime.now()
        duration = end_time - self.start_time
        
        final_report = {
            'project': 'Analysis目录增强项目',
            'start_time': self.start_time.isoformat(),
            'end_time': end_time.isoformat(),
            'duration_seconds': duration.total_seconds(),
            'progress': self.progress,
            'summary': {
                'total_phases': 4,
                'completed_phases': self.progress['completed_tasks'],
                'success_rate': (self.progress['completed_tasks'] / 4) * 100,
                'total_errors': len(self.progress['errors']),
                'total_warnings': len(self.progress['warnings'])
            },
            'recommendations': self._generate_recommendations()
        }
        
        # 保存最终报告
        final_report_file = self.base_dir / "final_enhancement_report.json"
        with open(final_report_file, 'w', encoding='utf-8') as f:
            json.dump(final_report, f, ensure_ascii=False, indent=2)
        
        return final_report
    
    def _generate_recommendations(self) -> List[str]:
        """生成改进建议"""
        recommendations = []
        
        if self.progress['errors']:
            recommendations.append("需要解决所有错误以确保系统稳定性")
        
        if self.progress['warnings']:
            recommendations.append("建议处理警告以提高文档质量")
        
        if self.progress['completed_tasks'] < 4:
            recommendations.append("部分阶段未完成，建议重新运行")
        
        recommendations.extend([
            "定期运行质量评估以监控文档质量",
            "建立自动化测试流程",
            "实施持续集成机制",
            "建立文档维护标准"
        ])
        
        return recommendations
    
    async def run_parallel_enhancement(self):
        """并行运行增强任务"""
        logger.info("开始并行运行增强任务")
        
        try:
            # 并行执行清理和重构
            cleanup_task = asyncio.create_task(self._run_cleanup_phase())
            refactor_task = asyncio.create_task(self._run_refactor_phase())
            
            # 等待第一阶段完成
            await asyncio.gather(cleanup_task, refactor_task)
            
            # 并行执行增强和质量评估
            enhancement_task = asyncio.create_task(self._run_enhancement_phase())
            quality_task = asyncio.create_task(self._run_quality_assessment_phase())
            
            # 等待第二阶段完成
            await asyncio.gather(enhancement_task, quality_task)
            
            # 生成最终报告
            final_report = await self._generate_final_report()
            
            logger.info("并行增强任务完成")
            return final_report
            
        except Exception as e:
            logger.error(f"并行增强任务失败: {e}")
            raise

async def main():
    """主函数"""
    logger.info("启动Analysis目录增强控制器")
    
    # 创建控制器实例
    controller = AnalysisEnhancementController(max_workers=8)
    
    try:
        # 运行完整流水线
        final_report = await controller.run_full_enhancement_pipeline()
        
        # 输出结果
        print("\n" + "="*60)
        print("🎉 Analysis目录增强项目完成！")
        print("="*60)
        print(f"项目开始时间: {final_report['start_time']}")
        print(f"项目结束时间: {final_report['end_time']}")
        print(f"总耗时: {final_report['duration_seconds']:.2f} 秒")
        print(f"完成阶段: {final_report['summary']['completed_phases']}/{final_report['summary']['total_phases']}")
        print(f"成功率: {final_report['summary']['success_rate']:.1f}%")
        print(f"错误数量: {final_report['summary']['total_errors']}")
        print(f"警告数量: {final_report['summary']['total_warnings']}")
        
        print("\n📋 改进建议:")
        for i, rec in enumerate(final_report['recommendations'], 1):
            print(f"  {i}. {rec}")
        
        print(f"\n📊 详细报告已保存到: {controller.base_dir}/final_enhancement_report.json")
        
    except Exception as e:
        logger.error(f"主程序执行失败: {e}")
        print(f"\n❌ 程序执行失败: {e}")
        print("请检查日志文件获取详细信息")

if __name__ == "__main__":
    asyncio.run(main())
