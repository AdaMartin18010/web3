#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
快速启动脚本
用于启动Analysis目录增强流程
"""

import sys
import os
from pathlib import Path

# 添加当前目录到Python路径
current_dir = Path(__file__).parent
sys.path.insert(0, str(current_dir))

def main():
    """主函数"""
    print("🚀 启动Analysis目录增强流程")
    print("=" * 50)
    
    # 检查Python版本
    if sys.version_info < (3, 7):
        print("❌ 需要Python 3.7或更高版本")
        sys.exit(1)
    
    # 检查依赖
    try:
        import asyncio
        import aiofiles
        print("✅ 依赖检查通过")
    except ImportError as e:
        print(f"❌ 缺少依赖: {e}")
        print("请运行: pip install -r requirements.txt")
        sys.exit(1)
    
    # 检查工作目录
    work_dir = Path.cwd()
    if not (work_dir / "docs" / "Analysis").exists():
        print("❌ 请在项目根目录运行此脚本")
        sys.exit(1)
    
    print(f"✅ 工作目录: {work_dir}")
    
    # 启动增强流程
    try:
        from main_controller import main as run_enhancement
        print("\n🎯 开始执行增强流程...")
        asyncio.run(run_enhancement())
    except Exception as e:
        print(f"\n❌ 执行失败: {e}")
        print("请检查日志文件获取详细信息")
        sys.exit(1)

if __name__ == "__main__":
    main()
