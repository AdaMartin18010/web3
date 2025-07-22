#!/usr/bin/env python3
"""
Web3理论形式化检查器 - 主程序入口

该工具用于检查Web3理论文档中的数学符号使用、定理证明格式和假设条件的规范性。
"""

import os
import sys
import argparse
import yaml
import json
from pathlib import Path

# 导入内部模块
try:
    from src.parser import DocumentParser
    from src.rules import RuleEngine
    from src.reporter import Reporter, JsonReporter, MarkdownReporter, HtmlReporter
    from src.utils import get_version, setup_logging, load_config
    from src.fixer import Fixer
except ImportError:
    # 如果作为独立脚本运行，添加当前目录到路径
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from src.parser import DocumentParser
    from src.rules import RuleEngine
    from src.reporter import Reporter, JsonReporter, MarkdownReporter, HtmlReporter
    from src.utils import get_version, setup_logging, load_config
    from src.fixer import Fixer

# 设置日志
logger = setup_logging()

def parse_arguments():
    """解析命令行参数"""
    parser = argparse.ArgumentParser(
        description="Web3理论形式化检查器 - 检查Web3理论文档的形式化规范性"
    )
    
    parser.add_argument(
        "--version", action="version", version=f"Web3理论形式化检查器 v{get_version()}"
    )
    
    subparsers = parser.add_subparsers(dest="command", help="可用命令")
    
    # 检查单个文件
    check_parser = subparsers.add_parser("check", help="检查单个文档")
    check_parser.add_argument("--file", required=True, help="要检查的文档路径")
    check_parser.add_argument("--config", help="配置文件路径")
    check_parser.add_argument(
        "--report", choices=["simple", "detailed"], default="simple", help="报告详细程度"
    )
    check_parser.add_argument(
        "--format", choices=["text", "json", "markdown", "html"], default="text", help="输出格式"
    )
    check_parser.add_argument(
        "--output", help="输出文件路径，默认输出到控制台"
    )
    check_parser.add_argument(
        "--auto-fix", action="store_true", help="自动修正问题"
    )
    
    # 检查整个目录
    check_dir_parser = subparsers.add_parser("check-dir", help="检查整个目录")
    check_dir_parser.add_argument("--dir", required=True, help="要检查的目录路径")
    check_dir_parser.add_argument("--config", help="配置文件路径")
    check_dir_parser.add_argument(
        "--pattern", default="*.md", help="文件匹配模式，默认为 *.md"
    )
    check_dir_parser.add_argument(
        "--report", choices=["simple", "detailed"], default="simple", help="报告详细程度"
    )
    check_dir_parser.add_argument(
        "--format", choices=["text", "json", "markdown", "html"], default="text", help="输出格式"
    )
    check_dir_parser.add_argument(
        "--output", help="输出文件路径，默认输出到控制台"
    )
    check_dir_parser.add_argument(
        "--auto-fix", action="store_true", help="自动修正问题"
    )
    
    # 初始化配置
    init_parser = subparsers.add_parser("init", help="初始化配置文件")
    init_parser.add_argument(
        "--output", default=".web3-checker.yml", help="输出配置文件路径"
    )
    
    return parser.parse_args()

def create_default_config():
    """创建默认配置"""
    return {
        "rules": {
            "enable_all": True,
            "exclude_rules": []
        },
        "output": {
            "format": "text",
            "include_suggestions": True
        },
        "severity": {
            "min_level": "WARNING"
        }
    }

def init_config(output_path):
    """初始化配置文件"""
    config = create_default_config()
    
    with open(output_path, "w", encoding="utf-8") as f:
        yaml.dump(config, f, default_flow_style=False)
    
    print(f"配置文件已创建: {output_path}")

def get_reporter(format_type):
    """获取对应格式的报告生成器"""
    reporters = {
        "text": Reporter(),
        "json": JsonReporter(),
        "markdown": MarkdownReporter(),
        "html": HtmlReporter()
    }
    return reporters.get(format_type, Reporter())

def check_file(file_path, config, report_type, format_type, output_path, auto_fix):
    """检查单个文件"""
    try:
        # 解析文档
        parser = DocumentParser()
        document = parser.parse(file_path)
        
        # 执行规则检查
        engine = RuleEngine(config)
        issues = engine.check(document)
        
        # 生成报告
        reporter = get_reporter(format_type)
        report = reporter.generate(issues, document, report_type)
        
        # 输出报告
        if output_path:
            with open(output_path, "w", encoding="utf-8") as f:
                f.write(report)
            print(f"报告已保存到: {output_path}")
        else:
            print(report)
        
        # 自动修正
        if auto_fix and issues:
            fixer = Fixer()
            fixed_document = fixer.fix(document, issues)
            with open(file_path, "w", encoding="utf-8") as f:
                f.write(fixed_document)
            print(f"文档已修正: {file_path}")
        
        return len(issues) == 0
    
    except Exception as e:
        logger.error(f"检查文件 {file_path} 时出错: {str(e)}")
        return False

def check_directory(dir_path, pattern, config, report_type, format_type, output_path, auto_fix):
    """检查整个目录"""
    try:
        # 获取匹配的文件
        files = list(Path(dir_path).glob(pattern))
        
        if not files:
            print(f"目录 {dir_path} 中没有找到匹配 {pattern} 的文件")
            return True
        
        # 检查每个文件
        all_issues = {}
        for file_path in files:
            # 解析文档
            parser = DocumentParser()
            document = parser.parse(str(file_path))
            
            # 执行规则检查
            engine = RuleEngine(config)
            issues = engine.check(document)
            
            if issues:
                all_issues[str(file_path)] = issues
            
            # 自动修正
            if auto_fix and issues:
                fixer = Fixer()
                fixed_document = fixer.fix(document, issues)
                with open(file_path, "w", encoding="utf-8") as f:
                    f.write(fixed_document)
                print(f"文档已修正: {file_path}")
        
        # 生成汇总报告
        reporter = get_reporter(format_type)
        report = reporter.generate_summary(all_issues, report_type)
        
        # 输出报告
        if output_path:
            with open(output_path, "w", encoding="utf-8") as f:
                f.write(report)
            print(f"报告已保存到: {output_path}")
        else:
            print(report)
        
        return len(all_issues) == 0
    
    except Exception as e:
        logger.error(f"检查目录 {dir_path} 时出错: {str(e)}")
        return False

def main():
    """主函数"""
    args = parse_arguments()
    
    # 初始化配置
    if args.command == "init":
        init_config(args.output)
        return 0
    
    # 加载配置
    config_path = args.config if hasattr(args, "config") and args.config else ".web3-checker.yml"
    config = load_config(config_path) if os.path.exists(config_path) else create_default_config()
    
    # 执行命令
    if args.command == "check":
        success = check_file(
            args.file,
            config,
            args.report,
            args.format,
            args.output,
            args.auto_fix
        )
    elif args.command == "check-dir":
        success = check_directory(
            args.dir,
            args.pattern,
            config,
            args.report,
            args.format,
            args.output,
            args.auto_fix
        )
    else:
        print("请指定要执行的命令。使用 --help 查看帮助。")
        return 1
    
    return 0 if success else 1

if __name__ == "__main__":
    sys.exit(main()) 