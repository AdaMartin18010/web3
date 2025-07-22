"""
文档解析器

负责解析文档内容，识别数学符号、定理证明和假设条件等内容。
"""

import os
import logging
from typing import Dict, Any

from .markdown_parser import MarkdownParser
from .latex_parser import LatexParser

logger = logging.getLogger(__name__)


class DocumentParser:
    """
    文档解析器
    
    根据文件类型选择合适的解析器解析文档内容。
    """
    
    def __init__(self):
        """初始化文档解析器"""
        self.parsers = {
            '.md': MarkdownParser(),
            '.markdown': MarkdownParser(),
            '.tex': LatexParser()
        }
    
    def parse(self, file_path: str) -> Dict[str, Any]:
        """
        解析文档
        
        Args:
            file_path: 文档路径
            
        Returns:
            解析后的文档对象，包含以下字段：
            - file_path: 文档路径
            - content: 原始内容
            - definitions: 符号定义列表
            - expressions: 数学表达式列表
            - theorems: 定理列表
            - proofs: 证明列表
            - assumptions: 假设列表
            - contexts: 上下文列表
        """
        try:
            # 获取文件扩展名
            _, ext = os.path.splitext(file_path)
            
            # 选择合适的解析器
            parser = self.parsers.get(ext.lower())
            if not parser:
                logger.warning(f"不支持的文件类型: {ext}，将使用Markdown解析器")
                parser = MarkdownParser()
            
            # 读取文件内容
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 解析文档
            document = parser.parse(content)
            
            # 添加文件路径
            document['file_path'] = file_path
            document['content'] = content
            
            return document
            
        except Exception as e:
            logger.error(f"解析文档 {file_path} 时出错: {str(e)}")
            # 返回空文档
            return {
                'file_path': file_path,
                'content': '',
                'definitions': [],
                'expressions': [],
                'theorems': [],
                'proofs': [],
                'assumptions': [],
                'contexts': [],
                'parse_error': str(e)
            } 