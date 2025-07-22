"""
Markdown解析器

解析Markdown文档，提取数学符号、定理证明和假设条件等内容。
"""

import re
import logging
from typing import Dict, List, Any, Tuple

logger = logging.getLogger(__name__)


class MarkdownParser:
    """
    Markdown解析器
    
    解析Markdown文档，提取数学符号、定理证明和假设条件等内容。
    """
    
    def __init__(self):
        """初始化Markdown解析器"""
        # 数学表达式正则表达式
        self.inline_math_pattern = r'\$([^\$]+)\$'
        self.block_math_pattern = r'\$\$([\s\S]+?)\$\$'
        
        # 定理正则表达式
        self.theorem_pattern = r'(?:定理|Theorem)\s+(\d+(?:\.\d+)*)(?:\s*\(([^)]+)\))?[：:]\s*([\s\S]+?)(?=(?:证明|Proof)|$)'
        
        # 证明正则表达式
        self.proof_pattern = r'(?:证明|Proof)(?:\s*\(([^)]+)\))?[：:]\s*([\s\S]+?)(?=□|\\square|\\blacksquare|$)'
        
        # 假设正则表达式
        self.assumption_pattern = r'(?:假设|Assumption)\s+(\d+(?:\.\d+)*)(?:\s*\(([^)]+)\))?[：:]\s*([\s\S]+?)(?=(?:假设|Assumption)|(?:定理|Theorem)|$)'
        
        # 符号定义正则表达式
        self.symbol_def_pattern = r'(?:符号|Symbol)\s+(\S+)[：:]\s*([\s\S]+?)(?=(?:符号|Symbol)|(?:定理|Theorem)|(?:假设|Assumption)|$)'
    
    def parse(self, content: str) -> Dict[str, Any]:
        """
        解析Markdown文档
        
        Args:
            content: 文档内容
            
        Returns:
            解析后的文档对象
        """
        # 初始化结果
        document = {
            'definitions': [],
            'expressions': [],
            'theorems': [],
            'proofs': [],
            'assumptions': [],
            'contexts': []
        }
        
        # 解析数学表达式
        document['expressions'] = self._parse_expressions(content)
        
        # 解析符号定义
        document['definitions'] = self._parse_definitions(content)
        
        # 解析定理
        document['theorems'] = self._parse_theorems(content)
        
        # 解析证明
        document['proofs'] = self._parse_proofs(content)
        
        # 解析假设
        document['assumptions'] = self._parse_assumptions(content)
        
        # 解析上下文
        document['contexts'] = self._parse_contexts(content)
        
        return document
    
    def _parse_expressions(self, content: str) -> List[Dict[str, Any]]:
        """
        解析数学表达式
        
        Args:
            content: 文档内容
            
        Returns:
            数学表达式列表
        """
        expressions = []
        
        # 解析行内数学表达式
        for match in re.finditer(self.inline_math_pattern, content):
            expr = match.group(1)
            location = self._get_location(content, match.start(), match.end())
            expressions.append({
                'type': 'inline',
                'content': expr,
                'location': location
            })
        
        # 解析块级数学表达式
        for match in re.finditer(self.block_math_pattern, content):
            expr = match.group(1)
            location = self._get_location(content, match.start(), match.end())
            expressions.append({
                'type': 'block',
                'content': expr,
                'location': location
            })
        
        return expressions
    
    def _parse_definitions(self, content: str) -> List[Dict[str, Any]]:
        """
        解析符号定义
        
        Args:
            content: 文档内容
            
        Returns:
            符号定义列表
        """
        definitions = []
        
        # 解析显式符号定义
        for match in re.finditer(self.symbol_def_pattern, content):
            symbol = match.group(1)
            meaning = match.group(2).strip()
            location = self._get_location(content, match.start(), match.end())
            
            # 尝试从定义中提取符号类别
            category = None
            category_match = re.search(r'类别[：:]\s*(\w+)', meaning)
            if category_match:
                category = category_match.group(1)
            
            definitions.append({
                'symbol': symbol,
                'meaning': meaning,
                'category': category,
                'location': location
            })
        
        return definitions
    
    def _parse_theorems(self, content: str) -> List[Dict[str, Any]]:
        """
        解析定理
        
        Args:
            content: 文档内容
            
        Returns:
            定理列表
        """
        theorems = []
        
        for match in re.finditer(self.theorem_pattern, content):
            number = match.group(1)
            name = match.group(2) if match.group(2) else None
            statement = match.group(3).strip()
            location = self._get_location(content, match.start(), match.end())
            
            theorems.append({
                'number': number,
                'name': name,
                'statement': statement,
                'location': location
            })
        
        return theorems
    
    def _parse_proofs(self, content: str) -> List[Dict[str, Any]]:
        """
        解析证明
        
        Args:
            content: 文档内容
            
        Returns:
            证明列表
        """
        proofs = []
        
        for match in re.finditer(self.proof_pattern, content):
            theorem_ref = match.group(1) if match.group(1) else None
            steps = match.group(2).strip()
            location = self._get_location(content, match.start(), match.end())
            
            # 解析证明步骤
            proof_steps = []
            step_matches = re.finditer(r'(?:步骤|Step)\s+(\d+)[：:]\s*([\s\S]+?)(?=(?:步骤|Step)|□|\\square|\\blacksquare|$)', steps)
            
            for step_match in step_matches:
                step_number = step_match.group(1)
                step_content = step_match.group(2).strip()
                step_location = self._get_location(steps, step_match.start(), step_match.end())
                
                proof_steps.append({
                    'number': step_number,
                    'content': step_content,
                    'location': step_location
                })
            
            proofs.append({
                'theorem_ref': theorem_ref,
                'steps': proof_steps,
                'content': steps,
                'location': location
            })
        
        return proofs
    
    def _parse_assumptions(self, content: str) -> List[Dict[str, Any]]:
        """
        解析假设
        
        Args:
            content: 文档内容
            
        Returns:
            假设列表
        """
        assumptions = []
        
        for match in re.finditer(self.assumption_pattern, content):
            number = match.group(1)
            category = match.group(2) if match.group(2) else None
            statement = match.group(3).strip()
            location = self._get_location(content, match.start(), match.end())
            
            assumptions.append({
                'number': number,
                'category': category,
                'statement': statement,
                'location': location
            })
        
        return assumptions
    
    def _parse_contexts(self, content: str) -> List[Dict[str, Any]]:
        """
        解析上下文
        
        Args:
            content: 文档内容
            
        Returns:
            上下文列表
        """
        contexts = []
        
        # 解析章节作为上下文
        section_pattern = r'#+\s+(.+)'
        current_section = None
        current_section_start = 0
        
        for match in re.finditer(section_pattern, content):
            # 如果已有当前章节，则添加到上下文
            if current_section:
                section_content = content[current_section_start:match.start()]
                section_symbols = self._extract_symbols_from_context(section_content)
                
                contexts.append({
                    'type': 'section',
                    'name': current_section,
                    'content': section_content,
                    'symbols': section_symbols,
                    'location': self._get_location(content, current_section_start, match.start())
                })
            
            # 更新当前章节
            current_section = match.group(1)
            current_section_start = match.start()
        
        # 添加最后一个章节
        if current_section:
            section_content = content[current_section_start:]
            section_symbols = self._extract_symbols_from_context(section_content)
            
            contexts.append({
                'type': 'section',
                'name': current_section,
                'content': section_content,
                'symbols': section_symbols,
                'location': self._get_location(content, current_section_start, len(content))
            })
        
        return contexts
    
    def _extract_symbols_from_context(self, content: str) -> List[Dict[str, Any]]:
        """
        从上下文中提取符号使用
        
        Args:
            content: 上下文内容
            
        Returns:
            符号使用列表
        """
        symbols = []
        
        # 提取数学表达式中的符号
        expressions = self._parse_expressions(content)
        for expr in expressions:
            expr_content = expr['content']
            # 使用正则表达式提取符号
            symbol_matches = re.finditer(r'\\[a-zA-Z]+|[a-zA-Z]', expr_content)
            
            for symbol_match in symbol_matches:
                symbol = symbol_match.group(0)
                
                # 尝试从上下文推断符号含义
                meaning = None
                meaning_pattern = f'{symbol}\\s+(?:表示|代表|is|represents)\\s+(.+?)(?=\\.|,|，|。|$)'
                meaning_match = re.search(meaning_pattern, content)
                if meaning_match:
                    meaning = meaning_match.group(1).strip()
                
                symbols.append({
                    'symbol': symbol,
                    'meaning': meaning,
                    'location': expr['location']
                })
        
        return symbols
    
    def _get_location(self, content: str, start: int, end: int) -> Dict[str, Any]:
        """
        获取位置信息
        
        Args:
            content: 文档内容
            start: 开始位置
            end: 结束位置
            
        Returns:
            位置信息，包含行号和列号
        """
        # 计算行号和列号
        lines = content[:start].split('\n')
        line = len(lines)
        column = len(lines[-1]) + 1
        
        # 计算结束行号和列号
        end_lines = content[:end].split('\n')
        end_line = len(end_lines)
        end_column = len(end_lines[-1]) + 1
        
        return {
            'start': {
                'line': line,
                'column': column
            },
            'end': {
                'line': end_line,
                'column': end_column
            }
        } 