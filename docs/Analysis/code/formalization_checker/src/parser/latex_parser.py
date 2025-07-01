"""
LaTeX解析器

解析LaTeX文档，提取数学符号、定理证明和假设条件等内容。
"""

import re
import logging
from typing import Dict, List, Any

logger = logging.getLogger(__name__)


class LatexParser:
    """
    LaTeX解析器
    
    解析LaTeX文档，提取数学符号、定理证明和假设条件等内容。
    """
    
    def __init__(self):
        """初始化LaTeX解析器"""
        # 数学环境正则表达式
        self.inline_math_pattern = r'\$([^\$]+)\$'
        self.display_math_pattern = r'\\\[([\s\S]+?)\\\]'
        self.equation_pattern = r'\\begin\{equation\}([\s\S]+?)\\end\{equation\}'
        self.equation_star_pattern = r'\\begin\{equation\*\}([\s\S]+?)\\end\{equation\*\}'
        self.align_pattern = r'\\begin\{align\}([\s\S]+?)\\end\{align\}'
        self.align_star_pattern = r'\\begin\{align\*\}([\s\S]+?)\\end\{align\*\}'
        
        # 定理环境正则表达式
        self.theorem_pattern = r'\\begin\{theorem\}(?:\[([^\]]+)\])?(?:\{([^\}]+)\})?([\s\S]+?)\\end\{theorem\}'
        self.lemma_pattern = r'\\begin\{lemma\}(?:\[([^\]]+)\])?(?:\{([^\}]+)\})?([\s\S]+?)\\end\{lemma\}'
        self.proposition_pattern = r'\\begin\{proposition\}(?:\[([^\]]+)\])?(?:\{([^\}]+)\})?([\s\S]+?)\\end\{proposition\}'
        self.corollary_pattern = r'\\begin\{corollary\}(?:\[([^\]]+)\])?(?:\{([^\}]+)\})?([\s\S]+?)\\end\{corollary\}'
        
        # 证明环境正则表达式
        self.proof_pattern = r'\\begin\{proof\}(?:\[([^\]]+)\])?([\s\S]+?)\\end\{proof\}'
        
        # 假设环境正则表达式
        self.assumption_pattern = r'\\begin\{assumption\}(?:\[([^\]]+)\])?(?:\{([^\}]+)\})?([\s\S]+?)\\end\{assumption\}'
        self.hypothesis_pattern = r'\\begin\{hypothesis\}(?:\[([^\]]+)\])?(?:\{([^\}]+)\})?([\s\S]+?)\\end\{hypothesis\}'
        
        # 符号定义正则表达式
        self.newcommand_pattern = r'\\newcommand\{\\([a-zA-Z]+)\}(?:\[(\d+)\])?\{([\s\S]+?)\}'
        self.def_pattern = r'\\def\\([a-zA-Z]+)(?:#(\d+))?\{([\s\S]+?)\}'
    
    def parse(self, content: str) -> Dict[str, Any]:
        """
        解析LaTeX文档
        
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
        
        # 解析显示数学表达式
        for pattern, expr_type in [
            (self.display_math_pattern, 'display'),
            (self.equation_pattern, 'equation'),
            (self.equation_star_pattern, 'equation*'),
            (self.align_pattern, 'align'),
            (self.align_star_pattern, 'align*')
        ]:
            for match in re.finditer(pattern, content):
                expr = match.group(1)
                location = self._get_location(content, match.start(), match.end())
                expressions.append({
                    'type': expr_type,
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
        
        # 解析 \newcommand 定义
        for match in re.finditer(self.newcommand_pattern, content):
            symbol = match.group(1)
            args = match.group(2)
            meaning = match.group(3)
            location = self._get_location(content, match.start(), match.end())
            
            definitions.append({
                'symbol': f'\\{symbol}',
                'meaning': meaning,
                'args': args,
                'category': 'command',
                'location': location
            })
        
        # 解析 \def 定义
        for match in re.finditer(self.def_pattern, content):
            symbol = match.group(1)
            args = match.group(2)
            meaning = match.group(3)
            location = self._get_location(content, match.start(), match.end())
            
            definitions.append({
                'symbol': f'\\{symbol}',
                'meaning': meaning,
                'args': args,
                'category': 'command',
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
        
        # 解析各种定理环境
        for pattern, theorem_type in [
            (self.theorem_pattern, 'theorem'),
            (self.lemma_pattern, 'lemma'),
            (self.proposition_pattern, 'proposition'),
            (self.corollary_pattern, 'corollary')
        ]:
            for match in re.finditer(pattern, content):
                label = match.group(1)
                name = match.group(2)
                statement = match.group(3).strip()
                location = self._get_location(content, match.start(), match.end())
                
                # 提取定理编号
                number = None
                number_match = re.search(r'\\label\{([^}]+)\}', statement)
                if number_match:
                    number = number_match.group(1)
                    # 移除 \label 命令
                    statement = re.sub(r'\\label\{[^}]+\}', '', statement).strip()
                
                theorems.append({
                    'type': theorem_type,
                    'number': number,
                    'label': label,
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
            theorem_ref = match.group(1)
            steps = match.group(2).strip()
            location = self._get_location(content, match.start(), match.end())
            
            # 解析证明步骤
            proof_steps = []
            step_matches = re.finditer(r'\\item\s+([\s\S]+?)(?=\\item|$)', steps)
            
            for i, step_match in enumerate(step_matches, 1):
                step_content = step_match.group(1).strip()
                step_location = self._get_location(steps, step_match.start(), step_match.end())
                
                proof_steps.append({
                    'number': str(i),
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
        
        # 解析各种假设环境
        for pattern, assumption_type in [
            (self.assumption_pattern, 'assumption'),
            (self.hypothesis_pattern, 'hypothesis')
        ]:
            for match in re.finditer(pattern, content):
                label = match.group(1)
                category = match.group(2)
                statement = match.group(3).strip()
                location = self._get_location(content, match.start(), match.end())
                
                # 提取假设编号
                number = None
                number_match = re.search(r'\\label\{([^}]+)\}', statement)
                if number_match:
                    number = number_match.group(1)
                    # 移除 \label 命令
                    statement = re.sub(r'\\label\{[^}]+\}', '', statement).strip()
                
                assumptions.append({
                    'type': assumption_type,
                    'number': number,
                    'label': label,
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
        section_patterns = [
            (r'\\chapter(?:\*)?(?:\[([^\]]+)\])?\{([^}]+)\}', 'chapter'),
            (r'\\section(?:\*)?(?:\[([^\]]+)\])?\{([^}]+)\}', 'section'),
            (r'\\subsection(?:\*)?(?:\[([^\]]+)\])?\{([^}]+)\}', 'subsection'),
            (r'\\subsubsection(?:\*)?(?:\[([^\]]+)\])?\{([^}]+)\}', 'subsubsection')
        ]
        
        # 按照章节命令在文档中的位置排序
        section_matches = []
        for pattern, section_type in section_patterns:
            for match in re.finditer(pattern, content):
                section_matches.append((match, section_type))
        
        # 按照位置排序
        section_matches.sort(key=lambda x: x[0].start())
        
        # 处理每个章节
        current_section = None
        current_section_type = None
        current_section_start = 0
        
        for match, section_type in section_matches:
            # 如果已有当前章节，则添加到上下文
            if current_section:
                section_content = content[current_section_start:match.start()]
                section_symbols = self._extract_symbols_from_context(section_content)
                
                contexts.append({
                    'type': current_section_type,
                    'name': current_section,
                    'content': section_content,
                    'symbols': section_symbols,
                    'location': self._get_location(content, current_section_start, match.start())
                })
            
            # 更新当前章节
            short_title = match.group(1) if match.group(1) else None
            title = match.group(2)
            current_section = title
            current_section_type = section_type
            current_section_start = match.start()
        
        # 添加最后一个章节
        if current_section:
            section_content = content[current_section_start:]
            section_symbols = self._extract_symbols_from_context(section_content)
            
            contexts.append({
                'type': current_section_type,
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
            # 匹配 LaTeX 命令和单个字母
            symbol_matches = re.finditer(r'\\[a-zA-Z]+|[a-zA-Z]', expr_content)
            
            for symbol_match in symbol_matches:
                symbol = symbol_match.group(0)
                
                # 尝试从上下文推断符号含义
                meaning = None
                if symbol.startswith('\\'):
                    # 对于 LaTeX 命令，查找注释或附近的文本
                    meaning_pattern = f'{symbol}\\s+(?:表示|代表|is|represents)\\s+(.+?)(?=\\.|,|，|。|$)'
                    meaning_match = re.search(meaning_pattern, content)
                    if meaning_match:
                        meaning = meaning_match.group(1).strip()
                else:
                    # 对于单个字母，查找附近的文本
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