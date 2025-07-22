"""
符号规则

检查数学符号的定义和使用是否符合规范。
"""

import re
from typing import Dict, List, Any

from .base import Rule


class SymbolDefinitionRule(Rule):
    """
    符号定义规则
    
    检查所有使用的符号是否都有明确的定义。
    """
    
    def __init__(self):
        super().__init__("SYM_001", "符号定义规则", "ERROR")
    
    def check(self, document: Dict[str, Any]) -> List[Dict[str, Any]]:
        """
        检查文档中的符号定义
        
        Args:
            document: 解析后的文档对象
            
        Returns:
            问题列表
        """
        issues = []
        
        # 获取文档中定义的所有符号
        defined_symbols = self._extract_defined_symbols(document)
        
        # 获取文档中使用的所有符号
        used_symbols = self._extract_used_symbols(document)
        
        # 检查是否有未定义的符号
        for symbol, locations in used_symbols.items():
            if symbol not in defined_symbols:
                for location in locations:
                    issues.append(self.create_issue(
                        message=f"符号 '{symbol}' 在使用前未定义",
                        location=location,
                        suggestion=f"在使用前添加符号 '{symbol}' 的明确定义"
                    ))
        
        return issues
    
    def _extract_defined_symbols(self, document: Dict[str, Any]) -> Dict[str, List[Dict[str, Any]]]:
        """
        提取文档中定义的所有符号
        
        Args:
            document: 解析后的文档对象
            
        Returns:
            符号到定义位置列表的映射
        """
        defined_symbols = {}
        
        # 检查定义部分
        definitions = document.get("definitions", [])
        for definition in definitions:
            symbol = definition.get("symbol")
            if symbol:
                if symbol not in defined_symbols:
                    defined_symbols[symbol] = []
                defined_symbols[symbol].append(definition.get("location", {}))
        
        return defined_symbols
    
    def _extract_used_symbols(self, document: Dict[str, Any]) -> Dict[str, List[Dict[str, Any]]]:
        """
        提取文档中使用的所有符号
        
        Args:
            document: 解析后的文档对象
            
        Returns:
            符号到使用位置列表的映射
        """
        used_symbols = {}
        
        # 检查数学表达式
        expressions = document.get("expressions", [])
        for expression in expressions:
            content = expression.get("content", "")
            location = expression.get("location", {})
            
            # 使用正则表达式提取符号
            # 这里使用简单的正则，实际应用中可能需要更复杂的解析
            symbols = re.findall(r'\\[a-zA-Z]+|[a-zA-Z]', content)
            
            for symbol in symbols:
                if symbol not in used_symbols:
                    used_symbols[symbol] = []
                used_symbols[symbol].append(location)
        
        return used_symbols


class SymbolConsistencyRule(Rule):
    """
    符号一致性规则
    
    检查符号在整个文档中的使用是否一致。
    """
    
    def __init__(self):
        super().__init__("SYM_002", "符号一致性规则", "WARNING")
    
    def check(self, document: Dict[str, Any]) -> List[Dict[str, Any]]:
        """
        检查文档中的符号一致性
        
        Args:
            document: 解析后的文档对象
            
        Returns:
            问题列表
        """
        issues = []
        
        # 获取符号定义
        symbol_definitions = {}
        definitions = document.get("definitions", [])
        for definition in definitions:
            symbol = definition.get("symbol")
            meaning = definition.get("meaning")
            if symbol and meaning:
                if symbol in symbol_definitions and symbol_definitions[symbol] != meaning:
                    issues.append(self.create_issue(
                        message=f"符号 '{symbol}' 有多个不同的定义",
                        location=definition.get("location", {}),
                        suggestion=f"确保符号 '{symbol}' 在整个文档中具有一致的定义"
                    ))
                else:
                    symbol_definitions[symbol] = meaning
        
        # 检查符号的上下文一致性
        contexts = document.get("contexts", [])
        for context in contexts:
            symbols = context.get("symbols", [])
            for symbol_usage in symbols:
                symbol = symbol_usage.get("symbol")
                context_meaning = symbol_usage.get("meaning")
                if symbol in symbol_definitions and context_meaning and symbol_definitions[symbol] != context_meaning:
                    issues.append(self.create_issue(
                        message=f"符号 '{symbol}' 在此上下文中的使用与其定义不一致",
                        location=symbol_usage.get("location", {}),
                        suggestion=f"确保符号 '{symbol}' 的使用与其定义一致，或明确说明上下文差异"
                    ))
        
        return issues


class SymbolNamingRule(Rule):
    """
    符号命名规则
    
    检查符号命名是否符合规范。
    """
    
    def __init__(self):
        super().__init__("SYM_003", "符号命名规则", "INFO")
    
    def check(self, document: Dict[str, Any]) -> List[Dict[str, Any]]:
        """
        检查文档中的符号命名
        
        Args:
            document: 解析后的文档对象
            
        Returns:
            问题列表
        """
        issues = []
        
        # 符号命名约定
        naming_conventions = {
            "sets": r'^[A-Z]$',  # 大写字母表示集合
            "elements": r'^[a-z]$',  # 小写字母表示元素
            "functions": r'^[a-z]([a-z]|[A-Z])*$',  # 函数名以小写字母开头
            "constants": r'^[A-Z]_[A-Z0-9_]+$',  # 常量使用大写字母和下划线
        }
        
        # 检查符号定义
        definitions = document.get("definitions", [])
        for definition in definitions:
            symbol = definition.get("symbol")
            category = definition.get("category")
            
            if symbol and category and category in naming_conventions:
                pattern = naming_conventions[category]
                if not re.match(pattern, symbol):
                    issues.append(self.create_issue(
                        message=f"符号 '{symbol}' 的命名不符合 {category} 类别的命名约定",
                        location=definition.get("location", {}),
                        suggestion=f"考虑重命名符号以符合约定: {pattern}"
                    ))
        
        return issues 