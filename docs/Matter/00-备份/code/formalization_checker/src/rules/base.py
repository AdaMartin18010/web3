"""
规则基类

定义了所有规则必须实现的接口。
"""

from abc import ABC, abstractmethod
from typing import Dict, List, Any


class Rule(ABC):
    """
    规则基类
    
    所有规则必须继承此类并实现check方法。
    """
    
    def __init__(self, rule_id: str, name: str, severity: str):
        """
        初始化规则
        
        Args:
            rule_id: 规则ID，如 "SYM_001"
            name: 规则名称
            severity: 严重程度，可选值为 "ERROR", "WARNING", "INFO"
        """
        self.id = rule_id
        self.name = name
        self.severity = severity
    
    @abstractmethod
    def check(self, document: Dict[str, Any]) -> List[Dict[str, Any]]:
        """
        检查文档是否符合规则
        
        Args:
            document: 解析后的文档对象
            
        Returns:
            问题列表，每个问题是一个字典，包含以下字段：
            - rule_id: 规则ID
            - severity: 严重程度
            - message: 问题描述
            - location: 问题位置
            - suggestion: 改进建议
        """
        pass
    
    def create_issue(self, message: str, location: Dict[str, Any], suggestion: str = None) -> Dict[str, Any]:
        """
        创建问题记录
        
        Args:
            message: 问题描述
            location: 问题位置，包含行号、列号等信息
            suggestion: 改进建议
            
        Returns:
            问题记录字典
        """
        return {
            "rule_id": self.id,
            "name": self.name,
            "severity": self.severity,
            "message": message,
            "location": location,
            "suggestion": suggestion
        } 