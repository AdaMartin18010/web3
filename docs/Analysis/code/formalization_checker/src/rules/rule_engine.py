"""
规则引擎

负责加载规则并执行检查。
"""

from typing import Dict, List, Any, Type
import logging

from .base import Rule
from .symbol_rules import SymbolDefinitionRule, SymbolConsistencyRule, SymbolNamingRule
from .proof_rules import ProofStructureRule, ProofStepClarityRule, ProofLogicRule
from .assumption_rules import AssumptionClarityRule, AssumptionClassificationRule, AssumptionVerificationRule

logger = logging.getLogger(__name__)


class RuleEngine:
    """
    规则引擎
    
    负责加载规则并执行检查。
    """
    
    def __init__(self, config: Dict[str, Any] = None):
        """
        初始化规则引擎
        
        Args:
            config: 配置信息，包含规则启用/禁用设置和严重程度过滤等
        """
        self.config = config or {}
        self.rules = self._load_rules()
    
    def _load_rules(self) -> List[Rule]:
        """
        加载规则
        
        根据配置加载启用的规则。
        
        Returns:
            规则列表
        """
        # 所有可用规则类
        available_rules = {
            # 符号规则
            "SYM_001": SymbolDefinitionRule,
            "SYM_002": SymbolConsistencyRule,
            "SYM_003": SymbolNamingRule,
            
            # 证明规则
            "PRF_001": ProofStructureRule,
            "PRF_002": ProofStepClarityRule,
            "PRF_003": ProofLogicRule,
            
            # 假设规则
            "ASM_001": AssumptionClarityRule,
            "ASM_002": AssumptionClassificationRule,
            "ASM_003": AssumptionVerificationRule
        }
        
        # 获取配置
        rules_config = self.config.get("rules", {})
        enable_all = rules_config.get("enable_all", True)
        exclude_rules = rules_config.get("exclude_rules", [])
        include_rules = rules_config.get("include_rules", [])
        
        # 确定要加载的规则
        rules_to_load = []
        
        if enable_all:
            # 加载所有规则，除了排除的
            for rule_id, rule_class in available_rules.items():
                if rule_id not in exclude_rules:
                    rules_to_load.append(rule_class())
        else:
            # 只加载明确包含的规则
            for rule_id in include_rules:
                if rule_id in available_rules:
                    rules_to_load.append(available_rules[rule_id]())
        
        logger.info(f"已加载 {len(rules_to_load)} 条规则")
        return rules_to_load
    
    def check(self, document: Dict[str, Any]) -> List[Dict[str, Any]]:
        """
        检查文档
        
        对文档应用所有启用的规则。
        
        Args:
            document: 解析后的文档对象
            
        Returns:
            问题列表
        """
        all_issues = []
        
        # 获取严重程度过滤
        severity_config = self.config.get("severity", {})
        min_severity = severity_config.get("min_level", "INFO")
        severity_levels = {"ERROR": 3, "WARNING": 2, "INFO": 1}
        min_severity_level = severity_levels.get(min_severity, 1)
        
        # 应用所有规则
        for rule in self.rules:
            try:
                issues = rule.check(document)
                
                # 过滤严重程度
                filtered_issues = []
                for issue in issues:
                    issue_severity = issue.get("severity", "INFO")
                    issue_level = severity_levels.get(issue_severity, 1)
                    if issue_level >= min_severity_level:
                        filtered_issues.append(issue)
                
                all_issues.extend(filtered_issues)
                
            except Exception as e:
                logger.error(f"应用规则 {rule.id} 时出错: {str(e)}")
        
        # 按严重程度排序
        all_issues.sort(key=lambda x: severity_levels.get(x.get("severity", "INFO"), 1), reverse=True)
        
        return all_issues 