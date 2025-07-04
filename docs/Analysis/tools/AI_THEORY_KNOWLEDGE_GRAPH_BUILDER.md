# AI理论知识图谱构建工具

## 1. 知识图谱架构设计

### 1.1 核心数据结构

**知识图谱节点**:

```python
@dataclass
class KnowledgeNode:
    """知识图谱节点"""
    id: str
    label: str
    node_type: str  # 'concept', 'theorem', 'method', 'application'
    properties: Dict[str, Any]
    confidence: float = 1.0
    created_at: datetime = field(default_factory=datetime.now)
    
    def update_property(self, key: str, value: Any):
        """更新属性"""
        self.properties[key] = value
```

**知识图谱边**:

```python
@dataclass
class KnowledgeEdge:
    """知识图谱边"""
    source_id: str
    target_id: str
    relationship_type: str  # 'is_a', 'part_of', 'depends_on', 'implements'
    properties: Dict[str, Any]
    weight: float = 1.0
    confidence: float = 1.0
```

### 1.2 知识图谱管理器

**知识图谱管理器**:

```python
class KnowledgeGraphManager:
    """知识图谱管理器"""
    
    def __init__(self):
        self.nodes: Dict[str, KnowledgeNode] = {}
        self.edges: List[KnowledgeEdge] = []
        self.node_index: Dict[str, List[str]] = {}
    
    def add_node(self, node: KnowledgeNode) -> bool:
        """添加节点"""
        if node.id in self.nodes:
            return False
        
        self.nodes[node.id] = node
        
        if node.node_type not in self.node_index:
            self.node_index[node.node_type] = []
        self.node_index[node.node_type].append(node.id)
        
        return True
    
    def add_edge(self, edge: KnowledgeEdge) -> bool:
        """添加边"""
        if edge.source_id not in self.nodes or edge.target_id not in self.nodes:
            return False
        
        self.edges.append(edge)
        return True
    
    def get_node(self, node_id: str) -> Optional[KnowledgeNode]:
        """获取节点"""
        return self.nodes.get(node_id)
    
    def get_neighbors(self, node_id: str) -> List[KnowledgeNode]:
        """获取邻居节点"""
        neighbors = []
        
        for edge in self.edges:
            if edge.source_id == node_id:
                neighbor = self.nodes.get(edge.target_id)
                if neighbor:
                    neighbors.append(neighbor)
            elif edge.target_id == node_id:
                neighbor = self.nodes.get(edge.source_id)
                if neighbor:
                    neighbors.append(neighbor)
        
        return neighbors
```

## 2. 知识提取与构建

### 2.1 文本知识提取器

**文本知识提取器**:

```python
class TextKnowledgeExtractor:
    """文本知识提取器"""
    
    def __init__(self):
        self.extraction_patterns = self._load_extraction_patterns()
    
    def extract_from_text(self, text: str) -> Dict[str, Any]:
        """从文本中提取知识"""
        extracted_knowledge = {
            'concepts': [],
            'relationships': [],
            'properties': []
        }
        
        # 提取概念
        concepts = self._extract_concepts(text)
        extracted_knowledge['concepts'] = concepts
        
        # 提取关系
        relationships = self._extract_relationships(text, concepts)
        extracted_knowledge['relationships'] = relationships
        
        return extracted_knowledge
    
    def _extract_concepts(self, text: str) -> List[Dict[str, Any]]:
        """提取概念"""
        concepts = []
        
        # 使用正则表达式提取概念
        concept_patterns = [
            r'定义\s*(\d+\.\d+)\s*\(([^)]+)\)',
            r'定理\s*(\d+\.\d+)\s*\(([^)]+)\)',
            r'([A-Z][a-z]+(?:\s+[A-Z][a-z]+)*)',
        ]
        
        for pattern in concept_patterns:
            matches = re.finditer(pattern, text)
            for match in matches:
                concept = {
                    'id': match.group(1) if len(match.groups()) > 1 else match.group(1),
                    'name': match.group(2) if len(match.groups()) > 1 else match.group(1),
                    'type': 'definition' if '定义' in pattern else 'theorem' if '定理' in pattern else 'concept',
                    'confidence': 0.8
                }
                concepts.append(concept)
        
        return concepts
    
    def _extract_relationships(self, text: str, concepts: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """提取关系"""
        relationships = []
        
        # 关系模式
        relationship_patterns = [
            (r'([^，。]+)是([^，。]+)', 'is_a'),
            (r'([^，。]+)包含([^，。]+)', 'contains'),
            (r'([^，。]+)依赖([^，。]+)', 'depends_on'),
        ]
        
        for pattern, rel_type in relationship_patterns:
            matches = re.finditer(pattern, text)
            for match in matches:
                source = match.group(1).strip()
                target = match.group(2).strip()
                
                source_concept = self._find_concept_by_name(source, concepts)
                target_concept = self._find_concept_by_name(target, concepts)
                
                if source_concept and target_concept:
                    relationship = {
                        'source': source_concept['id'],
                        'target': target_concept['id'],
                        'type': rel_type,
                        'confidence': 0.7
                    }
                    relationships.append(relationship)
        
        return relationships
    
    def _find_concept_by_name(self, name: str, concepts: List[Dict[str, Any]]) -> Optional[Dict[str, Any]]:
        """根据名称查找概念"""
        for concept in concepts:
            if concept['name'] == name or name in concept['name']:
                return concept
        return None
```

## 3. 知识图谱推理

### 3.1 路径推理器

**路径推理器**:

```python
class PathReasoner:
    """路径推理器"""
    
    def __init__(self, knowledge_graph: KnowledgeGraphManager):
        self.kg = knowledge_graph
        self.reasoning_rules = self._load_reasoning_rules()
    
    def infer_relationships(self, source_id: str, target_id: str) -> List[Dict[str, Any]]:
        """推理关系"""
        paths = self._find_paths(source_id, target_id)
        inferences = []
        
        for path in paths:
            inference = self._infer_from_path(path)
            if inference:
                inferences.append(inference)
        
        return inferences
    
    def _find_paths(self, source_id: str, target_id: str, max_depth: int = 5) -> List[List[KnowledgeEdge]]:
        """查找路径"""
        if source_id not in self.kg.nodes or target_id not in self.kg.nodes:
            return []
        
        visited = set()
        queue = [(source_id, [])]
        paths = []
        
        while queue and len(queue[0][1]) < max_depth:
            current_id, path = queue.pop(0)
            
            if current_id == target_id:
                paths.append(path)
                continue
            
            if current_id in visited:
                continue
            
            visited.add(current_id)
            
            for edge in self.kg.edges:
                if edge.source_id == current_id and edge.target_id not in visited:
                    new_path = path + [edge]
                    queue.append((edge.target_id, new_path))
                elif edge.target_id == current_id and edge.source_id not in visited:
                    new_path = path + [edge]
                    queue.append((edge.source_id, new_path))
        
        return paths
    
    def _infer_from_path(self, path: List[KnowledgeEdge]) -> Optional[Dict[str, Any]]:
        """从路径推理"""
        if not path:
            return None
        
        # 分析路径中的关系类型
        relationship_chain = [edge.relationship_type for edge in path]
        
        # 应用推理规则
        for rule in self.reasoning_rules:
            if self._matches_rule(relationship_chain, rule['pattern']):
                return {
                    'source': path[0].source_id,
                    'target': path[-1].target_id,
                    'inferred_type': rule['inference'],
                    'confidence': rule['confidence'],
                    'path': relationship_chain,
                    'reasoning_rule': rule['name']
                }
        
        return None
    
    def _matches_rule(self, chain: List[str], pattern: List[str]) -> bool:
        """检查是否匹配规则"""
        if len(chain) != len(pattern):
            return False
        
        for i, rel_type in enumerate(chain):
            if pattern[i] != '*' and pattern[i] != rel_type:
                return False
        
        return True
    
    def _load_reasoning_rules(self) -> List[Dict[str, Any]]:
        """加载推理规则"""
        return [
            {
                'name': 'transitive_is_a',
                'pattern': ['is_a', 'is_a'],
                'inference': 'is_a',
                'confidence': 0.8
            },
            {
                'name': 'composition_contains',
                'pattern': ['contains', 'contains'],
                'inference': 'contains',
                'confidence': 0.7
            }
        ]
```

## 4. 知识图谱可视化

### 4.1 图形可视化器

**图形可视化器**:

```python
class GraphVisualizer:
    """图形可视化器"""
    
    def __init__(self, knowledge_graph: KnowledgeGraphManager):
        self.kg = knowledge_graph
        self.node_colors = {
            'concept': '#4CAF50',
            'theorem': '#2196F3',
            'method': '#FF9800',
            'application': '#9C27B0'
        }
    
    def generate_visualization(self, output_path: str):
        """生成可视化"""
        import matplotlib.pyplot as plt
        import networkx as nx
        
        # 创建NetworkX图
        G = nx.Graph()
        
        # 添加节点
        for node_id, node in self.kg.nodes.items():
            G.add_node(node_id, label=node.label, type=node.node_type)
        
        # 添加边
        for edge in self.kg.edges:
            G.add_edge(edge.source_id, edge.target_id, 
                      type=edge.relationship_type, weight=edge.weight)
        
        # 设置布局
        pos = nx.spring_layout(G)
        
        # 绘制图
        plt.figure(figsize=(12, 8))
        
        # 绘制节点
        for node_type in self.node_colors:
            nodes = [node for node, data in G.nodes(data=True) if data['type'] == node_type]
            nx.draw_networkx_nodes(G, pos, nodelist=nodes, 
                                 node_color=self.node_colors[node_type],
                                 node_size=500, alpha=0.7)
        
        # 绘制边
        nx.draw_networkx_edges(G, pos, alpha=0.5, edge_color='gray')
        
        # 绘制标签
        labels = {node: data['label'] for node, data in G.nodes(data=True)}
        nx.draw_networkx_labels(G, pos, labels, font_size=8)
        
        plt.title("AI理论知识图谱")
        plt.axis('off')
        plt.tight_layout()
        plt.savefig(output_path, dpi=300, bbox_inches='tight')
        plt.close()
```

## 5. 知识图谱应用

### 5.1 知识问答系统

**知识问答系统**:

```python
class KnowledgeQASystem:
    """知识问答系统"""
    
    def __init__(self, knowledge_graph: KnowledgeGraphManager):
        self.kg = knowledge_graph
        self.question_patterns = self._load_question_patterns()
    
    def answer_question(self, question: str) -> Dict[str, Any]:
        """回答问题"""
        # 解析问题
        parsed_question = self._parse_question(question)
        
        if not parsed_question:
            return {
                'answer': '无法理解问题',
                'confidence': 0.0,
                'reasoning': []
            }
        
        # 查找答案
        answer = self._find_answer(parsed_question)
        
        return answer
    
    def _parse_question(self, question: str) -> Optional[Dict[str, Any]]:
        """解析问题"""
        question_lower = question.lower()
        
        for pattern in self.question_patterns:
            match = re.search(pattern['regex'], question_lower)
            if match:
                return {
                    'type': pattern['type'],
                    'entities': match.groups(),
                    'pattern': pattern
                }
        
        return None
    
    def _find_answer(self, parsed_question: Dict[str, Any]) -> Dict[str, Any]:
        """查找答案"""
        question_type = parsed_question['type']
        entities = parsed_question['entities']
        
        if question_type == 'definition':
            return self._find_definition(entities[0])
        elif question_type == 'relationship':
            return self._find_relationship(entities[0], entities[1])
        else:
            return {
                'answer': '不支持的问题类型',
                'confidence': 0.0,
                'reasoning': []
            }
    
    def _find_definition(self, concept_name: str) -> Dict[str, Any]:
        """查找定义"""
        # 查找概念节点
        concept = None
        for node_id, node in self.kg.nodes.items():
            if concept_name.lower() in node.label.lower():
                concept = node
                break
        
        if not concept:
            return {
                'answer': f'未找到概念 "{concept_name}" 的定义',
                'confidence': 0.0,
                'reasoning': []
            }
        
        # 查找定义属性
        definition = concept.get_property('definition', '')
        
        return {
            'answer': definition if definition else f'概念 "{concept_name}" 没有定义',
            'confidence': 0.8,
            'reasoning': [f'在知识图谱中找到概念: {concept.label}']
        }
    
    def _find_relationship(self, entity1: str, entity2: str) -> Dict[str, Any]:
        """查找关系"""
        # 查找实体
        entity1_node = self._find_node_by_name(entity1)
        entity2_node = self._find_node_by_name(entity2)
        
        if not entity1_node or not entity2_node:
            return {
                'answer': f'未找到实体 "{entity1}" 或 "{entity2}"',
                'confidence': 0.0,
                'reasoning': []
            }
        
        # 查找关系
        path = self.kg.find_path(entity1_node.id, entity2_node.id)
        
        if not path:
            return {
                'answer': f'未找到 "{entity1}" 和 "{entity2}" 之间的关系',
                'confidence': 0.0,
                'reasoning': []
            }
        
        # 构建关系描述
        relationship_desc = self._describe_path(path)
        
        return {
            'answer': relationship_desc,
            'confidence': 0.7,
            'reasoning': [f'通过路径分析找到关系: {[edge.relationship_type for edge in path]}']
        }
    
    def _find_node_by_name(self, name: str) -> Optional[KnowledgeNode]:
        """根据名称查找节点"""
        for node_id, node in self.kg.nodes.items():
            if name.lower() in node.label.lower():
                return node
        return None
    
    def _describe_path(self, path: List[KnowledgeEdge]) -> str:
        """描述路径"""
        if not path:
            return "无关系"
        
        descriptions = []
        for edge in path:
            source = self.kg.get_node(edge.source_id)
            target = self.kg.get_node(edge.target_id)
            
            if source and target:
                descriptions.append(f"{source.label} {edge.relationship_type} {target.label}")
        
        return " -> ".join(descriptions)
    
    def _load_question_patterns(self) -> List[Dict[str, Any]]:
        """加载问题模式"""
        return [
            {
                'type': 'definition',
                'regex': r'什么是(.+)',
                'description': '询问定义'
            },
            {
                'type': 'relationship',
                'regex': r'(.+)和(.+)有什么关系',
                'description': '询问关系'
            }
        ]
```

## 6. 使用示例

**主程序示例**:

```python
def main():
    """知识图谱构建示例"""
    print("=== AI理论知识图谱构建工具演示 ===")
    
    # 创建知识图谱管理器
    kg_manager = KnowledgeGraphManager()
    
    # 创建节点
    concept1 = KnowledgeNode(
        id="concept_1",
        label="智能系统",
        node_type="concept",
        properties={"definition": "能够感知、推理和行动的计算机系统"}
    )
    
    concept2 = KnowledgeNode(
        id="concept_2", 
        label="机器学习",
        node_type="method",
        properties={"definition": "通过数据训练模型的方法"}
    )
    
    concept3 = KnowledgeNode(
        id="concept_3",
        label="深度学习",
        node_type="method", 
        properties={"definition": "使用多层神经网络的机器学习方法"}
    )
    
    # 添加节点
    kg_manager.add_node(concept1)
    kg_manager.add_node(concept2)
    kg_manager.add_node(concept3)
    
    # 创建边
    edge1 = KnowledgeEdge(
        source_id="concept_2",
        target_id="concept_1",
        relationship_type="implements",
        properties={},
        weight=0.8
    )
    
    edge2 = KnowledgeEdge(
        source_id="concept_3",
        target_id="concept_2", 
        relationship_type="is_a",
        properties={},
        weight=0.9
    )
    
    # 添加边
    kg_manager.add_edge(edge1)
    kg_manager.add_edge(edge2)
    
    # 创建推理器
    reasoner = PathReasoner(kg_manager)
    
    # 推理关系
    inferences = reasoner.infer_relationships("concept_3", "concept_1")
    print(f"推理结果: {inferences}")
    
    # 创建问答系统
    qa_system = KnowledgeQASystem(kg_manager)
    
    # 回答问题
    question = "什么是智能系统？"
    answer = qa_system.answer_question(question)
    print(f"问题: {question}")
    print(f"答案: {answer}")
    
    # 创建可视化
    visualizer = GraphVisualizer(kg_manager)
    visualizer.generate_visualization("knowledge_graph.png")
    print("知识图谱已保存为 knowledge_graph.png")
    
    print("=== 演示完成 ===")

if __name__ == "__main__":
    main()
```

这个知识图谱构建工具提供了完整的知识图谱创建、管理和应用功能，包括知识提取、推理、可视化和问答系统等核心功能。
