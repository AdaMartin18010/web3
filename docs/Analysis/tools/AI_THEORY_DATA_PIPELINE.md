# AI理论数据管道工具

## 1. 数据管道架构

### 1.1 管道组件基类

**管道组件基类**:

```python
from abc import ABC, abstractmethod
from typing import Any, Dict, List, Optional
from dataclasses import dataclass, field
from datetime import datetime
import logging

@dataclass
class PipelineContext:
    """管道上下文"""
    data: Dict[str, Any] = field(default_factory=dict)
    metadata: Dict[str, Any] = field(default_factory=dict)
    timestamp: datetime = field(default_factory=datetime.now)
    
    def get_data(self, key: str, default: Any = None) -> Any:
        """获取数据"""
        return self.data.get(key, default)
    
    def set_data(self, key: str, value: Any):
        """设置数据"""
        self.data[key] = value
    
    def get_metadata(self, key: str, default: Any = None) -> Any:
        """获取元数据"""
        return self.metadata.get(key, default)
    
    def set_metadata(self, key: str, value: Any):
        """设置元数据"""
        self.metadata[key] = value

class PipelineComponent(ABC):
    """管道组件基类"""
    
    def __init__(self, name: str, config: Dict[str, Any] = None):
        self.name = name
        self.config = config or {}
        self.logger = logging.getLogger(f"pipeline.{name}")
    
    @abstractmethod
    def process(self, context: PipelineContext) -> PipelineContext:
        """处理数据"""
        pass
    
    def validate_input(self, context: PipelineContext) -> bool:
        """验证输入"""
        return True
    
    def validate_output(self, context: PipelineContext) -> bool:
        """验证输出"""
        return True
```

### 1.2 数据管道管理器

**数据管道管理器**:

```python
class DataPipeline:
    """数据管道管理器"""
    
    def __init__(self, name: str):
        self.name = name
        self.components: List[PipelineComponent] = []
        self.logger = logging.getLogger(f"pipeline.{name}")
        self.execution_history: List[Dict[str, Any]] = []
    
    def add_component(self, component: PipelineComponent):
        """添加组件"""
        self.components.append(component)
        self.logger.info(f"添加组件: {component.name}")
    
    def execute(self, initial_data: Dict[str, Any] = None) -> PipelineContext:
        """执行管道"""
        self.logger.info(f"开始执行管道: {self.name}")
        
        # 创建上下文
        context = PipelineContext(data=initial_data or {})
        context.set_metadata('pipeline_name', self.name)
        context.set_metadata('start_time', datetime.now())
        
        execution_record = {
            'pipeline_name': self.name,
            'start_time': context.timestamp,
            'components': [],
            'status': 'running'
        }
        
        try:
            # 执行每个组件
            for i, component in enumerate(self.components):
                self.logger.info(f"执行组件 {i+1}/{len(self.components)}: {component.name}")
                
                component_start = datetime.now()
                
                # 验证输入
                if not component.validate_input(context):
                    raise ValueError(f"组件 {component.name} 输入验证失败")
                
                # 处理数据
                context = component.process(context)
                
                # 验证输出
                if not component.validate_output(context):
                    raise ValueError(f"组件 {component.name} 输出验证失败")
                
                component_end = datetime.now()
                
                # 记录组件执行
                execution_record['components'].append({
                    'name': component.name,
                    'start_time': component_start,
                    'end_time': component_end,
                    'duration': (component_end - component_start).total_seconds(),
                    'status': 'success'
                })
                
                self.logger.info(f"组件 {component.name} 执行完成")
            
            # 完成执行
            context.set_metadata('end_time', datetime.now())
            context.set_metadata('status', 'success')
            
            execution_record['end_time'] = context.timestamp
            execution_record['status'] = 'success'
            
            self.logger.info(f"管道 {self.name} 执行完成")
            
        except Exception as e:
            self.logger.error(f"管道执行失败: {e}")
            context.set_metadata('error', str(e))
            context.set_metadata('status', 'failed')
            
            execution_record['end_time'] = datetime.now()
            execution_record['status'] = 'failed'
            execution_record['error'] = str(e)
            
            raise
        
        finally:
            # 记录执行历史
            self.execution_history.append(execution_record)
        
        return context
    
    def get_execution_summary(self) -> Dict[str, Any]:
        """获取执行摘要"""
        if not self.execution_history:
            return {}
        
        total_executions = len(self.execution_history)
        successful_executions = len([r for r in self.execution_history if r['status'] == 'success'])
        
        return {
            'total_executions': total_executions,
            'successful_executions': successful_executions,
            'success_rate': successful_executions / total_executions if total_executions > 0 else 0,
            'last_execution': self.execution_history[-1] if self.execution_history else None
        }
```

## 2. 数据源组件

### 2.1 文件数据源

**文件数据源组件**:

```python
class FileDataSource(PipelineComponent):
    """文件数据源组件"""
    
    def __init__(self, name: str, file_path: str, file_type: str = 'json'):
        super().__init__(name)
        self.file_path = file_path
        self.file_type = file_type
        self.config = {
            'file_path': file_path,
            'file_type': file_type
        }
    
    def process(self, context: PipelineContext) -> PipelineContext:
        """处理文件数据"""
        self.logger.info(f"读取文件: {self.file_path}")
        
        try:
            if self.file_type == 'json':
                data = self._read_json_file()
            elif self.file_type == 'csv':
                data = self._read_csv_file()
            elif self.file_type == 'txt':
                data = self._read_text_file()
            else:
                raise ValueError(f"不支持的文件类型: {self.file_type}")
            
            # 设置数据到上下文
            context.set_data('raw_data', data)
            context.set_metadata('source_file', self.file_path)
            context.set_metadata('data_size', len(data) if isinstance(data, list) else 1)
            
            self.logger.info(f"成功读取 {self.file_path}，数据大小: {context.get_metadata('data_size')}")
            
        except Exception as e:
            self.logger.error(f"读取文件失败: {e}")
            raise
        
        return context
    
    def _read_json_file(self) -> Any:
        """读取JSON文件"""
        import json
        with open(self.file_path, 'r', encoding='utf-8') as f:
            return json.load(f)
    
    def _read_csv_file(self) -> List[Dict[str, Any]]:
        """读取CSV文件"""
        import csv
        data = []
        with open(self.file_path, 'r', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                data.append(row)
        return data
    
    def _read_text_file(self) -> str:
        """读取文本文件"""
        with open(self.file_path, 'r', encoding='utf-8') as f:
            return f.read()
    
    def validate_input(self, context: PipelineContext) -> bool:
        """验证输入"""
        import os
        return os.path.exists(self.file_path)
```

## 3. 数据处理组件

### 3.1 数据清洗组件

**数据清洗组件**:

```python
class DataCleaningComponent(PipelineComponent):
    """数据清洗组件"""
    
    def __init__(self, name: str, cleaning_rules: Dict[str, Any] = None):
        super().__init__(name)
        self.cleaning_rules = cleaning_rules or {}
        self.config = {'cleaning_rules': cleaning_rules}
    
    def process(self, context: PipelineContext) -> PipelineContext:
        """处理数据清洗"""
        raw_data = context.get_data('raw_data')
        
        if not raw_data:
            self.logger.warning("没有原始数据需要清洗")
            return context
        
        self.logger.info(f"开始数据清洗，规则: {self.cleaning_rules}")
        
        try:
            if isinstance(raw_data, list):
                cleaned_data = self._clean_list_data(raw_data)
            else:
                cleaned_data = self._clean_single_data(raw_data)
            
            # 设置清洗后的数据
            context.set_data('cleaned_data', cleaned_data)
            context.set_metadata('cleaning_applied', True)
            context.set_metadata('cleaned_data_size', len(cleaned_data) if isinstance(cleaned_data, list) else 1)
            
            self.logger.info(f"数据清洗完成，清洗后数据大小: {context.get_metadata('cleaned_data_size')}")
            
        except Exception as e:
            self.logger.error(f"数据清洗失败: {e}")
            raise
        
        return context
    
    def _clean_list_data(self, data: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """清洗列表数据"""
        cleaned_data = []
        
        for item in data:
            cleaned_item = self._clean_single_data(item)
            if cleaned_item is not None:
                cleaned_data.append(cleaned_item)
        
        return cleaned_data
    
    def _clean_single_data(self, data: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        """清洗单个数据项"""
        if not isinstance(data, dict):
            return None
        
        cleaned_data = {}
        
        for key, value in data.items():
            # 应用清洗规则
            cleaned_value = self._apply_cleaning_rules(key, value)
            
            if cleaned_value is not None:
                cleaned_data[key] = cleaned_value
        
        return cleaned_data if cleaned_data else None
    
    def _apply_cleaning_rules(self, key: str, value: Any) -> Any:
        """应用清洗规则"""
        if value is None:
            return None
        
        # 去除空白字符
        if isinstance(value, str):
            value = value.strip()
            if not value:
                return None
        
        # 应用特定字段的规则
        if key in self.cleaning_rules:
            rule = self.cleaning_rules[key]
            
            if rule.get('type') == 'numeric':
                try:
                    return float(value)
                except (ValueError, TypeError):
                    return None
            
            elif rule.get('type') == 'integer':
                try:
                    return int(value)
                except (ValueError, TypeError):
                    return None
            
            elif rule.get('type') == 'string':
                if isinstance(value, str):
                    return value
                else:
                    return str(value)
        
        return value
```

### 3.2 数据转换组件

**数据转换组件**:

```python
class DataTransformationComponent(PipelineComponent):
    """数据转换组件"""
    
    def __init__(self, name: str, transformation_rules: Dict[str, Any] = None):
        super().__init__(name)
        self.transformation_rules = transformation_rules or {}
        self.config = {'transformation_rules': transformation_rules}
    
    def process(self, context: PipelineContext) -> PipelineContext:
        """处理数据转换"""
        input_data = context.get_data('cleaned_data') or context.get_data('raw_data')
        
        if not input_data:
            self.logger.warning("没有数据需要转换")
            return context
        
        self.logger.info(f"开始数据转换，规则: {self.transformation_rules}")
        
        try:
            if isinstance(input_data, list):
                transformed_data = self._transform_list_data(input_data)
            else:
                transformed_data = self._transform_single_data(input_data)
            
            # 设置转换后的数据
            context.set_data('transformed_data', transformed_data)
            context.set_metadata('transformation_applied', True)
            context.set_metadata('transformed_data_size', len(transformed_data) if isinstance(transformed_data, list) else 1)
            
            self.logger.info(f"数据转换完成，转换后数据大小: {context.get_metadata('transformed_data_size')}")
            
        except Exception as e:
            self.logger.error(f"数据转换失败: {e}")
            raise
        
        return context
    
    def _transform_list_data(self, data: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """转换列表数据"""
        transformed_data = []
        
        for item in data:
            transformed_item = self._transform_single_data(item)
            if transformed_item is not None:
                transformed_data.append(transformed_item)
        
        return transformed_data
    
    def _transform_single_data(self, data: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        """转换单个数据项"""
        if not isinstance(data, dict):
            return None
        
        transformed_data = {}
        
        for key, value in data.items():
            # 应用转换规则
            transformed_value = self._apply_transformation_rules(key, value)
            
            if transformed_value is not None:
                transformed_data[key] = transformed_value
        
        return transformed_data if transformed_data else None
    
    def _apply_transformation_rules(self, key: str, value: Any) -> Any:
        """应用转换规则"""
        if key in self.transformation_rules:
            rule = self.transformation_rules[key]
            
            if rule.get('type') == 'rename':
                # 重命名字段
                new_key = rule.get('new_name')
                if new_key:
                    return {new_key: value}
            
            elif rule.get('type') == 'function':
                # 自定义函数
                func_name = rule.get('function')
                if func_name == 'uppercase' and isinstance(value, str):
                    return value.upper()
                elif func_name == 'lowercase' and isinstance(value, str):
                    return value.lower()
                elif func_name == 'capitalize' and isinstance(value, str):
                    return value.capitalize()
        
        return value
```

## 4. 数据输出组件

### 4.1 文件输出组件

**文件输出组件**:

```python
class FileOutputComponent(PipelineComponent):
    """文件输出组件"""
    
    def __init__(self, name: str, output_path: str, output_format: str = 'json'):
        super().__init__(name)
        self.output_path = output_path
        self.output_format = output_format
        self.config = {
            'output_path': output_path,
            'output_format': output_format
        }
    
    def process(self, context: PipelineContext) -> PipelineContext:
        """处理文件输出"""
        # 获取要输出的数据
        data = (context.get_data('transformed_data') or 
                context.get_data('cleaned_data') or 
                context.get_data('raw_data'))
        
        if not data:
            self.logger.warning("没有数据需要输出")
            return context
        
        self.logger.info(f"输出数据到文件: {self.output_path}")
        
        try:
            if self.output_format == 'json':
                self._write_json_file(data)
            elif self.output_format == 'csv':
                self._write_csv_file(data)
            elif self.output_format == 'txt':
                self._write_text_file(data)
            else:
                raise ValueError(f"不支持的输出格式: {self.output_format}")
            
            # 设置输出元数据
            context.set_metadata('output_file', self.output_path)
            context.set_metadata('output_format', self.output_format)
            context.set_metadata('output_size', len(data) if isinstance(data, list) else 1)
            
            self.logger.info(f"成功输出数据到 {self.output_path}")
            
        except Exception as e:
            self.logger.error(f"文件输出失败: {e}")
            raise
        
        return context
    
    def _write_json_file(self, data: Any):
        """写入JSON文件"""
        import json
        with open(self.output_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
    
    def _write_csv_file(self, data: List[Dict[str, Any]]):
        """写入CSV文件"""
        import csv
        if not data:
            return
        
        fieldnames = data[0].keys()
        with open(self.output_path, 'w', newline='', encoding='utf-8') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(data)
    
    def _write_text_file(self, data: Any):
        """写入文本文件"""
        with open(self.output_path, 'w', encoding='utf-8') as f:
            if isinstance(data, list):
                for item in data:
                    f.write(str(item) + '\n')
            else:
                f.write(str(data))
```

## 5. 使用示例

**主程序示例**:

```python
def main():
    """数据管道示例"""
    print("=== AI理论数据管道工具演示 ===")
    
    # 创建数据管道
    pipeline = DataPipeline("ai_theory_data_pipeline")
    
    # 创建数据源组件
    file_source = FileDataSource(
        name="theory_data_source",
        file_path="ai_theory_data.json",
        file_type="json"
    )
    
    # 创建数据清洗组件
    cleaning_rules = {
        'name': {'type': 'string'},
        'description': {'type': 'string'},
        'complexity': {'type': 'numeric'},
        'accuracy': {'type': 'numeric'}
    }
    
    data_cleaner = DataCleaningComponent(
        name="theory_data_cleaner",
        cleaning_rules=cleaning_rules
    )
    
    # 创建数据转换组件
    transformation_rules = {
        'name': {'type': 'function', 'function': 'capitalize'},
        'category': {'type': 'rename', 'new_name': 'theory_category'}
    }
    
    data_transformer = DataTransformationComponent(
        name="theory_data_transformer",
        transformation_rules=transformation_rules
    )
    
    # 创建输出组件
    file_output = FileOutputComponent(
        name="theory_data_output",
        output_path="processed_ai_theory_data.json",
        output_format="json"
    )
    
    # 添加组件到管道
    pipeline.add_component(file_source)
    pipeline.add_component(data_cleaner)
    pipeline.add_component(data_transformer)
    pipeline.add_component(file_output)
    
    # 创建示例数据
    sample_data = [
        {
            'name': 'neural networks',
            'description': 'artificial neural networks for pattern recognition',
            'complexity': 0.8,
            'accuracy': 0.95,
            'category': 'machine_learning'
        },
        {
            'name': 'genetic algorithms',
            'description': 'evolutionary computation methods',
            'complexity': 0.6,
            'accuracy': 0.85,
            'category': 'optimization'
        }
    ]
    
    # 保存示例数据
    import json
    with open('ai_theory_data.json', 'w', encoding='utf-8') as f:
        json.dump(sample_data, f, indent=2, ensure_ascii=False)
    
    print("创建示例数据文件: ai_theory_data.json")
    
    # 执行管道
    print("开始执行数据管道...")
    try:
        result_context = pipeline.execute()
        
        print("管道执行成功!")
        print(f"输出文件: {result_context.get_metadata('output_file')}")
        print(f"处理数据量: {result_context.get_metadata('output_size')}")
        
        # 显示执行摘要
        summary = pipeline.get_execution_summary()
        print(f"执行摘要: {summary}")
        
    except Exception as e:
        print(f"管道执行失败: {e}")
    
    print("=== 演示完成 ===")

if __name__ == "__main__":
    main()
```

这个数据管道工具提供了完整的数据处理流程管理功能，包括数据源、数据清洗、数据转换和数据输出等核心组件，支持灵活的数据处理管道构建。
