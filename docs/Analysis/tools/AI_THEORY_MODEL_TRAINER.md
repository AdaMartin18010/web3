# AI理论模型训练工具

## 1. 模型训练框架

### 1.1 模型基类

**模型基类**:

```python
from abc import ABC, abstractmethod
from typing import Any, Dict, List, Optional, Tuple
from dataclasses import dataclass, field
from datetime import datetime
import numpy as np
import logging

@dataclass
class TrainingConfig:
    """训练配置"""
    model_type: str
    learning_rate: float = 0.001
    batch_size: int = 32
    epochs: int = 100
    validation_split: float = 0.2
    early_stopping_patience: int = 10
    model_save_path: str = "models/"
    log_level: str = "INFO"
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典"""
        return {
            'model_type': self.model_type,
            'learning_rate': self.learning_rate,
            'batch_size': self.batch_size,
            'epochs': self.epochs,
            'validation_split': self.validation_split,
            'early_stopping_patience': self.early_stopping_patience,
            'model_save_path': self.model_save_path,
            'log_level': self.log_level
        }

@dataclass
class TrainingMetrics:
    """训练指标"""
    epoch: int
    loss: float
    accuracy: float
    val_loss: float
    val_accuracy: float
    timestamp: datetime = field(default_factory=datetime.now)
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典"""
        return {
            'epoch': self.epoch,
            'loss': self.loss,
            'accuracy': self.accuracy,
            'val_loss': self.val_loss,
            'val_accuracy': self.val_accuracy,
            'timestamp': self.timestamp.isoformat()
        }

class BaseModel(ABC):
    """模型基类"""
    
    def __init__(self, name: str, config: TrainingConfig):
        self.name = name
        self.config = config
        self.logger = logging.getLogger(f"model.{name}")
        self.model = None
        self.training_history: List[TrainingMetrics] = []
        self.is_trained = False
    
    @abstractmethod
    def build_model(self) -> Any:
        """构建模型"""
        pass
    
    @abstractmethod
    def train(self, X_train: np.ndarray, y_train: np.ndarray, 
              X_val: np.ndarray = None, y_val: np.ndarray = None) -> Dict[str, Any]:
        """训练模型"""
        pass
    
    @abstractmethod
    def predict(self, X: np.ndarray) -> np.ndarray:
        """预测"""
        pass
    
    @abstractmethod
    def evaluate(self, X: np.ndarray, y: np.ndarray) -> Dict[str, float]:
        """评估模型"""
        pass
    
    def save_model(self, filepath: str):
        """保存模型"""
        if self.model is not None:
            import joblib
            joblib.dump(self.model, filepath)
            self.logger.info(f"模型已保存到: {filepath}")
    
    def load_model(self, filepath: str):
        """加载模型"""
        import joblib
        self.model = joblib.load(filepath)
        self.is_trained = True
        self.logger.info(f"模型已从 {filepath} 加载")
    
    def get_training_summary(self) -> Dict[str, Any]:
        """获取训练摘要"""
        if not self.training_history:
            return {}
        
        final_metrics = self.training_history[-1]
        
        return {
            'model_name': self.name,
            'total_epochs': len(self.training_history),
            'final_loss': final_metrics.loss,
            'final_accuracy': final_metrics.accuracy,
            'final_val_loss': final_metrics.val_loss,
            'final_val_accuracy': final_metrics.val_accuracy,
            'best_epoch': self._find_best_epoch()
        }
    
    def _find_best_epoch(self) -> int:
        """找到最佳epoch"""
        if not self.training_history:
            return 0
        
        best_epoch = 0
        best_val_accuracy = 0
        
        for metrics in self.training_history:
            if metrics.val_accuracy > best_val_accuracy:
                best_val_accuracy = metrics.val_accuracy
                best_epoch = metrics.epoch
        
        return best_epoch
```

### 1.2 模型训练器

**模型训练器**:

```python
class ModelTrainer:
    """模型训练器"""
    
    def __init__(self, config: TrainingConfig):
        self.config = config
        self.logger = logging.getLogger("model_trainer")
        self.models: Dict[str, BaseModel] = {}
        self.training_results: Dict[str, Dict[str, Any]] = {}
    
    def add_model(self, model: BaseModel):
        """添加模型"""
        self.models[model.name] = model
        self.logger.info(f"添加模型: {model.name}")
    
    def train_model(self, model_name: str, X_train: np.ndarray, y_train: np.ndarray,
                   X_val: np.ndarray = None, y_val: np.ndarray = None) -> Dict[str, Any]:
        """训练模型"""
        if model_name not in self.models:
            raise ValueError(f"模型 {model_name} 不存在")
        
        model = self.models[model_name]
        self.logger.info(f"开始训练模型: {model_name}")
        
        try:
            # 训练模型
            training_result = model.train(X_train, y_train, X_val, y_val)
            
            # 保存训练结果
            self.training_results[model_name] = training_result
            
            # 保存模型
            model_path = f"{self.config.model_save_path}/{model_name}.joblib"
            model.save_model(model_path)
            
            self.logger.info(f"模型 {model_name} 训练完成")
            
            return training_result
            
        except Exception as e:
            self.logger.error(f"模型 {model_name} 训练失败: {e}")
            raise
    
    def compare_models(self, X_test: np.ndarray, y_test: np.ndarray) -> Dict[str, Any]:
        """比较模型性能"""
        comparison = {}
        
        for model_name, model in self.models.items():
            if not model.is_trained:
                continue
            
            try:
                # 评估模型
                evaluation = model.evaluate(X_test, y_test)
                
                # 获取训练摘要
                training_summary = model.get_training_summary()
                
                comparison[model_name] = {
                    'evaluation': evaluation,
                    'training_summary': training_summary
                }
                
            except Exception as e:
                self.logger.error(f"评估模型 {model_name} 时出错: {e}")
                comparison[model_name] = {'error': str(e)}
        
        return comparison
    
    def get_best_model(self, X_test: np.ndarray, y_test: np.ndarray, 
                      metric: str = 'accuracy') -> Optional[str]:
        """获取最佳模型"""
        comparison = self.compare_models(X_test, y_test)
        
        best_model = None
        best_score = -1
        
        for model_name, result in comparison.items():
            if 'error' in result:
                continue
            
            score = result['evaluation'].get(metric, 0)
            if score > best_score:
                best_score = score
                best_model = model_name
        
        return best_model
```

## 2. 具体模型实现

### 2.1 神经网络模型

**神经网络模型**:

```python
class NeuralNetworkModel(BaseModel):
    """神经网络模型"""
    
    def __init__(self, name: str, config: TrainingConfig, layers: List[int] = None):
        super().__init__(name, config)
        self.layers = layers or [64, 32, 16]
        self.history = None
    
    def build_model(self):
        """构建神经网络模型"""
        try:
            import tensorflow as tf
            from tensorflow.keras import layers, models
            
            model = models.Sequential()
            
            # 输入层
            model.add(layers.Dense(self.layers[0], activation='relu', input_shape=(None,)))
            
            # 隐藏层
            for units in self.layers[1:]:
                model.add(layers.Dense(units, activation='relu'))
                model.add(layers.Dropout(0.2))
            
            # 输出层
            model.add(layers.Dense(1, activation='sigmoid'))
            
            # 编译模型
            model.compile(
                optimizer=tf.keras.optimizers.Adam(learning_rate=self.config.learning_rate),
                loss='binary_crossentropy',
                metrics=['accuracy']
            )
            
            self.model = model
            self.logger.info(f"神经网络模型构建完成，层数: {len(self.layers)}")
            
        except ImportError:
            self.logger.error("TensorFlow未安装，无法构建神经网络模型")
            raise
    
    def train(self, X_train: np.ndarray, y_train: np.ndarray,
              X_val: np.ndarray = None, y_val: np.ndarray = None) -> Dict[str, Any]:
        """训练神经网络"""
        if self.model is None:
            self.build_model()
        
        # 准备验证数据
        validation_data = None
        if X_val is not None and y_val is not None:
            validation_data = (X_val, y_val)
        
        # 训练模型
        self.history = self.model.fit(
            X_train, y_train,
            batch_size=self.config.batch_size,
            epochs=self.config.epochs,
            validation_data=validation_data,
            validation_split=self.config.validation_split if validation_data is None else 0.0,
            callbacks=self._get_callbacks(),
            verbose=1
        )
        
        # 记录训练历史
        self._record_training_history()
        
        self.is_trained = True
        
        return {
            'history': self.history.history,
            'final_loss': self.history.history['loss'][-1],
            'final_accuracy': self.history.history['accuracy'][-1]
        }
    
    def predict(self, X: np.ndarray) -> np.ndarray:
        """预测"""
        if self.model is None:
            raise ValueError("模型未训练")
        
        return self.model.predict(X)
    
    def evaluate(self, X: np.ndarray, y: np.ndarray) -> Dict[str, float]:
        """评估模型"""
        if self.model is None:
            raise ValueError("模型未训练")
        
        loss, accuracy = self.model.evaluate(X, y, verbose=0)
        
        # 计算其他指标
        y_pred = self.predict(X)
        y_pred_binary = (y_pred > 0.5).astype(int)
        
        from sklearn.metrics import precision_score, recall_score, f1_score
        
        precision = precision_score(y, y_pred_binary, average='binary')
        recall = recall_score(y, y_pred_binary, average='binary')
        f1 = f1_score(y, y_pred_binary, average='binary')
        
        return {
            'loss': loss,
            'accuracy': accuracy,
            'precision': precision,
            'recall': recall,
            'f1_score': f1
        }
    
    def _get_callbacks(self):
        """获取回调函数"""
        import tensorflow as tf
        
        callbacks = []
        
        # 早停
        if self.config.early_stopping_patience > 0:
            early_stopping = tf.keras.callbacks.EarlyStopping(
                monitor='val_loss',
                patience=self.config.early_stopping_patience,
                restore_best_weights=True
            )
            callbacks.append(early_stopping)
        
        return callbacks
    
    def _record_training_history(self):
        """记录训练历史"""
        if self.history is None:
            return
        
        for epoch in range(len(self.history.history['loss'])):
            metrics = TrainingMetrics(
                epoch=epoch + 1,
                loss=self.history.history['loss'][epoch],
                accuracy=self.history.history['accuracy'][epoch],
                val_loss=self.history.history.get('val_loss', [0])[epoch] if epoch < len(self.history.history.get('val_loss', [])) else 0,
                val_accuracy=self.history.history.get('val_accuracy', [0])[epoch] if epoch < len(self.history.history.get('val_accuracy', [])) else 0
            )
            self.training_history.append(metrics)
```

### 2.2 随机森林模型

**随机森林模型**:

```python
class RandomForestModel(BaseModel):
    """随机森林模型"""
    
    def __init__(self, name: str, config: TrainingConfig, n_estimators: int = 100):
        super().__init__(name, config)
        self.n_estimators = n_estimators
    
    def build_model(self):
        """构建随机森林模型"""
        try:
            from sklearn.ensemble import RandomForestClassifier
            
            self.model = RandomForestClassifier(
                n_estimators=self.n_estimators,
                random_state=42,
                n_jobs=-1
            )
            
            self.logger.info(f"随机森林模型构建完成，树的数量: {self.n_estimators}")
            
        except ImportError:
            self.logger.error("scikit-learn未安装，无法构建随机森林模型")
            raise
    
    def train(self, X_train: np.ndarray, y_train: np.ndarray,
              X_val: np.ndarray = None, y_val: np.ndarray = None) -> Dict[str, Any]:
        """训练随机森林"""
        if self.model is None:
            self.build_model()
        
        # 训练模型
        self.model.fit(X_train, y_train)
        
        # 记录训练历史
        self._record_training_history(X_train, y_train, X_val, y_val)
        
        self.is_trained = True
        
        return {
            'n_estimators': self.n_estimators,
            'feature_importances': self.model.feature_importances_.tolist()
        }
    
    def predict(self, X: np.ndarray) -> np.ndarray:
        """预测"""
        if self.model is None:
            raise ValueError("模型未训练")
        
        return self.model.predict(X)
    
    def evaluate(self, X: np.ndarray, y: np.ndarray) -> Dict[str, float]:
        """评估模型"""
        if self.model is None:
            raise ValueError("模型未训练")
        
        from sklearn.metrics import accuracy_score, precision_score, recall_score, f1_score
        
        y_pred = self.predict(X)
        
        accuracy = accuracy_score(y, y_pred)
        precision = precision_score(y, y_pred, average='binary')
        recall = recall_score(y, y_pred, average='binary')
        f1 = f1_score(y, y_pred, average='binary')
        
        return {
            'accuracy': accuracy,
            'precision': precision,
            'recall': recall,
            'f1_score': f1
        }
    
    def _record_training_history(self, X_train: np.ndarray, y_train: np.ndarray,
                                X_val: np.ndarray = None, y_val: np.ndarray = None):
        """记录训练历史"""
        # 训练集评估
        train_pred = self.predict(X_train)
        train_accuracy = np.mean(train_pred == y_train)
        
        # 验证集评估
        val_accuracy = 0.0
        if X_val is not None and y_val is not None:
            val_pred = self.predict(X_val)
            val_accuracy = np.mean(val_pred == y_val)
        
        metrics = TrainingMetrics(
            epoch=1,
            loss=0.0,  # 随机森林没有损失函数
            accuracy=train_accuracy,
            val_loss=0.0,
            val_accuracy=val_accuracy
        )
        self.training_history.append(metrics)
```

## 3. 数据预处理

### 3.1 数据预处理器

**数据预处理器**:

```python
class DataPreprocessor:
    """数据预处理器"""
    
    def __init__(self):
        self.scaler = None
        self.encoder = None
        self.feature_names = None
    
    def preprocess_features(self, X: np.ndarray, feature_names: List[str] = None) -> np.ndarray:
        """预处理特征"""
        if feature_names:
            self.feature_names = feature_names
        
        # 标准化数值特征
        X_scaled = self._scale_features(X)
        
        return X_scaled
    
    def preprocess_target(self, y: np.ndarray) -> np.ndarray:
        """预处理目标变量"""
        # 编码目标变量
        if len(np.unique(y)) > 2:
            # 多分类
            from sklearn.preprocessing import LabelEncoder
            self.encoder = LabelEncoder()
            y_encoded = self.encoder.fit_transform(y)
        else:
            # 二分类
            y_encoded = y.astype(int)
        
        return y_encoded
    
    def _scale_features(self, X: np.ndarray) -> np.ndarray:
        """标准化特征"""
        from sklearn.preprocessing import StandardScaler
        
        self.scaler = StandardScaler()
        X_scaled = self.scaler.fit_transform(X)
        
        return X_scaled
    
    def transform_features(self, X: np.ndarray) -> np.ndarray:
        """转换新数据"""
        if self.scaler is None:
            raise ValueError("预处理器未训练")
        
        X_scaled = self.scaler.transform(X)
        
        return X_scaled
```

## 4. 使用示例

**主程序示例**:

```python
def main():
    """模型训练示例"""
    print("=== AI理论模型训练工具演示 ===")
    
    # 创建训练配置
    config = TrainingConfig(
        model_type="neural_network",
        learning_rate=0.001,
        batch_size=32,
        epochs=50,
        validation_split=0.2,
        early_stopping_patience=5
    )
    
    # 创建模型训练器
    trainer = ModelTrainer(config)
    
    # 创建数据预处理器
    preprocessor = DataPreprocessor()
    
    # 生成示例数据
    np.random.seed(42)
    n_samples = 1000
    n_features = 10
    
    X = np.random.randn(n_samples, n_features)
    y = (X[:, 0] + X[:, 1] > 0).astype(int)  # 简单的二分类任务
    
    # 分割数据
    from sklearn.model_selection import train_test_split
    X_train, X_test, y_train, y_test = train_test_split(X, y, test_size=0.2, random_state=42)
    X_train, X_val, y_train, y_val = train_test_split(X_train, y_train, test_size=0.2, random_state=42)
    
    # 预处理数据
    X_train_processed = preprocessor.preprocess_features(X_train)
    X_val_processed = preprocessor.preprocess_features(X_val)
    X_test_processed = preprocessor.preprocess_features(X_test)
    
    y_train_processed = preprocessor.preprocess_target(y_train)
    y_val_processed = preprocessor.preprocess_target(y_val)
    y_test_processed = preprocessor.preprocess_target(y_test)
    
    print(f"训练集大小: {X_train_processed.shape}")
    print(f"验证集大小: {X_val_processed.shape}")
    print(f"测试集大小: {X_test_processed.shape}")
    
    # 创建模型
    nn_model = NeuralNetworkModel("neural_network", config, layers=[64, 32])
    rf_model = RandomForestModel("random_forest", config, n_estimators=100)
    
    # 添加模型到训练器
    trainer.add_model(nn_model)
    trainer.add_model(rf_model)
    
    # 训练模型
    print("开始训练模型...")
    for model_name in trainer.models:
        try:
            training_result = trainer.train_model(
                model_name, X_train_processed, y_train_processed,
                X_val_processed, y_val_processed
            )
            print(f"{model_name} 训练完成")
        except Exception as e:
            print(f"{model_name} 训练失败: {e}")
    
    # 比较模型
    comparison = trainer.compare_models(X_test_processed, y_test_processed)
    best_model = trainer.get_best_model(X_test_processed, y_test_processed)
    
    print(f"\n最佳模型: {best_model}")
    
    # 显示比较结果
    for model_name, result in comparison.items():
        if 'error' not in result:
            print(f"\n{model_name} 评估结果:")
            print(f"  准确率: {result['evaluation']['accuracy']:.4f}")
            print(f"  精确率: {result['evaluation']['precision']:.4f}")
            print(f"  召回率: {result['evaluation']['recall']:.4f}")
            print(f"  F1分数: {result['evaluation']['f1_score']:.4f}")
    
    print("=== 演示完成 ===")

if __name__ == "__main__":
    main()
```

这个模型训练工具提供了完整的机器学习模型训练和管理功能，包括神经网络、随机森林等多种模型类型，以及数据预处理和模型评估等核心功能。
