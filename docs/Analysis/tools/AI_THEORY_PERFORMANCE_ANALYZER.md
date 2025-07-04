# AI理论性能分析工具

## 1. 性能分析框架

### 1.1 性能指标定义

**性能指标类**:

```python
@dataclass
class PerformanceMetrics:
    """性能指标"""
    execution_time: float
    memory_usage: float
    cpu_usage: float
    throughput: float
    latency: float
    accuracy: float
    precision: float
    recall: float
    f1_score: float
    timestamp: datetime = field(default_factory=datetime.now)
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典"""
        return {
            'execution_time': self.execution_time,
            'memory_usage': self.memory_usage,
            'cpu_usage': self.cpu_usage,
            'throughput': self.throughput,
            'latency': self.latency,
            'accuracy': self.accuracy,
            'precision': self.precision,
            'recall': self.recall,
            'f1_score': self.f1_score,
            'timestamp': self.timestamp.isoformat()
        }
```

**性能基准类**:

```python
@dataclass
class PerformanceBenchmark:
    """性能基准"""
    name: str
    description: str
    metrics: PerformanceMetrics
    baseline_metrics: Optional[PerformanceMetrics] = None
    threshold: float = 0.1  # 10%的性能差异阈值
    
    def compare_with_baseline(self) -> Dict[str, Any]:
        """与基准比较"""
        if not self.baseline_metrics:
            return {'status': 'no_baseline', 'message': '没有基准数据'}
        
        comparison = {}
        
        # 比较执行时间
        time_diff = (self.metrics.execution_time - self.baseline_metrics.execution_time) / self.baseline_metrics.execution_time
        comparison['execution_time'] = {
            'difference': time_diff,
            'status': 'improved' if time_diff < -self.threshold else 'degraded' if time_diff > self.threshold else 'stable'
        }
        
        # 比较内存使用
        memory_diff = (self.metrics.memory_usage - self.baseline_metrics.memory_usage) / self.baseline_metrics.memory_usage
        comparison['memory_usage'] = {
            'difference': memory_diff,
            'status': 'improved' if memory_diff < -self.threshold else 'degraded' if memory_diff > self.threshold else 'stable'
        }
        
        return comparison
```

### 1.2 性能监控器

**性能监控器**:

```python
class PerformanceMonitor:
    """性能监控器"""
    
    def __init__(self):
        self.metrics_history: List[PerformanceMetrics] = []
        self.active_monitoring = False
        self.monitoring_interval = 1.0  # 秒
    
    def start_monitoring(self):
        """开始监控"""
        self.active_monitoring = True
        self.monitoring_thread = threading.Thread(target=self._monitoring_loop)
        self.monitoring_thread.daemon = True
        self.monitoring_thread.start()
    
    def stop_monitoring(self):
        """停止监控"""
        self.active_monitoring = False
        if hasattr(self, 'monitoring_thread'):
            self.monitoring_thread.join()
    
    def _monitoring_loop(self):
        """监控循环"""
        import psutil
        import os
        
        process = psutil.Process(os.getpid())
        
        while self.active_monitoring:
            try:
                # 收集性能指标
                cpu_percent = process.cpu_percent()
                memory_info = process.memory_info()
                memory_mb = memory_info.rss / 1024 / 1024
                
                metrics = PerformanceMetrics(
                    execution_time=0.0,  # 需要外部提供
                    memory_usage=memory_mb,
                    cpu_usage=cpu_percent,
                    throughput=0.0,  # 需要外部提供
                    latency=0.0,  # 需要外部提供
                    accuracy=0.0,  # 需要外部提供
                    precision=0.0,  # 需要外部提供
                    recall=0.0,  # 需要外部提供
                    f1_score=0.0  # 需要外部提供
                )
                
                self.metrics_history.append(metrics)
                time.sleep(self.monitoring_interval)
                
            except Exception as e:
                print(f"监控错误: {e}")
                time.sleep(self.monitoring_interval)
    
    def get_current_metrics(self) -> Optional[PerformanceMetrics]:
        """获取当前指标"""
        if self.metrics_history:
            return self.metrics_history[-1]
        return None
    
    def get_metrics_summary(self) -> Dict[str, Any]:
        """获取指标摘要"""
        if not self.metrics_history:
            return {}
        
        memory_usages = [m.memory_usage for m in self.metrics_history]
        cpu_usages = [m.cpu_usage for m in self.metrics_history]
        
        return {
            'total_samples': len(self.metrics_history),
            'memory_usage': {
                'mean': np.mean(memory_usages),
                'std': np.std(memory_usages),
                'min': np.min(memory_usages),
                'max': np.max(memory_usages)
            },
            'cpu_usage': {
                'mean': np.mean(cpu_usages),
                'std': np.std(cpu_usages),
                'min': np.min(cpu_usages),
                'max': np.max(cpu_usages)
            }
        }
```

## 2. 算法复杂度分析

### 2.1 复杂度分析器

**复杂度分析器**:

```python
class ComplexityAnalyzer:
    """复杂度分析器"""
    
    def __init__(self):
        self.complexity_patterns = {
            'O(1)': self._constant_pattern,
            'O(log n)': self._logarithmic_pattern,
            'O(n)': self._linear_pattern,
            'O(n log n)': self._linearithmic_pattern,
            'O(n²)': self._quadratic_pattern,
            'O(2ⁿ)': self._exponential_pattern
        }
    
    def analyze_algorithm(self, algorithm_func: callable, input_sizes: List[int], 
                         num_runs: int = 5) -> Dict[str, Any]:
        """分析算法复杂度"""
        execution_times = []
        
        for size in input_sizes:
            size_times = []
            
            for _ in range(num_runs):
                # 生成测试数据
                test_data = self._generate_test_data(size)
                
                # 测量执行时间
                start_time = time.perf_counter()
                algorithm_func(test_data)
                end_time = time.perf_counter()
                
                size_times.append(end_time - start_time)
            
            # 取平均值
            execution_times.append(np.mean(size_times))
        
        # 分析复杂度
        complexity = self._determine_complexity(input_sizes, execution_times)
        
        return {
            'input_sizes': input_sizes,
            'execution_times': execution_times,
            'complexity': complexity,
            'analysis': self._analyze_complexity_fit(input_sizes, execution_times, complexity)
        }
    
    def _generate_test_data(self, size: int) -> List[int]:
        """生成测试数据"""
        return list(range(size))
    
    def _determine_complexity(self, input_sizes: List[int], execution_times: List[float]) -> str:
        """确定复杂度"""
        best_fit = None
        min_error = float('inf')
        
        for complexity_name, pattern_func in self.complexity_patterns.items():
            error = pattern_func(input_sizes, execution_times)
            if error < min_error:
                min_error = error
                best_fit = complexity_name
        
        return best_fit
    
    def _constant_pattern(self, input_sizes: List[int], execution_times: List[float]) -> float:
        """常数模式"""
        return np.std(execution_times)
    
    def _logarithmic_pattern(self, input_sizes: List[int], execution_times: List[float]) -> float:
        """对数模式"""
        log_sizes = np.log(input_sizes)
        correlation = np.corrcoef(log_sizes, execution_times)[0, 1]
        return 1 - abs(correlation)
    
    def _linear_pattern(self, input_sizes: List[int], execution_times: List[float]) -> float:
        """线性模式"""
        correlation = np.corrcoef(input_sizes, execution_times)[0, 1]
        return 1 - abs(correlation)
    
    def _linearithmic_pattern(self, input_sizes: List[int], execution_times: List[float]) -> float:
        """线性对数模式"""
        n_log_n = [n * np.log(n) for n in input_sizes]
        correlation = np.corrcoef(n_log_n, execution_times)[0, 1]
        return 1 - abs(correlation)
    
    def _quadratic_pattern(self, input_sizes: List[int], execution_times: List[float]) -> float:
        """二次模式"""
        squared_sizes = [n**2 for n in input_sizes]
        correlation = np.corrcoef(squared_sizes, execution_times)[0, 1]
        return 1 - abs(correlation)
    
    def _exponential_pattern(self, input_sizes: List[int], execution_times: List[float]) -> float:
        """指数模式"""
        exp_sizes = [2**n for n in input_sizes]
        correlation = np.corrcoef(exp_sizes, execution_times)[0, 1]
        return 1 - abs(correlation)
    
    def _analyze_complexity_fit(self, input_sizes: List[int], execution_times: List[float], 
                               complexity: str) -> Dict[str, Any]:
        """分析复杂度拟合"""
        if complexity == 'O(1)':
            predicted_times = [np.mean(execution_times)] * len(input_sizes)
        elif complexity == 'O(log n)':
            predicted_times = [np.log(n) for n in input_sizes]
        elif complexity == 'O(n)':
            predicted_times = input_sizes
        elif complexity == 'O(n log n)':
            predicted_times = [n * np.log(n) for n in input_sizes]
        elif complexity == 'O(n²)':
            predicted_times = [n**2 for n in input_sizes]
        elif complexity == 'O(2ⁿ)':
            predicted_times = [2**n for n in input_sizes]
        else:
            predicted_times = execution_times
        
        # 归一化
        scale_factor = np.mean(execution_times) / np.mean(predicted_times)
        predicted_times = [t * scale_factor for t in predicted_times]
        
        # 计算拟合误差
        mse = np.mean((np.array(execution_times) - np.array(predicted_times))**2)
        r_squared = 1 - mse / np.var(execution_times)
        
        return {
            'mse': mse,
            'r_squared': r_squared,
            'scale_factor': scale_factor,
            'predicted_times': predicted_times
        }
```

### 2.2 性能基准测试

**性能基准测试器**:

```python
class PerformanceBenchmarker:
    """性能基准测试器"""
    
    def __init__(self):
        self.benchmarks: Dict[str, Dict[str, Any]] = {}
        self.complexity_analyzer = ComplexityAnalyzer()
    
    def add_benchmark(self, name: str, algorithm_func: callable, description: str = ""):
        """添加基准测试"""
        self.benchmarks[name] = {
            'function': algorithm_func,
            'description': description,
            'baseline': None
        }
    
    def run_benchmark(self, benchmark_name: str, input_sizes: List[int], 
                     num_runs: int = 5) -> PerformanceBenchmark:
        """运行基准测试"""
        if benchmark_name not in self.benchmarks:
            raise ValueError(f"基准测试 '{benchmark_name}' 不存在")
        
        benchmark_info = self.benchmarks[benchmark_name]
        algorithm_func = benchmark_info['function']
        
        # 分析复杂度
        complexity_analysis = self.complexity_analyzer.analyze_algorithm(
            algorithm_func, input_sizes, num_runs
        )
        
        # 创建性能指标
        metrics = PerformanceMetrics(
            execution_time=complexity_analysis['execution_times'][-1],  # 最大输入的执行时间
            memory_usage=0.0,  # 需要实际测量
            cpu_usage=0.0,  # 需要实际测量
            throughput=1.0 / complexity_analysis['execution_times'][-1] if complexity_analysis['execution_times'][-1] > 0 else 0.0,
            latency=complexity_analysis['execution_times'][-1],
            accuracy=1.0,  # 假设100%准确
            precision=1.0,
            recall=1.0,
            f1_score=1.0
        )
        
        # 创建基准测试结果
        benchmark = PerformanceBenchmark(
            name=benchmark_name,
            description=benchmark_info['description'],
            metrics=metrics,
            baseline_metrics=benchmark_info.get('baseline')
        )
        
        # 保存为新的基准
        benchmark_info['baseline'] = metrics
        
        return benchmark
    
    def compare_benchmarks(self, benchmark_names: List[str], input_sizes: List[int]) -> Dict[str, Any]:
        """比较多个基准测试"""
        results = {}
        
        for name in benchmark_names:
            benchmark = self.run_benchmark(name, input_sizes)
            results[name] = {
                'benchmark': benchmark,
                'comparison': benchmark.compare_with_baseline()
            }
        
        return results
```

## 3. 资源使用分析

### 3.1 内存分析器

**内存分析器**:

```python
class MemoryAnalyzer:
    """内存分析器"""
    
    def __init__(self):
        self.memory_snapshots: List[Dict[str, Any]] = []
    
    def start_analysis(self):
        """开始内存分析"""
        self.memory_snapshots = []
        self._take_snapshot("start")
    
    def take_snapshot(self, label: str):
        """拍摄内存快照"""
        self._take_snapshot(label)
    
    def end_analysis(self):
        """结束内存分析"""
        self._take_snapshot("end")
        return self._analyze_memory_usage()
    
    def _take_snapshot(self, label: str):
        """拍摄快照"""
        import psutil
        import os
        
        process = psutil.Process(os.getpid())
        memory_info = process.memory_info()
        
        snapshot = {
            'label': label,
            'timestamp': datetime.now(),
            'rss': memory_info.rss,  # 物理内存
            'vms': memory_info.vms,  # 虚拟内存
            'percent': process.memory_percent(),
            'available': psutil.virtual_memory().available
        }
        
        self.memory_snapshots.append(snapshot)
    
    def _analyze_memory_usage(self) -> Dict[str, Any]:
        """分析内存使用"""
        if len(self.memory_snapshots) < 2:
            return {}
        
        start_snapshot = self.memory_snapshots[0]
        end_snapshot = self.memory_snapshots[-1]
        
        # 计算内存增长
        rss_growth = end_snapshot['rss'] - start_snapshot['rss']
        vms_growth = end_snapshot['vms'] - start_snapshot['vms']
        
        # 计算峰值内存
        peak_rss = max(snapshot['rss'] for snapshot in self.memory_snapshots)
        peak_vms = max(snapshot['vms'] for snapshot in self.memory_snapshots)
        
        return {
            'start_memory': {
                'rss_mb': start_snapshot['rss'] / 1024 / 1024,
                'vms_mb': start_snapshot['vms'] / 1024 / 1024,
                'percent': start_snapshot['percent']
            },
            'end_memory': {
                'rss_mb': end_snapshot['rss'] / 1024 / 1024,
                'vms_mb': end_snapshot['vms'] / 1024 / 1024,
                'percent': end_snapshot['percent']
            },
            'memory_growth': {
                'rss_mb': rss_growth / 1024 / 1024,
                'vms_mb': vms_growth / 1024 / 1024
            },
            'peak_memory': {
                'rss_mb': peak_rss / 1024 / 1024,
                'vms_mb': peak_vms / 1024 / 1024
            },
            'snapshots': self.memory_snapshots
        }
```

## 4. 性能报告生成

### 4.1 性能报告生成器

**性能报告生成器**:

```python
class PerformanceReportGenerator:
    """性能报告生成器"""
    
    def __init__(self):
        self.report_template = self._load_report_template()
    
    def generate_report(self, performance_data: Dict[str, Any], output_path: str):
        """生成性能报告"""
        report_content = self._generate_report_content(performance_data)
        
        # 生成HTML报告
        html_report = self._format_html_report(report_content)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html_report)
        
        return output_path
    
    def _generate_report_content(self, performance_data: Dict[str, Any]) -> Dict[str, Any]:
        """生成报告内容"""
        return {
            'title': 'AI理论性能分析报告',
            'timestamp': datetime.now().isoformat(),
            'summary': self._generate_summary(performance_data),
            'detailed_analysis': performance_data,
            'recommendations': self._generate_recommendations(performance_data)
        }
    
    def _generate_summary(self, data: Dict[str, Any]) -> Dict[str, Any]:
        """生成摘要"""
        summary = {
            'total_benchmarks': len(data.get('benchmarks', {})),
            'performance_overview': {},
            'key_findings': []
        }
        
        # 分析性能概览
        for benchmark_name, benchmark_data in data.get('benchmarks', {}).items():
            metrics = benchmark_data.get('benchmark', {}).get('metrics', {})
            if metrics:
                summary['performance_overview'][benchmark_name] = {
                    'execution_time': metrics.get('execution_time', 0),
                    'memory_usage': metrics.get('memory_usage', 0),
                    'throughput': metrics.get('throughput', 0)
                }
        
        return summary
    
    def _generate_recommendations(self, data: Dict[str, Any]) -> List[str]:
        """生成建议"""
        recommendations = []
        
        for benchmark_name, benchmark_data in data.get('benchmarks', {}).items():
            metrics = benchmark_data.get('benchmark', {}).get('metrics', {})
            comparison = benchmark_data.get('comparison', {})
            
            # 基于执行时间的建议
            if metrics.get('execution_time', 0) > 1.0:  # 超过1秒
                recommendations.append(f"{benchmark_name}: 考虑优化算法复杂度")
            
            # 基于内存使用的建议
            if metrics.get('memory_usage', 0) > 100:  # 超过100MB
                recommendations.append(f"{benchmark_name}: 考虑优化内存使用")
            
            # 基于比较结果的建议
            for metric, result in comparison.items():
                if result.get('status') == 'degraded':
                    recommendations.append(f"{benchmark_name}: {metric}性能下降，需要调查")
        
        return recommendations
    
    def _format_html_report(self, content: Dict[str, Any]) -> str:
        """格式化HTML报告"""
        html = f"""
        <!DOCTYPE html>
        <html>
        <head>
            <title>{content['title']}</title>
            <style>
                body {{ font-family: Arial, sans-serif; margin: 20px; }}
                .header {{ background-color: #f0f0f0; padding: 20px; border-radius: 5px; }}
                .section {{ margin: 20px 0; padding: 15px; border: 1px solid #ddd; border-radius: 5px; }}
                .metric {{ display: inline-block; margin: 10px; padding: 10px; background-color: #f9f9f9; border-radius: 3px; }}
                .recommendation {{ background-color: #fff3cd; padding: 10px; margin: 5px 0; border-left: 4px solid #ffc107; }}
            </style>
        </head>
        <body>
            <div class="header">
                <h1>{content['title']}</h1>
                <p>生成时间: {content['timestamp']}</p>
            </div>
            
            <div class="section">
                <h2>性能摘要</h2>
                <p>总基准测试数: {content['summary']['total_benchmarks']}</p>
                <div class="metric">
                    <strong>性能概览:</strong><br>
                    {self._format_performance_overview(content['summary']['performance_overview'])}
                </div>
            </div>
            
            <div class="section">
                <h2>详细分析</h2>
                <pre>{json.dumps(content['detailed_analysis'], indent=2, ensure_ascii=False)}</pre>
            </div>
            
            <div class="section">
                <h2>优化建议</h2>
                {self._format_recommendations(content['recommendations'])}
            </div>
        </body>
        </html>
        """
        
        return html
    
    def _format_performance_overview(self, overview: Dict[str, Any]) -> str:
        """格式化性能概览"""
        html = ""
        for name, metrics in overview.items():
            html += f"<strong>{name}:</strong><br>"
            html += f"执行时间: {metrics['execution_time']:.3f}s<br>"
            html += f"内存使用: {metrics['memory_usage']:.1f}MB<br>"
            html += f"吞吐量: {metrics['throughput']:.2f}/s<br><br>"
        return html
    
    def _format_recommendations(self, recommendations: List[str]) -> str:
        """格式化建议"""
        html = ""
        for rec in recommendations:
            html += f'<div class="recommendation">{rec}</div>'
        return html
    
    def _load_report_template(self) -> str:
        """加载报告模板"""
        return "performance_report_template.html"
```

## 5. 使用示例

**主程序示例**:

```python
def main():
    """性能分析示例"""
    print("=== AI理论性能分析工具演示 ===")
    
    # 创建性能监控器
    monitor = PerformanceMonitor()
    
    # 创建复杂度分析器
    complexity_analyzer = ComplexityAnalyzer()
    
    # 创建基准测试器
    benchmarker = PerformanceBenchmarker()
    
    # 定义测试算法
    def linear_algorithm(data):
        """线性算法 O(n)"""
        return sum(data)
    
    def quadratic_algorithm(data):
        """二次算法 O(n²)"""
        result = 0
        for i in data:
            for j in data:
                result += i * j
        return result
    
    # 添加基准测试
    benchmarker.add_benchmark("linear", linear_algorithm, "线性算法")
    benchmarker.add_benchmark("quadratic", quadratic_algorithm, "二次算法")
    
    # 运行基准测试
    input_sizes = [100, 500, 1000, 2000]
    
    print("运行基准测试...")
    results = benchmarker.compare_benchmarks(["linear", "quadratic"], input_sizes)
    
    # 分析结果
    for name, result in results.items():
        benchmark = result['benchmark']
        comparison = result['comparison']
        
        print(f"\n{name} 基准测试:")
        print(f"  执行时间: {benchmark.metrics.execution_time:.6f}s")
        print(f"  吞吐量: {benchmark.metrics.throughput:.2f}/s")
        
        if comparison.get('status') != 'no_baseline':
            print(f"  与基准比较: {comparison}")
    
    # 创建性能报告
    report_generator = PerformanceReportGenerator()
    report_path = report_generator.generate_report(results, "performance_report.html")
    print(f"\n性能报告已生成: {report_path}")
    
    # 内存分析示例
    print("\n开始内存分析...")
    memory_analyzer = MemoryAnalyzer()
    memory_analyzer.start_analysis()
    
    # 执行一些操作
    large_list = [i for i in range(1000000)]
    memory_analyzer.take_snapshot("after_creating_list")
    
    # 清理内存
    del large_list
    memory_analyzer.take_snapshot("after_cleanup")
    
    memory_analysis = memory_analyzer.end_analysis()
    print(f"内存分析结果: {memory_analysis}")
    
    print("=== 演示完成 ===")

if __name__ == "__main__":
    main()
```

这个性能分析工具提供了完整的性能监控、分析和报告功能，包括算法复杂度分析、资源使用分析和性能基准测试等核心功能。
