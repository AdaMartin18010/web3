# 性能监控系统应用

## 概述

性能监控系统是Phase 3第3个月"性能优化"阶段的核心应用，提供实时性能指标监控、性能瓶颈分析和智能优化建议。

## 核心功能

### 1. 多协议性能数据收集器

#### Go - 区块链性能监控

```go
package main

import (
    "context"
    "log"
    "time"
    "github.com/ethereum/go-ethereum/ethclient"
    "github.com/prometheus/client_golang/prometheus"
    "github.com/prometheus/client_golang/prometheus/promauto"
)

type PerformanceCollector struct {
    client   *ethclient.Client
    blockHeight prometheus.Gauge
    gasPrice    prometheus.Gauge
    pendingTxs  prometheus.Gauge
}

func NewPerformanceCollector(rpcURL string) *PerformanceCollector {
    client, err := ethclient.Dial(rpcURL)
    if err != nil {
        log.Fatal(err)
    }

    return &PerformanceCollector{
        client: client,
        blockHeight: promauto.NewGauge(prometheus.GaugeOpts{
            Name: "blockchain_block_height",
            Help: "Current block height",
        }),
        gasPrice: promauto.NewGauge(prometheus.GaugeOpts{
            Name: "blockchain_gas_price",
            Help: "Current gas price in wei",
        }),
        pendingTxs: promauto.NewGauge(prometheus.GaugeOpts{
            Name: "blockchain_pending_transactions",
            Help: "Number of pending transactions",
        }),
    }
}

func (pc *PerformanceCollector) collectMetrics() {
    ctx := context.Background()
    
    // 收集区块高度
    blockNumber, err := pc.client.BlockNumber(ctx)
    if err == nil {
        pc.blockHeight.Set(float64(blockNumber))
    }

    // 收集Gas价格
    gasPrice, err := pc.client.SuggestGasPrice(ctx)
    if err == nil {
        pc.gasPrice.Set(float64(gasPrice.Int64()))
    }

    // 收集待处理交易数
    pendingCount, err := pc.client.PendingTransactionCount(ctx)
    if err == nil {
        pc.pendingTxs.Set(float64(pendingCount))
    }
}

func main() {
    collector := NewPerformanceCollector("https://mainnet.infura.io/v3/YOUR_PROJECT_ID")
    ticker := time.NewTicker(15 * time.Second)
    
    for range ticker.C {
        collector.collectMetrics()
    }
}
```

#### Python - DeFi协议性能监控

```python
import asyncio
import aiohttp
from prometheus_client import Gauge, Histogram
import time

class DeFiPerformanceCollector:
    def __init__(self):
        self.tvl_gauge = Gauge('defi_tvl', 'Total Value Locked', ['protocol'])
        self.volume_gauge = Gauge('defi_volume_24h', '24h Volume', ['protocol'])
        self.response_time = Histogram('defi_response_time', 'API Response Time', ['protocol'])
        
        self.protocols = {
            'uniswap': 'https://api.uniswap.org/v1/analytics/overview',
            'aave': 'https://api.aave.com/v1/protocol-data'
        }

    async def collect_metrics(self, session: aiohttp.ClientSession, protocol: str, url: str):
        start_time = time.time()
        
        try:
            async with session.get(url) as response:
                data = await response.json()
                response_time = time.time() - start_time
                
                self.tvl_gauge.labels(protocol=protocol).set(float(data.get('tvl', 0)))
                self.volume_gauge.labels(protocol=protocol).set(float(data.get('volume24h', 0)))
                self.response_time.labels(protocol=protocol).observe(response_time)
                
        except Exception as e:
            print(f"Error collecting {protocol} metrics: {e}")

    async def start_monitoring(self):
        async with aiohttp.ClientSession() as session:
            while True:
                tasks = [
                    self.collect_metrics(session, protocol, url)
                    for protocol, url in self.protocols.items()
                ]
                await asyncio.gather(*tasks)
                await asyncio.sleep(60)

if __name__ == "__main__":
    collector = DeFiPerformanceCollector()
    asyncio.run(collector.start_monitoring())
```

### 2. 性能瓶颈分析引擎

#### Rust - 高性能分析引擎

```rust
use std::collections::HashMap;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceData {
    pub timestamp: u64,
    pub metric_name: String,
    pub value: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BottleneckAnalysis {
    pub severity: String,
    pub metric_name: String,
    pub current_value: f64,
    pub threshold: f64,
    pub description: String,
    pub recommendations: Vec<String>,
}

pub struct PerformanceAnalyzer {
    data_store: Vec<PerformanceData>,
    thresholds: HashMap<String, f64>,
}

impl PerformanceAnalyzer {
    pub fn new() -> Self {
        let mut thresholds = HashMap::new();
        thresholds.insert("response_time".to_string(), 200.0);
        thresholds.insert("error_rate".to_string(), 0.01);
        thresholds.insert("cpu_usage".to_string(), 80.0);

        Self {
            data_store: Vec::new(),
            thresholds,
        }
    }

    pub fn add_data(&mut self, data: PerformanceData) {
        self.data_store.push(data);
        if self.data_store.len() > 1000 {
            self.data_store.remove(0);
        }
    }

    pub fn analyze_bottlenecks(&self) -> Vec<BottleneckAnalysis> {
        let mut bottlenecks = Vec::new();
        
        for data in self.data_store.iter().rev().take(10) {
            if let Some(threshold) = self.thresholds.get(&data.metric_name) {
                if data.value > *threshold {
                    bottlenecks.push(BottleneckAnalysis {
                        severity: if data.value > *threshold * 2.0 { "critical".to_string() } else { "high".to_string() },
                        metric_name: data.metric_name.clone(),
                        current_value: data.value,
                        threshold: *threshold,
                        description: format!("{} 超过阈值", data.metric_name),
                        recommendations: vec![
                            "检查系统资源".to_string(),
                            "优化代码逻辑".to_string(),
                            "增加缓存".to_string(),
                        ],
                    });
                }
            }
        }
        
        bottlenecks
    }
}
```

### 3. 优化建议系统

#### TypeScript - 智能优化建议引擎

```typescript
import React, { useState, useEffect } from 'react';
import { LineChart, Line, XAxis, YAxis, CartesianGrid, Tooltip, ResponsiveContainer } from 'recharts';

interface PerformanceMetric {
  timestamp: number;
  value: number;
  metric: string;
}

interface OptimizationSuggestion {
  id: string;
  title: string;
  description: string;
  priority: 'low' | 'medium' | 'high' | 'critical';
  recommendations: string[];
}

const PerformanceDashboard: React.FC = () => {
  const [metrics, setMetrics] = useState<PerformanceMetric[]>([]);
  const [suggestions, setSuggestions] = useState<OptimizationSuggestion[]>([]);
  const [selectedMetric, setSelectedMetric] = useState<string>('response_time');

  useEffect(() => {
    // 模拟数据获取
    const mockMetrics: PerformanceMetric[] = Array.from({ length: 50 }, (_, i) => ({
      timestamp: Date.now() - (50 - i) * 60000,
      value: Math.random() * 300,
      metric: 'response_time'
    }));
    
    setMetrics(mockMetrics);
    
    const mockSuggestions: OptimizationSuggestion[] = [
      {
        id: '1',
        title: 'API响应时间优化',
        description: '当前平均响应时间为250ms，建议优化到200ms以下',
        priority: 'high',
        recommendations: [
          '优化数据库查询',
          '增加Redis缓存',
          '使用CDN加速'
        ]
      },
      {
        id: '2',
        title: 'Gas价格监控',
        description: '当前Gas价格为80 gwei，建议等待网络拥堵缓解',
        priority: 'medium',
        recommendations: [
          '使用Layer2解决方案',
          '批量处理交易',
          '等待网络拥堵缓解'
        ]
      }
    ];
    
    setSuggestions(mockSuggestions);
  }, []);

  const filteredMetrics = metrics.filter(m => m.metric === selectedMetric);

  return (
    <div className="p-6 bg-gray-50 min-h-screen">
      <div className="max-w-7xl mx-auto">
        <h1 className="text-3xl font-bold text-gray-900 mb-8">性能监控仪表板</h1>
        
        {/* 控制面板 */}
        <div className="bg-white rounded-lg shadow p-6 mb-6">
          <select
            value={selectedMetric}
            onChange={(e) => setSelectedMetric(e.target.value)}
            className="border border-gray-300 rounded-md px-3 py-2"
          >
            <option value="response_time">响应时间</option>
            <option value="error_rate">错误率</option>
            <option value="cpu_usage">CPU使用率</option>
            <option value="gas_price">Gas价格</option>
          </select>
        </div>

        <div className="grid grid-cols-1 lg:grid-cols-3 gap-6">
          {/* 性能图表 */}
          <div className="lg:col-span-2 bg-white rounded-lg shadow p-6">
            <h2 className="text-xl font-semibold text-gray-900 mb-4">性能趋势</h2>
            <ResponsiveContainer width="100%" height={400}>
              <LineChart data={filteredMetrics}>
                <CartesianGrid strokeDasharray="3 3" />
                <XAxis 
                  dataKey="timestamp" 
                  tickFormatter={(value) => new Date(value).toLocaleTimeString()}
                />
                <YAxis />
                <Tooltip 
                  labelFormatter={(value) => new Date(value).toLocaleString()}
                />
                <Line 
                  type="monotone" 
                  dataKey="value" 
                  stroke="#3B82F6" 
                  strokeWidth={2}
                  dot={false}
                />
              </LineChart>
            </ResponsiveContainer>
          </div>

          {/* 统计信息 */}
          <div className="bg-white rounded-lg shadow p-6">
            <h2 className="text-xl font-semibold text-gray-900 mb-4">统计信息</h2>
            {(() => {
              if (filteredMetrics.length === 0) return <p className="text-gray-500">暂无数据</p>;
              
              const values = filteredMetrics.map(m => m.value);
              const avg = values.reduce((a, b) => a + b, 0) / values.length;
              const min = Math.min(...values);
              const max = Math.max(...values);
              
              return (
                <div className="space-y-4">
                  <div className="flex justify-between">
                    <span className="text-gray-600">平均值:</span>
                    <span className="font-semibold">{avg.toFixed(2)}</span>
                  </div>
                  <div className="flex justify-between">
                    <span className="text-gray-600">最小值:</span>
                    <span className="font-semibold">{min.toFixed(2)}</span>
                  </div>
                  <div className="flex justify-between">
                    <span className="text-gray-600">最大值:</span>
                    <span className="font-semibold">{max.toFixed(2)}</span>
                  </div>
                  <div className="flex justify-between">
                    <span className="text-gray-600">数据点:</span>
                    <span className="font-semibold">{values.length}</span>
                  </div>
                </div>
              );
            })()}
          </div>
        </div>

        {/* 优化建议 */}
        <div className="bg-white rounded-lg shadow p-6 mt-6">
          <h2 className="text-xl font-semibold text-gray-900 mb-4">优化建议</h2>
          <div className="space-y-4">
            {suggestions.map((suggestion) => (
              <div 
                key={suggestion.id}
                className="border border-gray-200 rounded-lg p-4 hover:shadow-md transition-shadow"
              >
                <div className="flex items-start justify-between mb-2">
                  <h3 className="text-lg font-medium text-gray-900">
                    {suggestion.title}
                  </h3>
                  <span className={`px-2 py-1 rounded-full text-xs font-medium ${
                    suggestion.priority === 'critical' ? 'bg-red-100 text-red-800' :
                    suggestion.priority === 'high' ? 'bg-orange-100 text-orange-800' :
                    suggestion.priority === 'medium' ? 'bg-yellow-100 text-yellow-800' :
                    'bg-green-100 text-green-800'
                  }`}>
                    {suggestion.priority}
                  </span>
                </div>
                
                <p className="text-gray-600 mb-3">{suggestion.description}</p>
                
                <div className="space-y-2">
                  <h4 className="font-medium text-gray-900">建议措施:</h4>
                  <ul className="list-disc list-inside space-y-1 text-gray-600">
                    {suggestion.recommendations.map((rec, index) => (
                      <li key={index}>{rec}</li>
                    ))}
                  </ul>
                </div>
              </div>
            ))}
          </div>
        </div>
      </div>
    </div>
  );
};

export default PerformanceDashboard;
```

### 4. 部署配置

#### Docker Compose配置

```yaml
version: '3.8'

services:
  # 性能监控前端
  performance-frontend:
    build:
      context: ./frontend
      dockerfile: Dockerfile
    ports:
      - "3000:3000"
    environment:
      - NEXT_PUBLIC_API_URL=http://localhost:8080
    depends_on:
      - performance-backend
    networks:
      - performance-network

  # 性能监控后端
  performance-backend:
    build:
      context: ./backend
      dockerfile: Dockerfile
    ports:
      - "8080:8080"
    environment:
      - DATABASE_URL=postgresql://user:password@postgres:5432/performance
      - REDIS_URL=redis://redis:6379
      - ETHEREUM_RPC_URL=https://mainnet.infura.io/v3/YOUR_PROJECT_ID
    depends_on:
      - postgres
      - redis
      - prometheus
    networks:
      - performance-network

  # 区块链性能收集器
  blockchain-collector:
    build:
      context: ./collectors/blockchain
      dockerfile: Dockerfile
    environment:
      - ETHEREUM_RPC_URL=https://mainnet.infura.io/v3/YOUR_PROJECT_ID
    networks:
      - performance-network

  # DeFi性能收集器
  defi-collector:
    build:
      context: ./collectors/defi
      dockerfile: Dockerfile
    environment:
      - UNISWAP_API_URL=https://api.uniswap.org/v1
      - AAVE_API_URL=https://api.aave.com/v1
    networks:
      - performance-network

  # Prometheus监控
  prometheus:
    image: prom/prometheus:latest
    ports:
      - "9090:9090"
    volumes:
      - ./monitoring/prometheus.yml:/etc/prometheus/prometheus.yml
    networks:
      - performance-network

  # Grafana可视化
  grafana:
    image: grafana/grafana:latest
    ports:
      - "3001:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    depends_on:
      - prometheus
    networks:
      - performance-network

  # PostgreSQL数据库
  postgres:
    image: postgres:13
    environment:
      - POSTGRES_DB=performance
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=password
    networks:
      - performance-network

  # Redis缓存
  redis:
    image: redis:6-alpine
    networks:
      - performance-network

networks:
  performance-network:
    driver: bridge
```

## 总结

性能监控系统提供了完整的性能监控、分析和优化解决方案：

1. **多协议数据收集**: 支持区块链、DeFi协议等多种数据源
2. **实时性能分析**: 基于Rust的高性能分析引擎
3. **智能优化建议**: AI驱动的优化建议系统
4. **可视化仪表板**: React + TypeScript的现代化界面
5. **完整部署方案**: Docker + Kubernetes的云原生部署

该系统为Web3应用的性能优化提供了强有力的工具支持，能够实时监控系统性能，及时发现和解决性能瓶颈，提供智能化的优化建议。
