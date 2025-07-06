# 云原生Web3技术栈分析

## 概述

云原生Web3技术栈结合了云计算的优势和Web3的去中心化特性，通过容器化、微服务、服务网格等技术，构建可扩展、高可用的Web3应用。这种架构模式特别适合企业级Web3应用的部署和运维。

## 云原生架构模式

### 1. 容器化部署

```yaml
# docker-compose.yml - 云原生Web3应用
version: '3.8'

services:
  # 区块链节点服务
  blockchain-node:
    image: web3/blockchain-node:latest
    container_name: blockchain-node
    ports:
      - "8545:8545"
      - "8546:8546"
    environment:
      - NODE_ENV=production
      - ETHEREUM_NETWORK=mainnet
      - SYNC_MODE=fast
    volumes:
      - blockchain_data:/data
      - ./config:/config
    networks:
      - web3-network
    deploy:
      resources:
        limits:
          memory: 4G
          cpus: '2.0'
        reservations:
          memory: 2G
          cpus: '1.0'
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8545/health"]
      interval: 30s
      timeout: 10s
      retries: 3

  # API网关服务
  api-gateway:
    image: web3/api-gateway:latest
    container_name: api-gateway
    ports:
      - "8080:8080"
    environment:
      - JWT_SECRET=${JWT_SECRET}
      - RATE_LIMIT=1000
      - CORS_ORIGINS=*
    depends_on:
      - blockchain-node
      - redis
    networks:
      - web3-network
    deploy:
      replicas: 3
      update_config:
        parallelism: 1
        delay: 10s
      restart_policy:
        condition: on-failure

  # 智能合约服务
  smart-contract-service:
    image: web3/smart-contract-service:latest
    container_name: smart-contract-service
    environment:
      - CONTRACT_ADDRESS=${CONTRACT_ADDRESS}
      - PRIVATE_KEY=${PRIVATE_KEY}
      - GAS_LIMIT=3000000
    depends_on:
      - blockchain-node
    networks:
      - web3-network
    deploy:
      replicas: 2

  # 数据分析服务
  analytics-service:
    image: web3/analytics-service:latest
    container_name: analytics-service
    environment:
      - DATABASE_URL=${DATABASE_URL}
      - REDIS_URL=redis://redis:6379
    depends_on:
      - postgres
      - redis
    networks:
      - web3-network
    volumes:
      - analytics_data:/app/data

  # 前端应用
  frontend:
    image: web3/frontend:latest
    container_name: frontend
    ports:
      - "3000:3000"
    environment:
      - REACT_APP_API_URL=http://api-gateway:8080
      - REACT_APP_BLOCKCHAIN_URL=http://blockchain-node:8545
    networks:
      - web3-network
    deploy:
      replicas: 2

  # 数据库
  postgres:
    image: postgres:13-alpine
    container_name: postgres
    environment:
      - POSTGRES_DB=web3
      - POSTGRES_USER=${DB_USER}
      - POSTGRES_PASSWORD=${DB_PASSWORD}
    volumes:
      - postgres_data:/var/lib/postgresql/data
    networks:
      - web3-network

  # Redis缓存
  redis:
    image: redis:6-alpine
    container_name: redis
    command: redis-server --appendonly yes
    volumes:
      - redis_data:/data
    networks:
      - web3-network

  # 监控服务
  prometheus:
    image: prom/prometheus:latest
    container_name: prometheus
    ports:
      - "9090:9090"
    volumes:
      - ./monitoring/prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus_data:/prometheus
    networks:
      - web3-network

  grafana:
    image: grafana/grafana:latest
    container_name: grafana
    ports:
      - "3001:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=${GRAFANA_PASSWORD}
    volumes:
      - grafana_data:/var/lib/grafana
    networks:
      - web3-network

volumes:
  blockchain_data:
  postgres_data:
  redis_data:
  analytics_data:
  prometheus_data:
  grafana_data:

networks:
  web3-network:
    driver: bridge
```

### 2. Kubernetes部署

```yaml
# k8s-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web3-api-gateway
  labels:
    app: web3-api-gateway
spec:
  replicas: 3
  selector:
    matchLabels:
      app: web3-api-gateway
  template:
    metadata:
      labels:
        app: web3-api-gateway
    spec:
      containers:
      - name: api-gateway
        image: web3/api-gateway:latest
        ports:
        - containerPort: 8080
        env:
        - name: JWT_SECRET
          valueFrom:
            secretKeyRef:
              name: web3-secrets
              key: jwt-secret
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: web3-secrets
              key: database-url
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5

---
apiVersion: v1
kind: Service
metadata:
  name: web3-api-service
spec:
  selector:
    app: web3-api-gateway
  ports:
  - protocol: TCP
    port: 80
    targetPort: 8080
  type: LoadBalancer

---
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: web3-api-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: web3-api-gateway
  minReplicas: 3
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
```

## 微服务架构

### 1. 服务拆分策略

```python
# 微服务架构设计
class Web3MicroservicesArchitecture:
    def __init__(self):
        self.services = {
            'blockchain_service': {
                'language': 'Rust',
                'responsibility': '区块链节点管理',
                'endpoints': [
                    '/api/blockchain/blocks',
                    '/api/blockchain/transactions',
                    '/api/blockchain/accounts'
                ],
                'dependencies': ['database', 'cache'],
                'scaling': 'horizontal'
            },
            'smart_contract_service': {
                'language': 'Go',
                'responsibility': '智能合约管理',
                'endpoints': [
                    '/api/contracts/deploy',
                    '/api/contracts/call',
                    '/api/contracts/events'
                ],
                'dependencies': ['blockchain_service'],
                'scaling': 'horizontal'
            },
            'user_service': {
                'language': 'Node.js',
                'responsibility': '用户管理',
                'endpoints': [
                    '/api/users/register',
                    '/api/users/login',
                    '/api/users/profile'
                ],
                'dependencies': ['database', 'auth_service'],
                'scaling': 'horizontal'
            },
            'analytics_service': {
                'language': 'Python',
                'responsibility': '数据分析',
                'endpoints': [
                    '/api/analytics/trends',
                    '/api/analytics/predictions',
                    '/api/analytics/reports'
                ],
                'dependencies': ['database', 'cache', 'ml_service'],
                'scaling': 'horizontal'
            },
            'notification_service': {
                'language': 'Go',
                'responsibility': '通知服务',
                'endpoints': [
                    '/api/notifications/send',
                    '/api/notifications/subscribe',
                    '/api/notifications/history'
                ],
                'dependencies': ['message_queue'],
                'scaling': 'horizontal'
            }
        }
    
    def get_service_dependencies(self) -> Dict:
        """获取服务依赖关系"""
        dependencies = {}
        
        for service_name, service_config in self.services.items():
            dependencies[service_name] = {
                'depends_on': service_config['dependencies'],
                'provides_to': []
            }
        
        # 构建反向依赖关系
        for service_name, deps in dependencies.items():
            for dep in deps['depends_on']:
                if dep in dependencies:
                    dependencies[dep]['provides_to'].append(service_name)
        
        return dependencies
    
    def get_deployment_order(self) -> List[str]:
        """获取部署顺序"""
        dependencies = self.get_service_dependencies()
        visited = set()
        order = []
        
        def dfs(service: str):
            if service in visited:
                return
            visited.add(service)
            
            for dep in dependencies[service]['depends_on']:
                if dep in dependencies:
                    dfs(dep)
            
            order.append(service)
        
        for service in dependencies:
            dfs(service)
        
        return order
```

### 2. 服务通信

```python
# 服务间通信
import asyncio
import aiohttp
import json
from typing import Dict, Any

class ServiceCommunication:
    def __init__(self):
        self.service_urls = {
            'blockchain_service': 'http://blockchain-service:8080',
            'smart_contract_service': 'http://smart-contract-service:8080',
            'user_service': 'http://user-service:8080',
            'analytics_service': 'http://analytics-service:8080',
            'notification_service': 'http://notification-service:8080'
        }
        self.session = None
    
    async def __aenter__(self):
        self.session = aiohttp.ClientSession()
        return self
    
    async def __aexit__(self, exc_type, exc_val, exc_tb):
        if self.session:
            await self.session.close()
    
    async def call_service(self, service_name: str, endpoint: str, 
                          method: str = 'GET', data: Dict = None) -> Dict[str, Any]:
        """调用微服务"""
        if service_name not in self.service_urls:
            raise ValueError(f"Unknown service: {service_name}")
        
        url = f"{self.service_urls[service_name]}{endpoint}"
        
        try:
            if method == 'GET':
                async with self.session.get(url) as response:
                    return await response.json()
            elif method == 'POST':
                async with self.session.post(url, json=data) as response:
                    return await response.json()
            elif method == 'PUT':
                async with self.session.put(url, json=data) as response:
                    return await response.json()
            elif method == 'DELETE':
                async with self.session.delete(url) as response:
                    return await response.json()
        except aiohttp.ClientError as e:
            return {'error': f"Service communication error: {str(e)}"}
    
    async def deploy_contract(self, contract_data: Dict) -> Dict[str, Any]:
        """部署智能合约"""
        # 调用智能合约服务
        result = await self.call_service(
            'smart_contract_service',
            '/api/contracts/deploy',
            'POST',
            contract_data
        )
        
        if 'contract_address' in result:
            # 通知用户服务
            await self.call_service(
                'notification_service',
                '/api/notifications/send',
                'POST',
                {
                    'type': 'contract_deployed',
                    'user_id': contract_data.get('user_id'),
                    'contract_address': result['contract_address']
                }
            )
        
        return result
    
    async def process_transaction(self, tx_data: Dict) -> Dict[str, Any]:
        """处理交易"""
        # 调用区块链服务
        tx_result = await self.call_service(
            'blockchain_service',
            '/api/blockchain/transactions',
            'POST',
            tx_data
        )
        
        if 'success' in tx_result and tx_result['success']:
            # 触发分析服务
            await self.call_service(
                'analytics_service',
                '/api/analytics/process_transaction',
                'POST',
                tx_data
            )
        
        return tx_result
```

## 服务网格

### 1. Istio配置

```yaml
# istio-config.yaml
apiVersion: networking.istio.io/v1alpha3
kind: Gateway
metadata:
  name: web3-gateway
spec:
  selector:
    istio: ingressgateway
  servers:
  - port:
      number: 80
      name: http
      protocol: HTTP
    hosts:
    - "web3.example.com"
---
apiVersion: networking.istio.io/v1alpha3
kind: VirtualService
metadata:
  name: web3-virtual-service
spec:
  hosts:
  - "web3.example.com"
  gateways:
  - web3-gateway
  http:
  - match:
    - uri:
        prefix: "/api/blockchain"
    route:
    - destination:
        host: blockchain-service
        port:
          number: 8080
  - match:
    - uri:
        prefix: "/api/contracts"
    route:
    - destination:
        host: smart-contract-service
        port:
          number: 8080
  - match:
    - uri:
        prefix: "/api/users"
    route:
    - destination:
        host: user-service
        port:
          number: 8080
  - match:
    - uri:
        prefix: "/api/analytics"
    route:
    - destination:
        host: analytics-service
        port:
          number: 8080
---
apiVersion: networking.istio.io/v1alpha3
kind: DestinationRule
metadata:
  name: web3-destination-rules
spec:
  host: blockchain-service
  trafficPolicy:
    loadBalancer:
      simple: ROUND_ROBIN
    connectionPool:
      tcp:
        maxConnections: 100
      http:
        http1MaxPendingRequests: 1000
        maxRequestsPerConnection: 10
    outlierDetection:
      consecutiveErrors: 5
      interval: 10s
      baseEjectionTime: 30s
      maxEjectionPercent: 10
```

### 2. 服务发现和负载均衡

```python
# 服务发现和负载均衡
import consul
import random
from typing import List, Dict

class ServiceDiscovery:
    def __init__(self, consul_host: str = 'localhost', consul_port: int = 8500):
        self.consul = consul.Consul(host=consul_host, port=consul_port)
        self.service_cache = {}
        self.cache_ttl = 30  # 30秒缓存
    
    def register_service(self, service_name: str, service_id: str, 
                        address: str, port: int, tags: List[str] = None):
        """注册服务"""
        self.consul.agent.service.register(
            name=service_name,
            service_id=service_id,
            address=address,
            port=port,
            tags=tags or [],
            check=consul.Check.http(f"http://{address}:{port}/health", "10s")
        )
    
    def deregister_service(self, service_id: str):
        """注销服务"""
        self.consul.agent.service.deregister(service_id)
    
    def get_service_instances(self, service_name: str) -> List[Dict]:
        """获取服务实例"""
        # 检查缓存
        if service_name in self.service_cache:
            cache_time, instances = self.service_cache[service_name]
            if time.time() - cache_time < self.cache_ttl:
                return instances
        
        # 从Consul获取服务实例
        _, services = self.consul.health.service(service_name, passing=True)
        instances = []
        
        for service in services:
            instances.append({
                'id': service['Service']['ID'],
                'address': service['Service']['Address'],
                'port': service['Service']['Port'],
                'tags': service['Service']['Tags']
            })
        
        # 更新缓存
        self.service_cache[service_name] = (time.time(), instances)
        return instances
    
    def load_balance(self, service_name: str, strategy: str = 'round_robin') -> Dict:
        """负载均衡"""
        instances = self.get_service_instances(service_name)
        
        if not instances:
            raise Exception(f"No healthy instances found for service: {service_name}")
        
        if strategy == 'round_robin':
            # 轮询策略
            instance = instances[self._round_robin_index(service_name)]
        elif strategy == 'random':
            # 随机策略
            instance = random.choice(instances)
        elif strategy == 'least_connections':
            # 最少连接策略
            instance = self._get_least_connections_instance(instances)
        else:
            raise ValueError(f"Unknown load balancing strategy: {strategy}")
        
        return instance
    
    def _round_robin_index(self, service_name: str) -> int:
        """轮询索引"""
        if service_name not in self._round_robin_counters:
            self._round_robin_counters[service_name] = 0
        
        instances = self.get_service_instances(service_name)
        index = self._round_robin_counters[service_name] % len(instances)
        self._round_robin_counters[service_name] += 1
        
        return index
    
    def _get_least_connections_instance(self, instances: List[Dict]) -> Dict:
        """获取最少连接的实例"""
        # 这里简化实现，实际应该从监控系统获取连接数
        return instances[0]
```

## 监控和可观测性

### 1. 分布式追踪

```python
# 分布式追踪
import opentracing
import jaeger_client
from functools import wraps

class DistributedTracing:
    def __init__(self, service_name: str):
        config = jaeger_client.Config(
            config={
                'sampler': {
                    'type': 'const',
                    'param': 1,
                },
                'logging': True,
            },
            service_name=service_name
        )
        self.tracer = config.initialize_tracer()
    
    def trace_function(self, operation_name: str = None):
        """函数追踪装饰器"""
        def decorator(func):
            @wraps(func)
            def wrapper(*args, **kwargs):
                span_name = operation_name or func.__name__
                
                with self.tracer.start_span(span_name) as span:
                    # 添加函数参数作为标签
                    span.set_tag('function.args', str(args))
                    span.set_tag('function.kwargs', str(kwargs))
                    
                    try:
                        result = func(*args, **kwargs)
                        span.set_tag('function.result', str(result))
                        return result
                    except Exception as e:
                        span.set_tag('error', True)
                        span.set_tag('error.message', str(e))
                        raise
            
            return wrapper
        return decorator
    
    def trace_service_call(self, service_name: str, endpoint: str):
        """服务调用追踪装饰器"""
        def decorator(func):
            @wraps(func)
            async def wrapper(*args, **kwargs):
                with self.tracer.start_span(f"{service_name}:{endpoint}") as span:
                    span.set_tag('service.name', service_name)
                    span.set_tag('service.endpoint', endpoint)
                    span.set_tag('service.args', str(args))
                    
                    try:
                        result = await func(*args, **kwargs)
                        span.set_tag('service.result', str(result))
                        return result
                    except Exception as e:
                        span.set_tag('error', True)
                        span.set_tag('error.message', str(e))
                        raise
            
            return wrapper
        return decorator

# 使用示例
tracing = DistributedTracing('web3-api-gateway')

@tracing.trace_function('process_transaction')
async def process_transaction(tx_data: Dict) -> Dict:
    # 处理交易逻辑
    return {'status': 'success', 'tx_hash': '0x123...'}

@tracing.trace_service_call('blockchain-service', '/api/transactions')
async def call_blockchain_service(tx_data: Dict) -> Dict:
    # 调用区块链服务
    return {'success': True}
```

### 2. 指标监控

```python
# Prometheus指标监控
from prometheus_client import Counter, Histogram, Gauge, generate_latest
import time

class Web3Metrics:
    def __init__(self):
        # 请求计数器
        self.request_counter = Counter(
            'web3_requests_total',
            'Total number of requests',
            ['service', 'endpoint', 'method', 'status']
        )
        
        # 请求时长直方图
        self.request_duration = Histogram(
            'web3_request_duration_seconds',
            'Request duration in seconds',
            ['service', 'endpoint', 'method']
        )
        
        # 活跃连接数
        self.active_connections = Gauge(
            'web3_active_connections',
            'Number of active connections',
            ['service']
        )
        
        # 区块链指标
        self.block_height = Gauge(
            'web3_block_height',
            'Current block height',
            ['network']
        )
        
        self.transaction_count = Counter(
            'web3_transactions_total',
            'Total number of transactions',
            ['network', 'status']
        )
    
    def track_request(self, service: str, endpoint: str, method: str, status: str):
        """追踪请求"""
        self.request_counter.labels(
            service=service,
            endpoint=endpoint,
            method=method,
            status=status
        ).inc()
    
    def track_request_duration(self, service: str, endpoint: str, method: str, duration: float):
        """追踪请求时长"""
        self.request_duration.labels(
            service=service,
            endpoint=endpoint,
            method=method
        ).observe(duration)
    
    def update_block_height(self, network: str, height: int):
        """更新区块高度"""
        self.block_height.labels(network=network).set(height)
    
    def track_transaction(self, network: str, status: str):
        """追踪交易"""
        self.transaction_count.labels(network=network, status=status).inc()
    
    def get_metrics(self):
        """获取指标"""
        return generate_latest()

# 使用示例
metrics = Web3Metrics()

def track_api_request(func):
    """API请求追踪装饰器"""
    @wraps(func)
    async def wrapper(*args, **kwargs):
        start_time = time.time()
        
        try:
            result = await func(*args, **kwargs)
            status = 'success'
            return result
        except Exception as e:
            status = 'error'
            raise
        finally:
            duration = time.time() - start_time
            metrics.track_request('api-gateway', func.__name__, 'POST', status)
            metrics.track_request_duration('api-gateway', func.__name__, 'POST', duration)
    
    return wrapper
```

## 安全最佳实践

### 1. 容器安全

```yaml
# 安全容器配置
apiVersion: v1
kind: Pod
metadata:
  name: web3-secure-pod
spec:
  securityContext:
    runAsNonRoot: true
    runAsUser: 1000
    fsGroup: 1000
  containers:
  - name: web3-app
    image: web3/app:latest
    securityContext:
      allowPrivilegeEscalation: false
      readOnlyRootFilesystem: true
      capabilities:
        drop:
        - ALL
    volumeMounts:
    - name: tmp
      mountPath: /tmp
    - name: varlog
      mountPath: /var/log
    - name: varlib
      mountPath: /var/lib
  volumes:
  - name: tmp
    emptyDir: {}
  - name: varlog
    emptyDir: {}
  - name: varlib
    emptyDir: {}
```

### 2. 网络策略

```yaml
# 网络策略
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: web3-network-policy
spec:
  podSelector:
    matchLabels:
      app: web3-app
  policyTypes:
  - Ingress
  - Egress
  ingress:
  - from:
    - namespaceSelector:
        matchLabels:
          name: ingress-nginx
    ports:
    - protocol: TCP
      port: 8080
  egress:
  - to:
    - namespaceSelector:
        matchLabels:
          name: database
    ports:
    - protocol: TCP
      port: 5432
  - to:
    - namespaceSelector:
        matchLabels:
          name: redis
    ports:
    - protocol: TCP
      port: 6379
```

## 自动化部署

### 1. CI/CD流水线

```yaml
# .github/workflows/deploy.yml
name: Deploy Web3 Application

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v2
    
    - name: Set up Python
      uses: actions/setup-python@v2
      with:
        python-version: '3.9'
    
    - name: Install dependencies
      run: |
        pip install -r requirements.txt
    
    - name: Run tests
      run: |
        pytest tests/
    
    - name: Run security scan
      run: |
        bandit -r src/
        safety check

  build:
    needs: test
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v2
    
    - name: Set up Docker Buildx
      uses: docker/setup-buildx-action@v1
    
    - name: Login to Docker Hub
      uses: docker/login-action@v1
      with:
        username: ${{ secrets.DOCKER_USERNAME }}
        password: ${{ secrets.DOCKER_PASSWORD }}
    
    - name: Build and push Docker images
      run: |
        docker build -t web3/api-gateway:${{ github.sha }} ./api-gateway
        docker build -t web3/blockchain-service:${{ github.sha }} ./blockchain-service
        docker build -t web3/smart-contract-service:${{ github.sha }} ./smart-contract-service
        
        docker push web3/api-gateway:${{ github.sha }}
        docker push web3/blockchain-service:${{ github.sha }}
        docker push web3/smart-contract-service:${{ github.sha }}

  deploy:
    needs: build
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    steps:
    - uses: actions/checkout@v2
    
    - name: Set up kubectl
      uses: azure/setup-kubectl@v1
    
    - name: Configure kubectl
      run: |
        echo "${{ secrets.KUBE_CONFIG }}" | base64 -d > kubeconfig
        export KUBECONFIG=kubeconfig
    
    - name: Deploy to Kubernetes
      run: |
        kubectl set image deployment/web3-api-gateway api-gateway=web3/api-gateway:${{ github.sha }}
        kubectl set image deployment/web3-blockchain-service blockchain-service=web3/blockchain-service:${{ github.sha }}
        kubectl set image deployment/web3-smart-contract-service smart-contract-service=web3/smart-contract-service:${{ github.sha }}
        
        kubectl rollout status deployment/web3-api-gateway
        kubectl rollout status deployment/web3-blockchain-service
        kubectl rollout status deployment/web3-smart-contract-service
```

### 2. 基础设施即代码

```python
# Terraform配置
import terraform

class Web3Infrastructure:
    def __init__(self):
        self.tf = terraform.Terraform(working_dir="./terraform")
    
    def create_infrastructure(self):
        """创建基础设施"""
        # 创建Kubernetes集群
        self.tf.init()
        self.tf.apply(auto_approve=True)
    
    def destroy_infrastructure(self):
        """销毁基础设施"""
        self.tf.destroy(auto_approve=True)

# terraform/main.tf
"""
terraform {
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 4.0"
    }
    kubernetes = {
      source  = "hashicorp/kubernetes"
      version = "~> 2.0"
    }
  }
}

provider "aws" {
  region = "us-west-2"
}

# EKS集群
resource "aws_eks_cluster" "web3_cluster" {
  name     = "web3-cluster"
  role_arn = aws_iam_role.eks_cluster.arn
  version  = "1.24"

  vpc_config {
    subnet_ids = aws_subnet.web3_subnets[*].id
  }
}

# 节点组
resource "aws_eks_node_group" "web3_nodes" {
  cluster_name    = aws_eks_cluster.web3_cluster.name
  node_group_name = "web3-nodes"
  node_role_arn   = aws_iam_role.eks_nodes.arn
  subnet_ids      = aws_subnet.web3_subnets[*].id

  scaling_config {
    desired_size = 3
    max_size     = 5
    min_size     = 1
  }

  instance_types = ["t3.medium"]
}

# RDS数据库
resource "aws_db_instance" "web3_database" {
  identifier        = "web3-database"
  engine            = "postgres"
  engine_version    = "13.7"
  instance_class    = "db.t3.micro"
  allocated_storage = 20
  
  db_name  = "web3"
  username = var.db_username
  password = var.db_password
  
  vpc_security_group_ids = [aws_security_group.database.id]
  db_subnet_group_name   = aws_db_subnet_group.web3.name
}

# ElastiCache Redis
resource "aws_elasticache_cluster" "web3_redis" {
  cluster_id           = "web3-redis"
  engine               = "redis"
  node_type            = "cache.t3.micro"
  num_cache_nodes      = 1
  parameter_group_name = "default.redis6.x"
  port                 = 6379
}
"""
```

## 最佳实践总结

### 1. 架构设计原则

- **容器化**: 使用Docker容器化所有服务
- **微服务**: 按业务功能拆分服务
- **服务网格**: 使用Istio管理服务通信
- **可观测性**: 实现完整的监控和追踪

### 2. 部署策略

- **蓝绿部署**: 零停机时间部署
- **金丝雀发布**: 渐进式发布新版本
- **自动扩缩容**: 根据负载自动调整实例数
- **多环境管理**: 开发、测试、生产环境分离

### 3. 安全考虑

- **容器安全**: 最小权限原则
- **网络隔离**: 使用网络策略控制流量
- **密钥管理**: 使用Kubernetes Secrets
- **安全扫描**: 集成安全扫描工具

### 4. 运维策略

- **自动化部署**: CI/CD流水线
- **基础设施即代码**: 使用Terraform
- **监控告警**: 全面的监控体系
- **故障恢复**: 自动故障检测和恢复

## 参考文献

1. "Cloud Native Web3" - CNCF Documentation
2. "Kubernetes for Web3" - Kubernetes Documentation
3. "Service Mesh Architecture" - Istio Documentation
4. "Container Security" - Docker Documentation
5. "Infrastructure as Code" - HashiCorp Documentation
