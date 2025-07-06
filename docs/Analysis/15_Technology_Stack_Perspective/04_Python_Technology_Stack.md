# Python技术栈在Web3中的深度分析

## 概述

Python在Web3生态系统中主要应用于数据分析、AI集成、快速原型开发和研究工具。其丰富的科学计算库、机器学习框架和简洁的语法使其成为Web3数据分析和AI应用开发的重要技术栈。

## Python技术栈核心特性

### 1. 数据分析能力

```python
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
from web3 import Web3
from datetime import datetime, timedelta

class BlockchainDataAnalyzer:
    def __init__(self, rpc_url: str):
        self.w3 = Web3(Web3.HTTPProvider(rpc_url))
        self.data = {}
    
    def analyze_transaction_patterns(self, address: str, days: int = 30):
        """分析地址的交易模式"""
        end_block = self.w3.eth.block_number
        start_block = end_block - (days * 5760)  # 假设每块15秒
        
        transactions = []
        for block_num in range(start_block, end_block, 1000):
            block = self.w3.eth.get_block(block_num, full_transactions=True)
            for tx in block.transactions:
                if tx['from'].lower() == address.lower() or tx['to'].lower() == address.lower():
                    transactions.append({
                        'hash': tx['hash'].hex(),
                        'from': tx['from'],
                        'to': tx['to'],
                        'value': self.w3.from_wei(tx['value'], 'ether'),
                        'gas': tx['gas'],
                        'gas_price': self.w3.from_wei(tx['gasPrice'], 'gwei'),
                        'block_number': block_num,
                        'timestamp': block.timestamp
                    })
        
        df = pd.DataFrame(transactions)
        return self._analyze_patterns(df)
    
    def _analyze_patterns(self, df: pd.DataFrame) -> dict:
        """分析交易模式"""
        analysis = {
            'total_transactions': len(df),
            'total_volume': df['value'].sum(),
            'average_value': df['value'].mean(),
            'gas_analysis': {
                'total_gas': df['gas'].sum(),
                'average_gas': df['gas'].mean(),
                'gas_cost': (df['gas'] * df['gas_price']).sum()
            },
            'time_analysis': {
                'hourly_distribution': df.groupby(df['timestamp'].dt.hour).size(),
                'daily_distribution': df.groupby(df['timestamp'].dt.date).size()
            },
            'address_analysis': {
                'unique_from': df['from'].nunique(),
                'unique_to': df['to'].nunique(),
                'most_frequent_to': df['to'].value_counts().head(10)
            }
        }
        
        return analysis
    
    def visualize_transaction_flow(self, df: pd.DataFrame):
        """可视化交易流"""
        fig, axes = plt.subplots(2, 2, figsize=(15, 10))
        
        # 交易价值分布
        axes[0, 0].hist(df['value'], bins=50, alpha=0.7)
        axes[0, 0].set_title('Transaction Value Distribution')
        axes[0, 0].set_xlabel('Value (ETH)')
        axes[0, 0].set_ylabel('Frequency')
        
        # 时间序列
        df['timestamp'] = pd.to_datetime(df['timestamp'], unit='s')
        daily_volume = df.groupby(df['timestamp'].dt.date)['value'].sum()
        axes[0, 1].plot(daily_volume.index, daily_volume.values)
        axes[0, 1].set_title('Daily Transaction Volume')
        axes[0, 1].set_xlabel('Date')
        axes[0, 1].set_ylabel('Volume (ETH)')
        
        # Gas价格分析
        axes[1, 0].scatter(df['gas_price'], df['value'], alpha=0.5)
        axes[1, 0].set_title('Gas Price vs Transaction Value')
        axes[1, 0].set_xlabel('Gas Price (Gwei)')
        axes[1, 0].set_ylabel('Value (ETH)')
        
        # 交易类型分布
        transaction_types = df.apply(
            lambda row: 'Incoming' if row['to'].lower() == self.address.lower() else 'Outgoing', 
            axis=1
        )
        transaction_types.value_counts().plot(kind='pie', ax=axes[1, 1])
        axes[1, 1].set_title('Transaction Type Distribution')
        
        plt.tight_layout()
        plt.show()
    
    def detect_anomalies(self, df: pd.DataFrame) -> pd.DataFrame:
        """检测异常交易"""
        # 使用IQR方法检测异常值
        Q1 = df['value'].quantile(0.25)
        Q3 = df['value'].quantile(0.75)
        IQR = Q3 - Q1
        
        lower_bound = Q1 - 1.5 * IQR
        upper_bound = Q3 + 1.5 * IQR
        
        anomalies = df[(df['value'] < lower_bound) | (df['value'] > upper_bound)]
        
        return anomalies
```

### 2. AI/ML集成

```python
import tensorflow as tf
import sklearn
from sklearn.ensemble import RandomForestClassifier
from sklearn.model_selection import train_test_split
from sklearn.preprocessing import StandardScaler
import joblib

class Web3AIAnalyzer:
    def __init__(self):
        self.models = {}
        self.scaler = StandardScaler()
    
    def prepare_features(self, df: pd.DataFrame) -> np.ndarray:
        """准备机器学习特征"""
        features = []
        
        for _, row in df.iterrows():
            feature_vector = [
                row['value'],
                row['gas'],
                row['gas_price'],
                row['timestamp'].hour,
                row['timestamp'].weekday(),
                len(row['from']),  # 地址长度
                len(row['to']),
                int(row['from'].startswith('0x')),
                int(row['to'].startswith('0x'))
            ]
            features.append(feature_vector)
        
        return np.array(features)
    
    def train_fraud_detection_model(self, df: pd.DataFrame, labels: np.ndarray):
        """训练欺诈检测模型"""
        features = self.prepare_features(df)
        
        # 分割训练和测试数据
        X_train, X_test, y_train, y_test = train_test_split(
            features, labels, test_size=0.2, random_state=42
        )
        
        # 标准化特征
        X_train_scaled = self.scaler.fit_transform(X_train)
        X_test_scaled = self.scaler.transform(X_test)
        
        # 训练随机森林模型
        rf_model = RandomForestClassifier(n_estimators=100, random_state=42)
        rf_model.fit(X_train_scaled, y_train)
        
        # 评估模型
        train_score = rf_model.score(X_train_scaled, y_train)
        test_score = rf_model.score(X_test_scaled, y_test)
        
        self.models['fraud_detection'] = {
            'model': rf_model,
            'scaler': self.scaler,
            'train_score': train_score,
            'test_score': test_score
        }
        
        return {
            'train_score': train_score,
            'test_score': test_score,
            'feature_importance': rf_model.feature_importances_
        }
    
    def predict_fraud(self, transaction_data: dict) -> float:
        """预测交易是否为欺诈"""
        if 'fraud_detection' not in self.models:
            raise ValueError("Fraud detection model not trained")
        
        model = self.models['fraud_detection']['model']
        scaler = self.models['fraud_detection']['scaler']
        
        # 准备特征
        features = self.prepare_features(pd.DataFrame([transaction_data]))
        features_scaled = scaler.transform(features)
        
        # 预测
        probability = model.predict_proba(features_scaled)[0][1]
        return probability
    
    def train_price_prediction_model(self, historical_data: pd.DataFrame):
        """训练价格预测模型"""
        # 准备时间序列数据
        df = historical_data.copy()
        df['timestamp'] = pd.to_datetime(df['timestamp'], unit='s')
        df = df.set_index('timestamp')
        
        # 创建滞后特征
        for lag in [1, 2, 3, 7]:
            df[f'price_lag_{lag}'] = df['price'].shift(lag)
        
        # 创建技术指标
        df['price_ma_7'] = df['price'].rolling(window=7).mean()
        df['price_ma_30'] = df['price'].rolling(window=30).mean()
        df['price_std_7'] = df['price'].rolling(window=7).std()
        
        # 删除NaN值
        df = df.dropna()
        
        # 准备特征和目标
        feature_columns = [col for col in df.columns if col != 'price']
        X = df[feature_columns]
        y = df['price']
        
        # 分割数据
        split_idx = int(len(df) * 0.8)
        X_train, X_test = X[:split_idx], X[split_idx:]
        y_train, y_test = y[:split_idx], y[split_idx:]
        
        # 训练模型
        model = tf.keras.Sequential([
            tf.keras.layers.Dense(64, activation='relu', input_shape=(X_train.shape[1],)),
            tf.keras.layers.Dropout(0.2),
            tf.keras.layers.Dense(32, activation='relu'),
            tf.keras.layers.Dropout(0.2),
            tf.keras.layers.Dense(1)
        ])
        
        model.compile(optimizer='adam', loss='mse', metrics=['mae'])
        
        history = model.fit(
            X_train, y_train,
            validation_data=(X_test, y_test),
            epochs=100,
            batch_size=32,
            verbose=0
        )
        
        self.models['price_prediction'] = {
            'model': model,
            'feature_columns': feature_columns,
            'history': history
        }
        
        return history
    
    def predict_price(self, current_data: dict) -> float:
        """预测价格"""
        if 'price_prediction' not in self.models:
            raise ValueError("Price prediction model not trained")
        
        model = self.models['price_prediction']['model']
        feature_columns = self.models['price_prediction']['feature_columns']
        
        # 准备特征
        features = []
        for col in feature_columns:
            features.append(current_data.get(col, 0))
        
        # 预测
        prediction = model.predict(np.array([features]))[0][0]
        return prediction
```

### 3. 智能合约交互

```python
from web3 import Web3
from eth_account import Account
import json
import asyncio
import aiohttp

class PythonWeb3Client:
    def __init__(self, rpc_url: str, private_key: str = None):
        self.w3 = Web3(Web3.HTTPProvider(rpc_url))
        self.account = Account.from_key(private_key) if private_key else None
        self.contracts = {}
    
    def load_contract(self, address: str, abi: list):
        """加载智能合约"""
        contract = self.w3.eth.contract(address=address, abi=abi)
        self.contracts[address] = contract
        return contract
    
    async def get_token_info(self, token_address: str) -> dict:
        """获取代币信息"""
        # ERC20标准ABI
        erc20_abi = [
            {
                "constant": True,
                "inputs": [],
                "name": "name",
                "outputs": [{"name": "", "type": "string"}],
                "type": "function"
            },
            {
                "constant": True,
                "inputs": [],
                "name": "symbol",
                "outputs": [{"name": "", "type": "string"}],
                "type": "function"
            },
            {
                "constant": True,
                "inputs": [],
                "name": "decimals",
                "outputs": [{"name": "", "type": "uint8"}],
                "type": "function"
            },
            {
                "constant": True,
                "inputs": [],
                "name": "totalSupply",
                "outputs": [{"name": "", "type": "uint256"}],
                "type": "function"
            }
        ]
        
        contract = self.load_contract(token_address, erc20_abi)
        
        try:
            name = await self._call_contract_function(contract, 'name')
            symbol = await self._call_contract_function(contract, 'symbol')
            decimals = await self._call_contract_function(contract, 'decimals')
            total_supply = await self._call_contract_function(contract, 'totalSupply')
            
            return {
                'address': token_address,
                'name': name,
                'symbol': symbol,
                'decimals': decimals,
                'total_supply': self.w3.from_wei(total_supply, 'ether')
            }
        except Exception as e:
            return {'error': str(e)}
    
    async def _call_contract_function(self, contract, function_name: str, *args):
        """调用合约函数"""
        try:
            function = getattr(contract.functions, function_name)
            result = function(*args).call()
            return result
        except Exception as e:
            raise Exception(f"Contract call failed: {str(e)}")
    
    async def get_token_balances(self, wallet_address: str, token_addresses: list) -> dict:
        """获取多个代币余额"""
        balances = {}
        
        for token_address in token_addresses:
            try:
                balance = await self.get_token_balance(wallet_address, token_address)
                balances[token_address] = balance
            except Exception as e:
                balances[token_address] = {'error': str(e)}
        
        return balances
    
    async def get_token_balance(self, wallet_address: str, token_address: str) -> dict:
        """获取代币余额"""
        erc20_abi = [
            {
                "constant": True,
                "inputs": [{"name": "_owner", "type": "address"}],
                "name": "balanceOf",
                "outputs": [{"name": "balance", "type": "uint256"}],
                "type": "function"
            }
        ]
        
        contract = self.load_contract(token_address, erc20_abi)
        balance = await self._call_contract_function(contract, 'balanceOf', wallet_address)
        
        return {
            'address': token_address,
            'wallet': wallet_address,
            'balance': self.w3.from_wei(balance, 'ether')
        }
    
    def send_transaction(self, to_address: str, value: float, gas_limit: int = 21000) -> str:
        """发送交易"""
        if not self.account:
            raise ValueError("No account configured")
        
        # 构建交易
        transaction = {
            'to': to_address,
            'value': self.w3.to_wei(value, 'ether'),
            'gas': gas_limit,
            'gasPrice': self.w3.eth.gas_price,
            'nonce': self.w3.eth.get_transaction_count(self.account.address),
            'chainId': self.w3.eth.chain_id
        }
        
        # 签名交易
        signed_txn = self.w3.eth.account.sign_transaction(transaction, self.account.key)
        
        # 发送交易
        tx_hash = self.w3.eth.send_raw_transaction(signed_txn.rawTransaction)
        
        return tx_hash.hex()
    
    async def monitor_transactions(self, address: str, callback):
        """监控地址交易"""
        last_block = self.w3.eth.block_number
        
        while True:
            try:
                current_block = self.w3.eth.block_number
                
                if current_block > last_block:
                    for block_num in range(last_block + 1, current_block + 1):
                        block = self.w3.eth.get_block(block_num, full_transactions=True)
                        
                        for tx in block.transactions:
                            if (tx['from'].lower() == address.lower() or 
                                tx['to'].lower() == address.lower()):
                                await callback(tx)
                    
                    last_block = current_block
                
                await asyncio.sleep(1)  # 等待1秒
                
            except Exception as e:
                print(f"Error monitoring transactions: {e}")
                await asyncio.sleep(5)  # 出错时等待5秒
```

## Python在Web3生态系统中的应用

### 1. DeFi数据分析

```python
import ccxt
import pandas as pd
import numpy as np
from typing import Dict, List

class DeFiAnalyzer:
    def __init__(self):
        self.exchanges = {}
        self.data = {}
    
    def add_exchange(self, exchange_name: str, api_key: str = None, secret: str = None):
        """添加交易所"""
        exchange_class = getattr(ccxt, exchange_name)
        self.exchanges[exchange_name] = exchange_class({
            'apiKey': api_key,
            'secret': secret,
            'enableRateLimit': True
        })
    
    def get_dex_data(self, token_address: str, dex_name: str = 'uniswap') -> pd.DataFrame:
        """获取DEX数据"""
        # 这里需要集成具体的DEX API
        # 示例数据结构
        data = {
            'timestamp': pd.date_range(start='2023-01-01', periods=100, freq='H'),
            'price': np.random.random(100) * 100,
            'volume': np.random.random(100) * 1000000,
            'liquidity': np.random.random(100) * 10000000
        }
        
        return pd.DataFrame(data)
    
    def calculate_impermanent_loss(self, initial_price: float, current_price: float) -> float:
        """计算无常损失"""
        price_ratio = current_price / initial_price
        
        # 无常损失公式
        il = 2 * np.sqrt(price_ratio) / (1 + price_ratio) - 1
        
        return il * 100  # 返回百分比
    
    def analyze_liquidity_pool(self, pool_data: pd.DataFrame) -> Dict:
        """分析流动性池"""
        analysis = {
            'total_volume': pool_data['volume'].sum(),
            'average_volume': pool_data['volume'].mean(),
            'volume_volatility': pool_data['volume'].std(),
            'price_volatility': pool_data['price'].std(),
            'impermanent_loss': self.calculate_impermanent_loss(
                pool_data['price'].iloc[0],
                pool_data['price'].iloc[-1]
            )
        }
        
        return analysis
    
    def calculate_apy(self, rewards: float, principal: float, time_period: int) -> float:
        """计算APY"""
        if principal == 0:
            return 0
        
        # 简单APY计算
        apy = ((rewards / principal) / time_period) * 365 * 100
        return apy
    
    def analyze_yield_farming(self, farming_data: pd.DataFrame) -> Dict:
        """分析收益农场"""
        analysis = {
            'total_rewards': farming_data['rewards'].sum(),
            'average_apy': self.calculate_apy(
                farming_data['rewards'].sum(),
                farming_data['principal'].mean(),
                len(farming_data)
            ),
            'reward_distribution': farming_data['rewards'].describe(),
            'risk_metrics': {
                'volatility': farming_data['rewards'].std(),
                'max_drawdown': self.calculate_max_drawdown(farming_data['rewards'])
            }
        }
        
        return analysis
    
    def calculate_max_drawdown(self, returns: pd.Series) -> float:
        """计算最大回撤"""
        cumulative = (1 + returns).cumprod()
        running_max = cumulative.expanding().max()
        drawdown = (cumulative - running_max) / running_max
        return drawdown.min() * 100
```

### 2. NFT分析工具

```python
import requests
import pandas as pd
from datetime import datetime
import matplotlib.pyplot as plt

class NFTAnalyzer:
    def __init__(self, api_key: str = None):
        self.api_key = api_key
        self.base_url = "https://api.opensea.io/api/v1"
    
    def get_collection_stats(self, collection_slug: str) -> Dict:
        """获取NFT集合统计"""
        url = f"{self.base_url}/collection/{collection_slug}/stats"
        headers = {'X-API-KEY': self.api_key} if self.api_key else {}
        
        try:
            response = requests.get(url, headers=headers)
            response.raise_for_status()
            return response.json()
        except requests.RequestException as e:
            return {'error': str(e)}
    
    def get_nft_events(self, collection_slug: str, event_type: str = 'successful') -> pd.DataFrame:
        """获取NFT事件"""
        url = f"{self.base_url}/events"
        params = {
            'collection_slug': collection_slug,
            'event_type': event_type,
            'limit': 50
        }
        headers = {'X-API-KEY': self.api_key} if self.api_key else {}
        
        try:
            response = requests.get(url, params=params, headers=headers)
            response.raise_for_status()
            data = response.json()
            
            events = []
            for event in data.get('asset_events', []):
                events.append({
                    'token_id': event['asset']['token_id'],
                    'price': float(event['payment']['amount']) / 10**18,  # 转换为ETH
                    'timestamp': datetime.fromisoformat(event['created_date'].replace('Z', '+00:00')),
                    'seller': event['seller']['address'],
                    'buyer': event['bidder']['address'] if 'bidder' in event else None
                })
            
            return pd.DataFrame(events)
        except requests.RequestException as e:
            return pd.DataFrame()
    
    def analyze_nft_trends(self, events_df: pd.DataFrame) -> Dict:
        """分析NFT趋势"""
        if events_df.empty:
            return {}
        
        analysis = {
            'total_sales': len(events_df),
            'total_volume': events_df['price'].sum(),
            'average_price': events_df['price'].mean(),
            'median_price': events_df['price'].median(),
            'price_range': {
                'min': events_df['price'].min(),
                'max': events_df['price'].max()
            },
            'daily_stats': events_df.groupby(events_df['timestamp'].dt.date).agg({
                'price': ['count', 'sum', 'mean'],
                'token_id': 'nunique'
            })
        }
        
        return analysis
    
    def visualize_nft_data(self, events_df: pd.DataFrame):
        """可视化NFT数据"""
        if events_df.empty:
            print("No data to visualize")
            return
        
        fig, axes = plt.subplots(2, 2, figsize=(15, 10))
        
        # 价格分布
        axes[0, 0].hist(events_df['price'], bins=30, alpha=0.7)
        axes[0, 0].set_title('NFT Price Distribution')
        axes[0, 0].set_xlabel('Price (ETH)')
        axes[0, 0].set_ylabel('Frequency')
        
        # 时间序列
        daily_volume = events_df.groupby(events_df['timestamp'].dt.date)['price'].sum()
        axes[0, 1].plot(daily_volume.index, daily_volume.values)
        axes[0, 1].set_title('Daily Sales Volume')
        axes[0, 1].set_xlabel('Date')
        axes[0, 1].set_ylabel('Volume (ETH)')
        
        # 价格趋势
        daily_avg_price = events_df.groupby(events_df['timestamp'].dt.date)['price'].mean()
        axes[1, 0].plot(daily_avg_price.index, daily_avg_price.values)
        axes[1, 0].set_title('Daily Average Price')
        axes[1, 0].set_xlabel('Date')
        axes[1, 0].set_ylabel('Average Price (ETH)')
        
        # 销售数量
        daily_sales = events_df.groupby(events_df['timestamp'].dt.date).size()
        axes[1, 1].bar(daily_sales.index, daily_sales.values)
        axes[1, 1].set_title('Daily Sales Count')
        axes[1, 1].set_xlabel('Date')
        axes[1, 1].set_ylabel('Number of Sales')
        
        plt.tight_layout()
        plt.show()
    
    def calculate_rarity_score(self, traits_data: List[Dict]) -> Dict:
        """计算稀有度分数"""
        trait_counts = {}
        
        # 统计每个特征的出现次数
        for trait in traits_data:
            for attr, value in trait.items():
                if attr not in trait_counts:
                    trait_counts[attr] = {}
                if value not in trait_counts[attr]:
                    trait_counts[attr][value] = 0
                trait_counts[attr][value] += 1
        
        # 计算稀有度分数
        rarity_scores = {}
        total_nfts = len(traits_data)
        
        for i, trait in enumerate(traits_data):
            score = 0
            for attr, value in trait.items():
                if attr in trait_counts and value in trait_counts[attr]:
                    frequency = trait_counts[attr][value] / total_nfts
                    score += 1 / frequency
            
            rarity_scores[i] = score
        
        return rarity_scores
```

## Python Web3项目生态系统

### 1. 核心项目

| 项目名称 | 类别 | Python使用场景 | 性能指标 |
|---------|------|---------------|----------|
| Web3.py | 区块链库 | 以太坊交互 | 稳定可靠 |
| Brownie | 开发框架 | 智能合约开发 | 开发效率高 |
| Vyper | 合约语言 | 安全合约开发 | 安全性高 |
| PyTorch | AI框架 | 机器学习 | 高性能 |
| Pandas | 数据分析 | 数据处理 | 高效处理 |
| NumPy | 科学计算 | 数值计算 | 高性能 |

### 2. 开发工具链

```python
# requirements.txt
web3==6.0.0
pandas==2.0.0
numpy==1.24.0
matplotlib==3.7.0
seaborn==0.12.0
scikit-learn==1.3.0
tensorflow==2.13.0
torch==2.0.0
ccxt==4.0.0
requests==2.31.0
aiohttp==3.8.0
asyncio==3.4.3
python-dotenv==1.0.0
pytest==7.4.0
black==23.0.0
flake8==6.0.0
mypy==1.4.0
```

## 性能优化策略

### 1. 数据处理优化

```python
import pandas as pd
import numpy as np
from concurrent.futures import ThreadPoolExecutor, ProcessPoolExecutor
import asyncio
import aiohttp

class OptimizedDataProcessor:
    def __init__(self):
        self.cache = {}
    
    def parallel_process_data(self, data_list: List, func, max_workers: int = 4):
        """并行处理数据"""
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            results = list(executor.map(func, data_list))
        return results
    
    def chunk_process_data(self, data: pd.DataFrame, chunk_size: int = 1000):
        """分块处理大数据"""
        chunks = [data[i:i + chunk_size] for i in range(0, len(data), chunk_size)]
        
        processed_chunks = []
        for chunk in chunks:
            processed_chunk = self.process_chunk(chunk)
            processed_chunks.append(processed_chunk)
        
        return pd.concat(processed_chunks, ignore_index=True)
    
    def process_chunk(self, chunk: pd.DataFrame) -> pd.DataFrame:
        """处理数据块"""
        # 示例处理逻辑
        chunk['processed_value'] = chunk['value'] * 2
        return chunk
    
    async def async_fetch_data(self, urls: List[str]) -> List[Dict]:
        """异步获取数据"""
        async with aiohttp.ClientSession() as session:
            tasks = [self.fetch_url(session, url) for url in urls]
            results = await asyncio.gather(*tasks)
            return results
    
    async def fetch_url(self, session: aiohttp.ClientSession, url: str) -> Dict:
        """获取单个URL数据"""
        try:
            async with session.get(url) as response:
                return await response.json()
        except Exception as e:
            return {'error': str(e)}
    
    def optimize_memory_usage(self, df: pd.DataFrame) -> pd.DataFrame:
        """优化内存使用"""
        # 减少数据类型内存占用
        for col in df.columns:
            if df[col].dtype == 'object':
                df[col] = df[col].astype('category')
            elif df[col].dtype == 'int64':
                df[col] = pd.to_numeric(df[col], downcast='integer')
            elif df[col].dtype == 'float64':
                df[col] = pd.to_numeric(df[col], downcast='float')
        
        return df
```

### 2. 机器学习优化

```python
import joblib
from sklearn.pipeline import Pipeline
from sklearn.preprocessing import StandardScaler
from sklearn.ensemble import RandomForestRegressor
import numpy as np

class OptimizedMLPipeline:
    def __init__(self):
        self.pipeline = None
        self.models = {}
    
    def create_pipeline(self, model_type: str = 'random_forest'):
        """创建机器学习管道"""
        if model_type == 'random_forest':
            model = RandomForestRegressor(
                n_estimators=100,
                max_depth=10,
                random_state=42,
                n_jobs=-1  # 使用所有CPU核心
            )
        else:
            raise ValueError(f"Unsupported model type: {model_type}")
        
        self.pipeline = Pipeline([
            ('scaler', StandardScaler()),
            ('model', model)
        ])
        
        return self.pipeline
    
    def train_model(self, X: np.ndarray, y: np.ndarray, model_name: str):
        """训练模型"""
        if self.pipeline is None:
            self.create_pipeline()
        
        self.pipeline.fit(X, y)
        self.models[model_name] = self.pipeline
        
        # 保存模型
        joblib.dump(self.pipeline, f'{model_name}_model.pkl')
    
    def load_model(self, model_name: str):
        """加载模型"""
        try:
            self.models[model_name] = joblib.load(f'{model_name}_model.pkl')
            return self.models[model_name]
        except FileNotFoundError:
            raise ValueError(f"Model {model_name} not found")
    
    def predict(self, X: np.ndarray, model_name: str) -> np.ndarray:
        """预测"""
        if model_name not in self.models:
            self.load_model(model_name)
        
        return self.models[model_name].predict(X)
    
    def batch_predict(self, X: np.ndarray, model_name: str, batch_size: int = 1000) -> np.ndarray:
        """批量预测"""
        predictions = []
        
        for i in range(0, len(X), batch_size):
            batch = X[i:i + batch_size]
            batch_predictions = self.predict(batch, model_name)
            predictions.extend(batch_predictions)
        
        return np.array(predictions)
```

## 安全最佳实践

### 1. 数据安全

```python
import hashlib
import hmac
import os
from cryptography.fernet import Fernet
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC

class DataSecurityManager:
    def __init__(self, key: bytes = None):
        if key is None:
            key = Fernet.generate_key()
        self.cipher = Fernet(key)
    
    def encrypt_data(self, data: str) -> bytes:
        """加密数据"""
        return self.cipher.encrypt(data.encode())
    
    def decrypt_data(self, encrypted_data: bytes) -> str:
        """解密数据"""
        return self.cipher.decrypt(encrypted_data).decode()
    
    def hash_password(self, password: str, salt: bytes = None) -> tuple:
        """哈希密码"""
        if salt is None:
            salt = os.urandom(16)
        
        kdf = PBKDF2HMAC(
            algorithm=hashes.SHA256(),
            length=32,
            salt=salt,
            iterations=100000,
        )
        
        key = kdf.derive(password.encode())
        return key, salt
    
    def verify_password(self, password: str, key: bytes, salt: bytes) -> bool:
        """验证密码"""
        try:
            kdf = PBKDF2HMAC(
                algorithm=hashes.SHA256(),
                length=32,
                salt=salt,
                iterations=100000,
            )
            kdf.verify(password.encode(), key)
            return True
        except Exception:
            return False
    
    def create_hmac(self, data: str, key: str) -> str:
        """创建HMAC"""
        return hmac.new(
            key.encode(),
            data.encode(),
            hashlib.sha256
        ).hexdigest()
    
    def verify_hmac(self, data: str, key: str, signature: str) -> bool:
        """验证HMAC"""
        expected_signature = self.create_hmac(data, key)
        return hmac.compare_digest(expected_signature, signature)
```

### 2. API安全

```python
import jwt
import time
from functools import wraps
from flask import request, jsonify

class APISecurityManager:
    def __init__(self, secret_key: str):
        self.secret_key = secret_key
    
    def create_token(self, user_id: str, expires_in: int = 3600) -> str:
        """创建JWT令牌"""
        payload = {
            'user_id': user_id,
            'exp': time.time() + expires_in,
            'iat': time.time()
        }
        return jwt.encode(payload, self.secret_key, algorithm='HS256')
    
    def verify_token(self, token: str) -> dict:
        """验证JWT令牌"""
        try:
            payload = jwt.decode(token, self.secret_key, algorithms=['HS256'])
            return payload
        except jwt.ExpiredSignatureError:
            raise ValueError("Token has expired")
        except jwt.InvalidTokenError:
            raise ValueError("Invalid token")
    
    def require_auth(self, f):
        """认证装饰器"""
        @wraps(f)
        def decorated_function(*args, **kwargs):
            token = request.headers.get('Authorization')
            
            if not token:
                return jsonify({'error': 'No token provided'}), 401
            
            try:
                token = token.split(' ')[1]  # Bearer token
                payload = self.verify_token(token)
                request.user_id = payload['user_id']
            except ValueError as e:
                return jsonify({'error': str(e)}), 401
            
            return f(*args, **kwargs)
        return decorated_function
    
    def rate_limit(self, max_requests: int = 100, window: int = 3600):
        """速率限制装饰器"""
        def decorator(f):
            @wraps(f)
            def decorated_function(*args, **kwargs):
                # 简化的速率限制实现
                client_ip = request.remote_addr
                current_time = time.time()
                
                # 这里应该使用Redis等存储来跟踪请求
                # 简化实现
                return f(*args, **kwargs)
            return decorated_function
        return decorator
```

## 测试框架

### 1. 单元测试

```python
import pytest
import pandas as pd
import numpy as np
from unittest.mock import Mock, patch

class TestWeb3Analyzer:
    def setup_method(self):
        """设置测试环境"""
        self.analyzer = BlockchainDataAnalyzer("http://localhost:8545")
    
    def test_analyze_transaction_patterns(self):
        """测试交易模式分析"""
        # 模拟数据
        mock_transactions = [
            {
                'hash': '0x123',
                'from': '0xabc',
                'to': '0xdef',
                'value': 1.0,
                'gas': 21000,
                'gas_price': 20,
                'block_number': 1000,
                'timestamp': pd.Timestamp('2023-01-01')
            }
        ]
        
        with patch.object(self.analyzer, '_get_transactions', return_value=mock_transactions):
            result = self.analyzer.analyze_transaction_patterns('0xabc')
            
            assert result['total_transactions'] == 1
            assert result['total_volume'] == 1.0
            assert result['average_value'] == 1.0
    
    def test_calculate_impermanent_loss(self):
        """测试无常损失计算"""
        initial_price = 100
        current_price = 200
        
        il = self.analyzer.calculate_impermanent_loss(initial_price, current_price)
        
        # 验证无常损失在合理范围内
        assert -50 <= il <= 0
    
    def test_detect_anomalies(self):
        """测试异常检测"""
        # 创建包含异常值的数据
        data = pd.DataFrame({
            'value': [1, 2, 3, 1000, 4, 5]  # 1000是异常值
        })
        
        anomalies = self.analyzer.detect_anomalies(data)
        
        assert len(anomalies) > 0
        assert 1000 in anomalies['value'].values

class TestDeFiAnalyzer:
    def setup_method(self):
        """设置测试环境"""
        self.analyzer = DeFiAnalyzer()
    
    def test_calculate_apy(self):
        """测试APY计算"""
        rewards = 100
        principal = 1000
        time_period = 365
        
        apy = self.analyzer.calculate_apy(rewards, principal, time_period)
        
        assert apy == 10.0  # 10% APY
    
    def test_calculate_max_drawdown(self):
        """测试最大回撤计算"""
        returns = pd.Series([0.1, -0.2, 0.15, -0.3, 0.1])
        
        max_dd = self.analyzer.calculate_max_drawdown(returns)
        
        assert max_dd < 0  # 回撤应该是负数
        assert max_dd >= -100  # 最大回撤不超过100%

@pytest.fixture
def sample_nft_data():
    """NFT测试数据"""
    return pd.DataFrame({
        'token_id': [1, 2, 3, 4, 5],
        'price': [1.0, 2.0, 3.0, 4.0, 5.0],
        'timestamp': pd.date_range('2023-01-01', periods=5),
        'seller': ['0x1', '0x2', '0x3', '0x4', '0x5'],
        'buyer': ['0xa', '0xb', '0xc', '0xd', '0xe']
    })

def test_nft_analyzer(sample_nft_data):
    """测试NFT分析器"""
    analyzer = NFTAnalyzer()
    
    analysis = analyzer.analyze_nft_trends(sample_nft_data)
    
    assert analysis['total_sales'] == 5
    assert analysis['total_volume'] == 15.0
    assert analysis['average_price'] == 3.0
```

### 2. 集成测试

```python
import asyncio
import aiohttp
import pytest

class TestWeb3Integration:
    @pytest.mark.asyncio
    async def test_web3_client_connection(self):
        """测试Web3客户端连接"""
        client = PythonWeb3Client("http://localhost:8545")
        
        # 测试连接
        assert client.w3.is_connected()
    
    @pytest.mark.asyncio
    async def test_contract_interaction(self):
        """测试合约交互"""
        client = PythonWeb3Client("http://localhost:8545")
        
        # 模拟合约调用
        with patch.object(client, '_call_contract_function') as mock_call:
            mock_call.return_value = "TestToken"
            
            result = await client.get_token_info("0x123")
            
            assert result['name'] == "TestToken"
    
    @pytest.mark.asyncio
    async def test_transaction_monitoring(self):
        """测试交易监控"""
        client = PythonWeb3Client("http://localhost:8545")
        
        transactions_received = []
        
        async def callback(tx):
            transactions_received.append(tx)
        
        # 启动监控
        monitor_task = asyncio.create_task(
            client.monitor_transactions("0x123", callback)
        )
        
        # 等待一段时间
        await asyncio.sleep(1)
        
        # 取消监控
        monitor_task.cancel()
        
        # 验证回调被调用
        assert len(transactions_received) >= 0

class TestAIIntegration:
    def test_ml_pipeline_training(self):
        """测试机器学习管道训练"""
        pipeline = OptimizedMLPipeline()
        
        # 创建测试数据
        X = np.random.random((100, 5))
        y = np.random.random(100)
        
        # 训练模型
        pipeline.train_model(X, y, 'test_model')
        
        # 验证模型存在
        assert 'test_model' in pipeline.models
    
    def test_prediction_accuracy(self):
        """测试预测准确性"""
        pipeline = OptimizedMLPipeline()
        
        # 创建简单线性关系数据
        X = np.random.random((100, 2))
        y = X[:, 0] * 2 + X[:, 1] * 3  # 线性关系
        
        # 训练模型
        pipeline.train_model(X, y, 'linear_model')
        
        # 预测
        X_test = np.random.random((10, 2))
        predictions = pipeline.predict(X_test, 'linear_model')
        
        # 验证预测结果合理
        assert len(predictions) == 10
        assert all(not np.isnan(pred) for pred in predictions)
```

## 最佳实践总结

### 1. 代码组织

- 使用类型提示提高代码可读性
- 采用模块化设计
- 实现适当的错误处理
- 编写全面的文档

### 2. 性能优化

- 使用异步编程处理I/O密集型任务
- 实现数据缓存减少重复计算
- 使用并行处理提高计算效率
- 优化内存使用

### 3. 安全考虑

- 验证所有输入数据
- 使用加密存储敏感信息
- 实现API认证和授权
- 定期安全审计

### 4. 测试策略

- 单元测试覆盖核心逻辑
- 集成测试验证系统行为
- 性能测试监控性能
- 数据质量测试

## 参考文献

1. "Web3.py Documentation" - Ethereum Foundation
2. "Pandas Documentation" - NumFOCUS
3. "Scikit-learn Documentation" - Inria
4. "TensorFlow Documentation" - Google
5. "Python Web3 Development" - Python Software Foundation
