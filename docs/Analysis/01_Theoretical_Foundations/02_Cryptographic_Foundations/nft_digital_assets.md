# NFT与数字资产理论分析

## 1. NFT基础理论

### 1.1 基本定义

**定义 1.1 (NFT)** 非同质化代币，每个代币具有唯一性和不可替代性。

**定义 1.2 (数字资产)** 以数字形式存在的具有价值的资产。

**定义 1.3 (元数据)** 描述NFT属性的结构化数据。

### 1.2 NFT类型

**定义 1.4 (ERC-721)** 以太坊NFT标准，每个代币具有唯一ID。

**定义 1.5 (ERC-1155)** 半同质化代币标准，支持批量操作。

**定义 1.6 (动态NFT)** 可以根据外部条件或时间变化的NFT。

## 2. NFT标准实现

### 2.1 ERC-721标准

```python
import time
import hashlib
from typing import Dict, List, Optional, Any
from dataclasses import dataclass

@dataclass
class NFTMetadata:
    name: str
    symbol: str
    description: str
    image: str
    attributes: List[Dict]

class ERC721Implementation:
    def __init__(self):
        self.tokens = {}
        self.owners = {}
        self.approvals = {}
        self.total_supply = 0
        self.metadata = {}
    
    def mint(self, to_address: str, token_id: int, metadata: NFTMetadata) -> bool:
        """铸造NFT"""
        if token_id in self.tokens:
            return False  # 代币已存在
        
        token = {
            "id": token_id,
            "owner": to_address,
            "metadata": metadata,
            "minted_at": time.time(),
            "transfers": []
        }
        
        self.tokens[token_id] = token
        
        # 更新所有者映射
        if to_address not in self.owners:
            self.owners[to_address] = []
        self.owners[to_address].append(token_id)
        
        self.total_supply += 1
        
        return True
    
    def transfer(self, from_address: str, to_address: str, token_id: int) -> bool:
        """转移NFT"""
        if token_id not in self.tokens:
            return False
        
        token = self.tokens[token_id]
        
        if token["owner"] != from_address:
            return False
        
        # 更新所有者
        token["owner"] = to_address
        
        # 更新所有者映射
        if from_address in self.owners:
            self.owners[from_address].remove(token_id)
        
        if to_address not in self.owners:
            self.owners[to_address] = []
        self.owners[to_address].append(token_id)
        
        # 记录转移
        transfer_record = {
            "from": from_address,
            "to": to_address,
            "timestamp": time.time()
        }
        token["transfers"].append(transfer_record)
        
        return True
    
    def approve(self, owner: str, spender: str, token_id: int) -> bool:
        """授权"""
        if token_id not in self.tokens:
            return False
        
        token = self.tokens[token_id]
        
        if token["owner"] != owner:
            return False
        
        approval_key = f"{token_id}_{spender}"
        self.approvals[approval_key] = {
            "spender": spender,
            "approved_at": time.time()
        }
        
        return True
    
    def transfer_from(self, spender: str, from_address: str, to_address: str, token_id: int) -> bool:
        """授权转移"""
        if token_id not in self.tokens:
            return False
        
        token = self.tokens[token_id]
        
        if token["owner"] != from_address:
            return False
        
        # 检查授权
        approval_key = f"{token_id}_{spender}"
        if approval_key not in self.approvals:
            return False
        
        # 执行转移
        success = self.transfer(from_address, to_address, token_id)
        
        if success:
            # 清除授权
            del self.approvals[approval_key]
        
        return success
    
    def get_owner(self, token_id: int) -> Optional[str]:
        """获取所有者"""
        if token_id not in self.tokens:
            return None
        
        return self.tokens[token_id]["owner"]
    
    def get_token_metadata(self, token_id: int) -> Optional[NFTMetadata]:
        """获取代币元数据"""
        if token_id not in self.tokens:
            return None
        
        return self.tokens[token_id]["metadata"]
    
    def get_tokens_by_owner(self, owner_address: str) -> List[int]:
        """获取所有者拥有的代币"""
        return self.owners.get(owner_address, [])
    
    def get_transfer_history(self, token_id: int) -> List[Dict]:
        """获取转移历史"""
        if token_id not in self.tokens:
            return []
        
        return self.tokens[token_id]["transfers"]
```

### 2.2 ERC-1155标准

```python
class ERC1155Implementation:
    def __init__(self):
        self.balances = {}
        self.operators = {}
        self.metadata = {}
    
    def mint(self, to_address: str, token_id: int, amount: int, metadata: Dict) -> bool:
        """铸造代币"""
        balance_key = f"{to_address}_{token_id}"
        
        if balance_key not in self.balances:
            self.balances[balance_key] = 0
        
        self.balances[balance_key] += amount
        
        # 存储元数据
        if token_id not in self.metadata:
            self.metadata[token_id] = metadata
        
        return True
    
    def mint_batch(self, to_address: str, token_ids: List[int], amounts: List[int], metadata_list: List[Dict]) -> bool:
        """批量铸造"""
        if len(token_ids) != len(amounts) or len(token_ids) != len(metadata_list):
            return False
        
        for token_id, amount, metadata in zip(token_ids, amounts, metadata_list):
            success = self.mint(to_address, token_id, amount, metadata)
            if not success:
                return False
        
        return True
    
    def transfer(self, from_address: str, to_address: str, token_id: int, amount: int) -> bool:
        """转移代币"""
        from_balance_key = f"{from_address}_{token_id}"
        to_balance_key = f"{to_address}_{token_id}"
        
        if from_balance_key not in self.balances:
            return False
        
        if self.balances[from_balance_key] < amount:
            return False
        
        # 更新余额
        self.balances[from_balance_key] -= amount
        
        if to_balance_key not in self.balances:
            self.balances[to_balance_key] = 0
        self.balances[to_balance_key] += amount
        
        return True
    
    def transfer_batch(self, from_address: str, to_address: str, token_ids: List[int], amounts: List[int]) -> bool:
        """批量转移"""
        if len(token_ids) != len(amounts):
            return False
        
        # 检查所有余额
        for token_id, amount in zip(token_ids, amounts):
            balance_key = f"{from_address}_{token_id}"
            if balance_key not in self.balances or self.balances[balance_key] < amount:
                return False
        
        # 执行转移
        for token_id, amount in zip(token_ids, amounts):
            success = self.transfer(from_address, to_address, token_id, amount)
            if not success:
                return False
        
        return True
    
    def get_balance(self, address: str, token_id: int) -> int:
        """获取余额"""
        balance_key = f"{address}_{token_id}"
        return self.balances.get(balance_key, 0)
    
    def get_balances(self, address: str) -> Dict[int, int]:
        """获取所有代币余额"""
        balances = {}
        for key, amount in self.balances.items():
            if key.startswith(f"{address}_"):
                token_id = int(key.split("_")[1])
                balances[token_id] = amount
        
        return balances
```

## 3. 动态NFT

### 3.1 可升级NFT

```python
class DynamicNFT:
    def __init__(self):
        self.tokens = {}
        self.upgrade_rules = {}
        self.external_data = {}
    
    def create_dynamic_nft(self, token_id: int, base_metadata: Dict, upgrade_rules: Dict) -> bool:
        """创建动态NFT"""
        token = {
            "id": token_id,
            "base_metadata": base_metadata,
            "current_metadata": base_metadata.copy(),
            "upgrade_rules": upgrade_rules,
            "upgrade_history": [],
            "created_at": time.time()
        }
        
        self.tokens[token_id] = token
        return True
    
    def upgrade_nft(self, token_id: int, upgrade_type: str, upgrade_data: Dict) -> bool:
        """升级NFT"""
        if token_id not in self.tokens:
            return False
        
        token = self.tokens[token_id]
        rules = token["upgrade_rules"]
        
        # 检查升级规则
        if upgrade_type not in rules:
            return False
        
        rule = rules[upgrade_type]
        
        # 验证升级条件
        if not self.verify_upgrade_conditions(token, rule, upgrade_data):
            return False
        
        # 应用升级
        self.apply_upgrade(token, upgrade_type, upgrade_data)
        
        # 记录升级历史
        upgrade_record = {
            "type": upgrade_type,
            "data": upgrade_data,
            "timestamp": time.time()
        }
        token["upgrade_history"].append(upgrade_record)
        
        return True
    
    def verify_upgrade_conditions(self, token: Dict, rule: Dict, upgrade_data: Dict) -> bool:
        """验证升级条件"""
        # 检查等级要求
        if "level_requirement" in rule:
            current_level = token["current_metadata"].get("level", 0)
            if current_level < rule["level_requirement"]:
                return False
        
        # 检查资源要求
        if "resource_requirement" in rule:
            for resource, amount in rule["resource_requirement"].items():
                current_amount = token["current_metadata"].get(resource, 0)
                if current_amount < amount:
                    return False
        
        return True
    
    def apply_upgrade(self, token: Dict, upgrade_type: str, upgrade_data: Dict):
        """应用升级"""
        current_metadata = token["current_metadata"]
        
        # 更新属性
        for attribute, value in upgrade_data.items():
            if attribute in current_metadata:
                if isinstance(value, (int, float)):
                    current_metadata[attribute] += value
                else:
                    current_metadata[attribute] = value
            else:
                current_metadata[attribute] = value
    
    def get_external_data(self, token_id: int, data_source: str) -> Dict:
        """获取外部数据"""
        key = f"{token_id}_{data_source}"
        return self.external_data.get(key, {})
    
    def update_external_data(self, token_id: int, data_source: str, data: Dict):
        """更新外部数据"""
        key = f"{token_id}_{data_source}"
        self.external_data[key] = data
    
    def calculate_dynamic_attributes(self, token_id: int) -> Dict:
        """计算动态属性"""
        if token_id not in self.tokens:
            return {}
        
        token = self.tokens[token_id]
        base_metadata = token["base_metadata"]
        current_metadata = token["current_metadata"]
        
        # 基于时间和外部数据的动态计算
        age = time.time() - token["created_at"]
        
        dynamic_attributes = {
            "age": age,
            "experience": current_metadata.get("experience", 0) + age // 3600,  # 每小时增加经验
            "rarity_score": self.calculate_rarity_score(token),
            "market_value": self.calculate_market_value(token)
        }
        
        return dynamic_attributes
    
    def calculate_rarity_score(self, token: Dict) -> float:
        """计算稀有度分数"""
        metadata = token["current_metadata"]
        attributes = metadata.get("attributes", [])
        
        if not attributes:
            return 0.0
        
        # 计算稀有度
        rarity_scores = []
        for attr in attributes:
            trait_type = attr.get("trait_type", "")
            value = attr.get("value", "")
            
            # 简化的稀有度计算
            rarity = self.get_trait_rarity(trait_type, value)
            rarity_scores.append(rarity)
        
        return sum(rarity_scores) / len(rarity_scores) if rarity_scores else 0.0
    
    def get_trait_rarity(self, trait_type: str, value: str) -> float:
        """获取特征稀有度"""
        # 简化的稀有度计算
        # 实际应用中需要基于整个集合的统计数据
        
        rarity_map = {
            "background": {"common": 0.3, "rare": 0.7, "legendary": 0.95},
            "accessory": {"none": 0.5, "hat": 0.7, "glasses": 0.8},
            "expression": {"happy": 0.4, "sad": 0.6, "angry": 0.8}
        }
        
        trait_rarities = rarity_map.get(trait_type, {})
        return trait_rarities.get(value, 0.5)
    
    def calculate_market_value(self, token: Dict) -> float:
        """计算市场价值"""
        rarity_score = self.calculate_rarity_score(token)
        age = time.time() - token["created_at"]
        
        # 简化的价值计算
        base_value = 100
        rarity_multiplier = 1 + rarity_score
        age_bonus = min(age / (365 * 24 * 3600), 1.0)  # 最多1年加成
        
        return base_value * rarity_multiplier * (1 + age_bonus)
```

### 3.2 游戏化NFT

```python
class GamifiedNFT:
    def __init__(self):
        self.nfts = {}
        self.games = {}
        self.achievements = {}
    
    def create_game_nft(self, token_id: int, game_type: str, initial_stats: Dict) -> bool:
        """创建游戏NFT"""
        nft = {
            "id": token_id,
            "game_type": game_type,
            "stats": initial_stats.copy(),
            "level": 1,
            "experience": 0,
            "achievements": [],
            "created_at": time.time(),
            "last_played": time.time()
        }
        
        self.nfts[token_id] = nft
        return True
    
    def play_game(self, token_id: int, game_action: str, action_data: Dict) -> Dict:
        """玩游戏"""
        if token_id not in self.nfts:
            return {"success": False, "error": "NFT not found"}
        
        nft = self.nfts[token_id]
        
        # 执行游戏动作
        result = self.execute_game_action(nft, game_action, action_data)
        
        if result["success"]:
            # 更新NFT状态
            self.update_nft_stats(nft, result["rewards"])
            nft["last_played"] = time.time()
            
            # 检查升级
            self.check_level_up(nft)
            
            # 检查成就
            self.check_achievements(nft)
        
        return result
    
    def execute_game_action(self, nft: Dict, action: str, data: Dict) -> Dict:
        """执行游戏动作"""
        game_type = nft["game_type"]
        
        if game_type == "rpg":
            return self.execute_rpg_action(nft, action, data)
        elif game_type == "strategy":
            return self.execute_strategy_action(nft, action, data)
        else:
            return {"success": False, "error": "Unknown game type"}
    
    def execute_rpg_action(self, nft: Dict, action: str, data: Dict) -> Dict:
        """执行RPG动作"""
        stats = nft["stats"]
        
        if action == "battle":
            enemy_level = data.get("enemy_level", 1)
            player_level = nft["level"]
            
            # 简化的战斗计算
            win_probability = min(0.9, player_level / (player_level + enemy_level))
            
            import random
            if random.random() < win_probability:
                exp_gain = enemy_level * 10
                return {
                    "success": True,
                    "result": "victory",
                    "rewards": {"experience": exp_gain, "gold": enemy_level * 5}
                }
            else:
                return {
                    "success": True,
                    "result": "defeat",
                    "rewards": {"experience": 1}
                }
        
        elif action == "craft":
            materials = data.get("materials", {})
            recipe = data.get("recipe", {})
            
            # 检查材料
            for material, required in recipe.items():
                if stats.get(material, 0) < required:
                    return {"success": False, "error": "Insufficient materials"}
            
            # 消耗材料
            for material, amount in recipe.items():
                stats[material] -= amount
            
            # 获得物品
            crafted_item = data.get("crafted_item", "unknown")
            if "inventory" not in stats:
                stats["inventory"] = []
            stats["inventory"].append(crafted_item)
            
            return {
                "success": True,
                "result": "crafted",
                "rewards": {"item": crafted_item}
            }
        
        return {"success": False, "error": "Unknown action"}
    
    def execute_strategy_action(self, nft: Dict, action: str, data: Dict) -> Dict:
        """执行策略游戏动作"""
        stats = nft["stats"]
        
        if action == "build":
            building_type = data.get("building_type", "")
            cost = data.get("cost", 0)
            
            if stats.get("resources", 0) < cost:
                return {"success": False, "error": "Insufficient resources"}
            
            stats["resources"] -= cost
            
            if "buildings" not in stats:
                stats["buildings"] = []
            stats["buildings"].append(building_type)
            
            return {
                "success": True,
                "result": "built",
                "rewards": {"building": building_type}
            }
        
        return {"success": False, "error": "Unknown action"}
    
    def update_nft_stats(self, nft: Dict, rewards: Dict):
        """更新NFT统计"""
        stats = nft["stats"]
        
        for reward_type, amount in rewards.items():
            if reward_type == "experience":
                nft["experience"] += amount
            elif reward_type in stats:
                stats[reward_type] += amount
            else:
                stats[reward_type] = amount
    
    def check_level_up(self, nft: Dict):
        """检查升级"""
        current_exp = nft["experience"]
        current_level = nft["level"]
        
        # 计算升级所需经验
        exp_needed = current_level * 100
        
        if current_exp >= exp_needed:
            nft["level"] += 1
            nft["experience"] -= exp_needed
            
            # 升级奖励
            stats = nft["stats"]
            if "health" in stats:
                stats["health"] += 10
            if "attack" in stats:
                stats["attack"] += 5
    
    def check_achievements(self, nft: Dict):
        """检查成就"""
        stats = nft["stats"]
        level = nft["level"]
        achievements = nft["achievements"]
        
        # 等级成就
        if level >= 10 and "level_10" not in achievements:
            achievements.append("level_10")
        
        if level >= 50 and "level_50" not in achievements:
            achievements.append("level_50")
        
        # 战斗成就
        battles_won = stats.get("battles_won", 0)
        if battles_won >= 100 and "battle_master" not in achievements:
            achievements.append("battle_master")
        
        # 收集成就
        inventory = stats.get("inventory", [])
        unique_items = len(set(inventory))
        if unique_items >= 20 and "collector" not in achievements:
            achievements.append("collector")
```

## 4. NFT市场分析

### 4.1 市场指标

```python
class NFTMarketAnalytics:
    def __init__(self):
        self.collections = {}
        self.sales = {}
        self.trends = {}
    
    def analyze_collection(self, collection_address: str, nft_data: List[Dict]) -> Dict:
        """分析NFT集合"""
        if not nft_data:
            return {}
        
        # 基本统计
        total_supply = len(nft_data)
        floor_price = min(nft["price"] for nft in nft_data if nft["price"] > 0)
        total_volume = sum(nft["volume"] for nft in nft_data)
        
        # 价格分布
        prices = [nft["price"] for nft in nft_data if nft["price"] > 0]
        price_stats = self.calculate_price_statistics(prices)
        
        # 稀有度分析
        rarity_analysis = self.analyze_rarity(nft_data)
        
        # 交易活动
        trading_activity = self.analyze_trading_activity(nft_data)
        
        analysis = {
            "collection_address": collection_address,
            "total_supply": total_supply,
            "floor_price": floor_price,
            "total_volume": total_volume,
            "price_statistics": price_stats,
            "rarity_analysis": rarity_analysis,
            "trading_activity": trading_activity
        }
        
        return analysis
    
    def calculate_price_statistics(self, prices: List[float]) -> Dict:
        """计算价格统计"""
        if not prices:
            return {}
        
        return {
            "mean": sum(prices) / len(prices),
            "median": sorted(prices)[len(prices)//2],
            "min": min(prices),
            "max": max(prices),
            "std": self.calculate_std(prices)
        }
    
    def calculate_std(self, values: List[float]) -> float:
        """计算标准差"""
        if not values:
            return 0
        
        mean = sum(values) / len(values)
        variance = sum((x - mean) ** 2 for x in values) / len(values)
        return variance ** 0.5
    
    def analyze_rarity(self, nft_data: List[Dict]) -> Dict:
        """分析稀有度"""
        trait_frequencies = {}
        
        for nft in nft_data:
            traits = nft.get("traits", [])
            for trait in traits:
                trait_type = trait.get("trait_type", "")
                value = trait.get("value", "")
                
                if trait_type not in trait_frequencies:
                    trait_frequencies[trait_type] = {}
                
                if value not in trait_frequencies[trait_type]:
                    trait_frequencies[trait_type][value] = 0
                
                trait_frequencies[trait_type][value] += 1
        
        # 计算稀有度分数
        rarity_scores = {}
        total_nfts = len(nft_data)
        
        for nft in nft_data:
            traits = nft.get("traits", [])
            rarity_score = 0
            
            for trait in traits:
                trait_type = trait.get("trait_type", "")
                value = trait.get("value", "")
                
                if trait_type in trait_frequencies and value in trait_frequencies[trait_type]:
                    frequency = trait_frequencies[trait_type][value] / total_nfts
                    rarity_score += 1 / frequency
            
            rarity_scores[nft["token_id"]] = rarity_score
        
        return {
            "trait_frequencies": trait_frequencies,
            "rarity_scores": rarity_scores
        }
    
    def analyze_trading_activity(self, nft_data: List[Dict]) -> Dict:
        """分析交易活动"""
        # 计算交易频率
        trading_frequency = len([nft for nft in nft_data if nft.get("last_sold")])
        
        # 计算平均持有时间
        hold_times = []
        for nft in nft_data:
            if nft.get("minted_at") and nft.get("last_sold"):
                hold_time = nft["last_sold"] - nft["minted_at"]
                hold_times.append(hold_time)
        
        avg_hold_time = sum(hold_times) / len(hold_times) if hold_times else 0
        
        return {
            "trading_frequency": trading_frequency,
            "average_hold_time": avg_hold_time,
            "total_trades": len(hold_times)
        }
```

## 5. 总结

NFT与数字资产为Web3生态系统提供了独特的价值表示：

1. **NFT标准**：ERC-721、ERC-1155等标准化实现
2. **动态NFT**：可升级、游戏化、外部数据集成等
3. **市场分析**：价格统计、稀有度分析、交易活动等
4. **应用场景**：数字艺术、游戏、收藏品、身份认证等
5. **Web3集成**：与DeFi、治理、跨链等深度集成

NFT与数字资产将继续在Web3生态系统中发挥核心作用，为用户提供独特的数字所有权体验。
