# 元宇宙与虚拟经济理论分析

## 1. 元宇宙基础理论

### 1.1 基本定义

**定义 1.1 (元宇宙)** 由虚拟现实、增强现实和互联网技术构建的持久性虚拟世界。

**定义 1.2 (虚拟经济)** 在虚拟世界中运行的经济系统，包括虚拟货币、资产和服务。

**定义 1.3 (数字身份)** 用户在元宇宙中的虚拟身份和属性。

### 1.2 元宇宙架构

**定义 1.4 (虚拟空间)** 元宇宙中的三维环境，支持用户交互和活动。

**定义 1.5 (虚拟资产)** 在元宇宙中具有价值的数字物品和财产。

**定义 1.6 (虚拟服务)** 在元宇宙中提供的各种服务和功能。

## 2. 虚拟经济系统

### 2.1 虚拟货币系统

```python
import time
import hashlib
from typing import Dict, List, Optional, Any
from dataclasses import dataclass

@dataclass
class VirtualCurrency:
    name: str
    symbol: str
    total_supply: float
    inflation_rate: float

class VirtualEconomy:
    def __init__(self):
        self.currencies = {}
        self.users = {}
        self.transactions = {}
        self.markets = {}
    
    def create_virtual_currency(self, currency_id: str, name: str, symbol: str,
                              initial_supply: float, inflation_rate: float = 0.02) -> Dict:
        """创建虚拟货币"""
        currency = {
            "id": currency_id,
            "name": name,
            "symbol": symbol,
            "total_supply": initial_supply,
            "circulating_supply": initial_supply,
            "inflation_rate": inflation_rate,
            "created_at": time.time(),
            "holders": {},
            "transactions": []
        }
        
        self.currencies[currency_id] = currency
        return currency
    
    def mint_currency(self, currency_id: str, to_address: str, amount: float) -> bool:
        """铸造虚拟货币"""
        if currency_id not in self.currencies:
            return False
        
        currency = self.currencies[currency_id]
        
        # 更新供应量
        currency["total_supply"] += amount
        currency["circulating_supply"] += amount
        
        # 更新持有者
        if to_address not in currency["holders"]:
            currency["holders"][to_address] = 0
        currency["holders"][to_address] += amount
        
        return True
    
    def transfer_currency(self, currency_id: str, from_address: str,
                         to_address: str, amount: float) -> bool:
        """转移虚拟货币"""
        if currency_id not in self.currencies:
            return False
        
        currency = self.currencies[currency_id]
        
        # 检查余额
        if currency["holders"].get(from_address, 0) < amount:
            return False
        
        # 执行转移
        currency["holders"][from_address] -= amount
        if to_address not in currency["holders"]:
            currency["holders"][to_address] = 0
        currency["holders"][to_address] += amount
        
        # 记录交易
        transaction = {
            "from": from_address,
            "to": to_address,
            "amount": amount,
            "timestamp": time.time()
        }
        currency["transactions"].append(transaction)
        
        return True
    
    def apply_inflation(self, currency_id: str) -> float:
        """应用通胀"""
        if currency_id not in self.currencies:
            return 0
        
        currency = self.currencies[currency_id]
        inflation_amount = currency["circulating_supply"] * currency["inflation_rate"]
        
        currency["total_supply"] += inflation_amount
        currency["circulating_supply"] += inflation_amount
        
        return inflation_amount
    
    def get_currency_stats(self, currency_id: str) -> Dict:
        """获取货币统计"""
        if currency_id not in self.currencies:
            return {}
        
        currency = self.currencies[currency_id]
        
        return {
            "id": currency_id,
            "name": currency["name"],
            "symbol": currency["symbol"],
            "total_supply": currency["total_supply"],
            "circulating_supply": currency["circulating_supply"],
            "inflation_rate": currency["inflation_rate"],
            "holder_count": len(currency["holders"]),
            "transaction_count": len(currency["transactions"])
        }
```

### 2.2 虚拟资产市场

```python
class VirtualAssetMarket:
    def __init__(self):
        self.assets = {}
        self.markets = {}
        self.orders = {}
        self.trades = {}
    
    def create_virtual_asset(self, asset_id: str, name: str, asset_type: str,
                            owner: str, metadata: Dict) -> Dict:
        """创建虚拟资产"""
        asset = {
            "id": asset_id,
            "name": name,
            "type": asset_type,
            "owner": owner,
            "metadata": metadata,
            "created_at": time.time(),
            "trade_history": [],
            "current_price": 0
        }
        
        self.assets[asset_id] = asset
        return asset
    
    def create_market(self, market_id: str, asset_type: str, base_currency: str) -> Dict:
        """创建市场"""
        market = {
            "id": market_id,
            "asset_type": asset_type,
            "base_currency": base_currency,
            "orders": [],
            "trades": [],
            "created_at": time.time()
        }
        
        self.markets[market_id] = market
        return market
    
    def place_order(self, market_id: str, user_address: str, asset_id: str,
                   order_type: str, price: float, quantity: int) -> Dict:
        """下单"""
        if market_id not in self.markets:
            return {"success": False, "error": "Market not found"}
        
        if asset_id not in self.assets:
            return {"success": False, "error": "Asset not found"}
        
        order = {
            "id": f"order_{time.time()}_{user_address}",
            "market_id": market_id,
            "user": user_address,
            "asset_id": asset_id,
            "type": order_type,  # "buy" or "sell"
            "price": price,
            "quantity": quantity,
            "filled_quantity": 0,
            "status": "open",
            "created_at": time.time()
        }
        
        self.orders[order["id"]] = order
        
        # 尝试匹配订单
        self.match_orders(market_id)
        
        return {"success": True, "order_id": order["id"]}
    
    def match_orders(self, market_id: str):
        """匹配订单"""
        if market_id not in self.markets:
            return
        
        market = self.markets[market_id]
        open_orders = [order for order in self.orders.values() 
                      if order["market_id"] == market_id and order["status"] == "open"]
        
        # 分离买单和卖单
        buy_orders = [order for order in open_orders if order["type"] == "buy"]
        sell_orders = [order for order in open_orders if order["type"] == "sell"]
        
        # 按价格排序
        buy_orders.sort(key=lambda x: x["price"], reverse=True)
        sell_orders.sort(key=lambda x: x["price"])
        
        # 匹配订单
        for buy_order in buy_orders:
            for sell_order in sell_orders:
                if buy_order["price"] >= sell_order["price"]:
                    # 执行交易
                    trade_quantity = min(buy_order["quantity"] - buy_order["filled_quantity"],
                                       sell_order["quantity"] - sell_order["filled_quantity"])
                    
                    if trade_quantity > 0:
                        self.execute_trade(buy_order, sell_order, trade_quantity)
    
    def execute_trade(self, buy_order: Dict, sell_order: Dict, quantity: int):
        """执行交易"""
        trade_price = (buy_order["price"] + sell_order["price"]) / 2
        
        trade = {
            "id": f"trade_{time.time()}",
            "buy_order_id": buy_order["id"],
            "sell_order_id": sell_order["id"],
            "asset_id": buy_order["asset_id"],
            "price": trade_price,
            "quantity": quantity,
            "timestamp": time.time()
        }
        
        self.trades[trade["id"]] = trade
        
        # 更新订单
        buy_order["filled_quantity"] += quantity
        sell_order["filled_quantity"] += quantity
        
        if buy_order["filled_quantity"] >= buy_order["quantity"]:
            buy_order["status"] = "filled"
        
        if sell_order["filled_quantity"] >= sell_order["quantity"]:
            sell_order["status"] = "filled"
        
        # 更新资产价格
        asset_id = buy_order["asset_id"]
        if asset_id in self.assets:
            self.assets[asset_id]["current_price"] = trade_price
    
    def get_market_data(self, market_id: str) -> Dict:
        """获取市场数据"""
        if market_id not in self.markets:
            return {}
        
        market = self.markets[market_id]
        market_orders = [order for order in self.orders.values() 
                        if order["market_id"] == market_id]
        
        # 计算市场统计
        total_volume = sum(trade["quantity"] * trade["price"] 
                          for trade in self.trades.values()
                          if trade["asset_id"] in [order["asset_id"] for order in market_orders])
        
        open_orders = len([order for order in market_orders if order["status"] == "open"])
        
        return {
            "market_id": market_id,
            "asset_type": market["asset_type"],
            "base_currency": market["base_currency"],
            "total_volume": total_volume,
            "open_orders": open_orders,
            "total_trades": len([trade for trade in self.trades.values()
                               if trade["asset_id"] in [order["asset_id"] for order in market_orders]])
        }
```

## 3. 虚拟空间管理

### 3.1 虚拟土地系统

```python
class VirtualLandSystem:
    def __init__(self):
        self.lands = {}
        self.parcels = {}
        self.buildings = {}
        self.zones = {}
    
    def create_virtual_world(self, world_id: str, name: str, size: tuple,
                           parcel_size: tuple) -> Dict:
        """创建虚拟世界"""
        world = {
            "id": world_id,
            "name": name,
            "size": size,
            "parcel_size": parcel_size,
            "parcels": {},
            "created_at": time.time()
        }
        
        # 创建地块
        x_size, y_size = size
        parcel_x, parcel_y = parcel_size
        
        for x in range(0, x_size, parcel_x):
            for y in range(0, y_size, parcel_y):
                parcel_id = f"parcel_{x}_{y}"
                world["parcels"][parcel_id] = {
                    "id": parcel_id,
                    "coordinates": (x, y),
                    "size": parcel_size,
                    "owner": None,
                    "buildings": [],
                    "price": 100  # 基础价格
                }
        
        self.lands[world_id] = world
        return world
    
    def purchase_land(self, world_id: str, parcel_id: str, buyer: str,
                     price: float) -> bool:
        """购买土地"""
        if world_id not in self.lands:
            return False
        
        world = self.lands[world_id]
        
        if parcel_id not in world["parcels"]:
            return False
        
        parcel = world["parcels"][parcel_id]
        
        if parcel["owner"] is not None:
            return False  # 已售出
        
        # 检查价格
        if price < parcel["price"]:
            return False
        
        # 购买土地
        parcel["owner"] = buyer
        parcel["purchase_price"] = price
        parcel["purchased_at"] = time.time()
        
        return True
    
    def build_on_land(self, world_id: str, parcel_id: str, building_type: str,
                     building_data: Dict) -> bool:
        """在土地上建造"""
        if world_id not in self.lands:
            return False
        
        world = self.lands[world_id]
        
        if parcel_id not in world["parcels"]:
            return False
        
        parcel = world["parcels"][parcel_id]
        
        if parcel["owner"] is None:
            return False  # 需要拥有土地
        
        # 创建建筑
        building_id = f"building_{time.time()}"
        building = {
            "id": building_id,
            "type": building_type,
            "data": building_data,
            "parcel_id": parcel_id,
            "created_at": time.time()
        }
        
        parcel["buildings"].append(building_id)
        self.buildings[building_id] = building
        
        return True
    
    def get_land_info(self, world_id: str, parcel_id: str) -> Dict:
        """获取土地信息"""
        if world_id not in self.lands:
            return {}
        
        world = self.lands[world_id]
        
        if parcel_id not in world["parcels"]:
            return {}
        
        parcel = world["parcels"][parcel_id]
        
        return {
            "parcel_id": parcel_id,
            "coordinates": parcel["coordinates"],
            "size": parcel["size"],
            "owner": parcel["owner"],
            "buildings": parcel["buildings"],
            "price": parcel["price"]
        }
    
    def calculate_land_value(self, world_id: str, parcel_id: str) -> float:
        """计算土地价值"""
        if world_id not in self.lands:
            return 0
        
        world = self.lands[world_id]
        
        if parcel_id not in world["parcels"]:
            return 0
        
        parcel = world["parcels"][parcel_id]
        base_price = parcel["price"]
        
        # 位置加成
        x, y = parcel["coordinates"]
        center_x, center_y = world["size"][0] // 2, world["size"][1] // 2
        distance_to_center = ((x - center_x) ** 2 + (y - center_y) ** 2) ** 0.5
        
        # 距离中心越近，价值越高
        location_bonus = max(0.5, 1 - distance_to_center / 1000)
        
        # 建筑加成
        building_bonus = len(parcel["buildings"]) * 0.1
        
        return base_price * location_bonus * (1 + building_bonus)
```

### 3.2 虚拟服务系统

```python
class VirtualServiceSystem:
    def __init__(self):
        self.services = {}
        self.providers = {}
        self.consumers = {}
        self.transactions = {}
    
    def register_service_provider(self, provider_id: str, provider_name: str,
                                service_types: List[str]) -> Dict:
        """注册服务提供者"""
        provider = {
            "id": provider_id,
            "name": provider_name,
            "service_types": service_types,
            "services": [],
            "rating": 0,
            "total_earnings": 0,
            "registered_at": time.time()
        }
        
        self.providers[provider_id] = provider
        return provider
    
    def create_service(self, service_id: str, provider_id: str, service_type: str,
                      name: str, description: str, price: float) -> Dict:
        """创建服务"""
        service = {
            "id": service_id,
            "provider_id": provider_id,
            "type": service_type,
            "name": name,
            "description": description,
            "price": price,
            "status": "active",
            "created_at": time.time(),
            "bookings": []
        }
        
        self.services[service_id] = service
        
        # 添加到提供者
        if provider_id in self.providers:
            self.providers[provider_id]["services"].append(service_id)
        
        return service
    
    def book_service(self, service_id: str, consumer_id: str, booking_data: Dict) -> Dict:
        """预订服务"""
        if service_id not in self.services:
            return {"success": False, "error": "Service not found"}
        
        service = self.services[service_id]
        
        if service["status"] != "active":
            return {"success": False, "error": "Service not available"}
        
        # 创建预订
        booking = {
            "id": f"booking_{time.time()}_{consumer_id}",
            "service_id": service_id,
            "consumer_id": consumer_id,
            "data": booking_data,
            "status": "confirmed",
            "created_at": time.time()
        }
        
        service["bookings"].append(booking)
        
        # 记录交易
        transaction = {
            "id": f"transaction_{time.time()}",
            "service_id": service_id,
            "provider_id": service["provider_id"],
            "consumer_id": consumer_id,
            "amount": service["price"],
            "timestamp": time.time()
        }
        
        self.transactions[transaction["id"]] = transaction
        
        # 更新提供者收益
        if service["provider_id"] in self.providers:
            self.providers[service["provider_id"]]["total_earnings"] += service["price"]
        
        return {"success": True, "booking_id": booking["id"]}
    
    def rate_service(self, booking_id: str, rating: float, review: str) -> bool:
        """评价服务"""
        # 查找预订
        booking = None
        service = None
        
        for s in self.services.values():
            for b in s["bookings"]:
                if b["id"] == booking_id:
                    booking = b
                    service = s
                    break
            if booking:
                break
        
        if not booking:
            return False
        
        # 更新评价
        booking["rating"] = rating
        booking["review"] = review
        booking["rated_at"] = time.time()
        
        # 更新提供者评分
        provider_id = service["provider_id"]
        if provider_id in self.providers:
            provider = self.providers[provider_id]
            
            # 计算平均评分
            all_ratings = []
            for s in self.services.values():
                if s["provider_id"] == provider_id:
                    for b in s["bookings"]:
                        if "rating" in b:
                            all_ratings.append(b["rating"])
            
            if all_ratings:
                provider["rating"] = sum(all_ratings) / len(all_ratings)
        
        return True
    
    def get_service_statistics(self, provider_id: str) -> Dict:
        """获取服务统计"""
        if provider_id not in self.providers:
            return {}
        
        provider = self.providers[provider_id]
        provider_services = [s for s in self.services.values() 
                           if s["provider_id"] == provider_id]
        
        total_bookings = sum(len(s["bookings"]) for s in provider_services)
        total_revenue = provider["total_earnings"]
        
        return {
            "provider_id": provider_id,
            "provider_name": provider["name"],
            "service_count": len(provider_services),
            "total_bookings": total_bookings,
            "total_revenue": total_revenue,
            "average_rating": provider["rating"]
        }
```

## 4. 数字身份管理

### 4.1 虚拟身份系统

```python
class VirtualIdentitySystem:
    def __init__(self):
        self.identities = {}
        self.avatars = {}
        self.reputations = {}
        self.relationships = {}
    
    def create_digital_identity(self, identity_id: str, username: str,
                              email: str, avatar_data: Dict) -> Dict:
        """创建数字身份"""
        identity = {
            "id": identity_id,
            "username": username,
            "email": email,
            "avatar_id": None,
            "reputation_score": 0,
            "created_at": time.time(),
            "last_active": time.time(),
            "achievements": [],
            "relationships": []
        }
        
        self.identities[identity_id] = identity
        
        # 创建头像
        avatar_id = self.create_avatar(identity_id, avatar_data)
        identity["avatar_id"] = avatar_id
        
        return identity
    
    def create_avatar(self, identity_id: str, avatar_data: Dict) -> str:
        """创建头像"""
        avatar_id = f"avatar_{identity_id}"
        
        avatar = {
            "id": avatar_id,
            "identity_id": identity_id,
            "appearance": avatar_data.get("appearance", {}),
            "customizations": avatar_data.get("customizations", []),
            "created_at": time.time()
        }
        
        self.avatars[avatar_id] = avatar
        return avatar_id
    
    def update_avatar(self, identity_id: str, new_appearance: Dict) -> bool:
        """更新头像"""
        if identity_id not in self.identities:
            return False
        
        identity = self.identities[identity_id]
        avatar_id = identity["avatar_id"]
        
        if avatar_id not in self.avatars:
            return False
        
        avatar = self.avatars[avatar_id]
        avatar["appearance"].update(new_appearance)
        avatar["updated_at"] = time.time()
        
        return True
    
    def update_reputation(self, identity_id: str, action_type: str, points: int) -> bool:
        """更新声誉"""
        if identity_id not in self.identities:
            return False
        
        identity = self.identities[identity_id]
        identity["reputation_score"] += points
        
        # 记录声誉变化
        reputation_record = {
            "action_type": action_type,
            "points": points,
            "timestamp": time.time()
        }
        
        if identity_id not in self.reputations:
            self.reputations[identity_id] = []
        
        self.reputations[identity_id].append(reputation_record)
        
        return True
    
    def add_achievement(self, identity_id: str, achievement_type: str,
                       achievement_data: Dict) -> bool:
        """添加成就"""
        if identity_id not in self.identities:
            return False
        
        identity = self.identities[identity_id]
        
        achievement = {
            "type": achievement_type,
            "data": achievement_data,
            "earned_at": time.time()
        }
        
        identity["achievements"].append(achievement)
        
        return True
    
    def create_relationship(self, identity_id_1: str, identity_id_2: str,
                          relationship_type: str) -> bool:
        """创建关系"""
        if identity_id_1 not in self.identities or identity_id_2 not in self.identities:
            return False
        
        relationship_id = f"rel_{identity_id_1}_{identity_id_2}"
        
        relationship = {
            "id": relationship_id,
            "identity_1": identity_id_1,
            "identity_2": identity_id_2,
            "type": relationship_type,
            "created_at": time.time(),
            "strength": 1.0
        }
        
        self.relationships[relationship_id] = relationship
        
        # 更新身份关系列表
        self.identities[identity_id_1]["relationships"].append(relationship_id)
        self.identities[identity_id_2]["relationships"].append(relationship_id)
        
        return True
    
    def get_identity_profile(self, identity_id: str) -> Dict:
        """获取身份档案"""
        if identity_id not in self.identities:
            return {}
        
        identity = self.identities[identity_id]
        avatar = self.avatars.get(identity["avatar_id"], {})
        
        return {
            "id": identity_id,
            "username": identity["username"],
            "reputation_score": identity["reputation_score"],
            "achievement_count": len(identity["achievements"]),
            "relationship_count": len(identity["relationships"]),
            "avatar": avatar.get("appearance", {}),
            "created_at": identity["created_at"],
            "last_active": identity["last_active"]
        }
```

## 5. 总结

元宇宙与虚拟经济为Web3生态系统提供了沉浸式体验：

1. **虚拟经济**：虚拟货币、资产市场、服务系统等
2. **虚拟空间**：土地系统、建筑系统、服务管理等
3. **数字身份**：虚拟身份、头像、声誉、关系等
4. **应用场景**：虚拟世界、游戏、社交、商业等
5. **Web3集成**：与区块链、NFT、DeFi深度集成

元宇宙与虚拟经济将继续在Web3生态系统中发挥核心作用，为用户提供全新的数字生活体验。
