# 电商行业架构最佳实践

## 目录

- [电商行业架构最佳实践](#电商行业架构最佳实践)
  - [目录](#目录)
  - [1. 行业概述与核心挑战](#1-行业概述与核心挑战)
    - [1.1 行业特点](#11-行业特点)
    - [1.2 核心挑战](#12-核心挑战)
  - [2. 技术栈选型与架构模式](#2-技术栈选型与架构模式)
    - [2.1 核心技术栈](#21-核心技术栈)
  - [3. 微服务电商架构](#3-微服务电商架构)
    - [3.1 架构层次](#31-架构层次)
    - [3.2 微服务实现](#32-微服务实现)
  - [4. 事件驱动电商架构](#4-事件驱动电商架构)
    - [4.1 事件定义](#41-事件定义)
    - [4.2 事件处理器](#42-事件处理器)
  - [5. 用户与产品管理](#5-用户与产品管理)
    - [5.1 用户管理](#51-用户管理)
    - [5.2 产品管理](#52-产品管理)
  - [6. 订单与支付系统](#6-订单与支付系统)
    - [6.1 订单管理](#61-订单管理)
    - [6.2 支付系统](#62-支付系统)
  - [7. 推荐与库存管理](#7-推荐与库存管理)
    - [7.1 推荐系统](#71-推荐系统)
    - [7.2 库存管理](#72-库存管理)
  - [总结](#总结)

---

## 1. 行业概述与核心挑战

### 1.1 行业特点

电子商务领域需要处理高并发交易、实时库存管理、个性化推荐、支付处理等复杂业务场景。

### 1.2 核心挑战

- **高并发**: 秒杀、促销活动的高并发处理
- **实时性**: 库存实时更新、价格实时同步
- **一致性**: 订单状态、库存数据的一致性
- **个性化**: 用户行为分析、智能推荐
- **安全性**: 支付安全、用户数据保护

---

## 2. 技术栈选型与架构模式

### 2.1 核心技术栈

```toml
[dependencies]
# Web框架
actix-web = "4.4"
axum = "0.7"
rocket = "0.5"
warp = "0.3"

# 数据库
diesel = { version = "2.1", features = ["postgres"] }
sqlx = { version = "0.7", features = ["postgres", "runtime-tokio-rustls"] }
seaorm = { version = "0.12", features = ["sqlx-postgres", "runtime-tokio-rustls"] }
redis = { version = "0.24", features = ["tokio-comp"] }

# 搜索引擎
elasticsearch = "8.0"
meilisearch = "0.1"

# 消息队列
lapin = "2.3"
kafka = "0.1"
redis-streams = "0.1"

# 支付处理
stripe = "0.1"
paypal = "0.1"
alipay = "0.1"

# 加密和安全
ring = "0.17"
rustls = "0.21"
aes-gcm = "0.10"

# 推荐和AI
tch-rs = "0.13"
burn = "0.1"
candle = "0.1"
polars = "0.35"
ndarray = "0.15"
statrs = "0.16"
```

---

## 3. 微服务电商架构

### 3.1 架构层次

```text
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   API Gateway   │    │  Authentication │    │   User Service  │
│   (Axum)        │    │   Service       │    │                 │
└─────────────────┘    └─────────────────┘    └─────────────────┘
         │                       │                       │
         └───────────────────────┼───────────────────────┘
                                 │
         ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
         │ Product Service │    │  Order Service  │    │ Payment Service │
         │                 │    │                 │    │                 │
         └─────────────────┘    └─────────────────┘    └─────────────────┘
```

### 3.2 微服务实现

```rust
use actix_web::{web, App, HttpServer, middleware};
use serde::{Deserialize, Serialize};

#[derive(Clone)]
pub struct ECommerceMicroservices {
    user_service: UserService,
    product_service: ProductService,
    order_service: OrderService,
    payment_service: PaymentService,
    inventory_service: InventoryService,
    recommendation_service: RecommendationService,
    notification_service: NotificationService,
}

impl ECommerceMicroservices {
    pub async fn start_services(&self) -> Result<(), ServiceError> {
        // 启动用户服务
        let user_server = HttpServer::new(|| {
            App::new()
                .wrap(middleware::Logger::default())
                .wrap(middleware::Cors::default())
                .service(user_routes())
        })
        .bind("127.0.0.1:8081")?
        .run();

        // 启动产品服务
        let product_server = HttpServer::new(|| {
            App::new()
                .wrap(middleware::Logger::default())
                .wrap(middleware::Cors::default())
                .service(product_routes())
        })
        .bind("127.0.0.1:8082")?
        .run();

        // 启动订单服务
        let order_server = HttpServer::new(|| {
            App::new()
                .wrap(middleware::Logger::default())
                .wrap(middleware::Cors::default())
                .service(order_routes())
        })
        .bind("127.0.0.1:8083")?
        .run();

        // 启动支付服务
        let payment_server = HttpServer::new(|| {
            App::new()
                .wrap(middleware::Logger::default())
                .wrap(middleware::Cors::default())
                .service(payment_routes())
        })
        .bind("127.0.0.1:8084")?
        .run();

        // 并行运行所有服务
        tokio::try_join!(user_server, product_server, order_server, payment_server)?;
        Ok(())
    }
}

// 用户服务
pub struct UserService {
    user_repository: Arc<UserRepository>,
    auth_service: Arc<AuthService>,
    cache: Arc<RedisCache>,
}

impl UserService {
    pub async fn register_user(&self, registration: UserRegistration) -> Result<User, ServiceError> {
        // 1. 验证用户数据
        self.validate_registration(&registration).await?;
        
        // 2. 检查邮箱是否已存在
        if self.user_repository.email_exists(&registration.email).await? {
            return Err(ServiceError::EmailAlreadyExists);
        }
        
        // 3. 创建用户
        let user = User::new(registration);
        
        // 4. 保存用户
        let saved_user = self.user_repository.save(&user).await?;
        
        // 5. 缓存用户信息
        self.cache.set_user(&saved_user).await?;
        
        Ok(saved_user)
    }
    
    pub async fn authenticate_user(&self, credentials: LoginCredentials) -> Result<AuthToken, ServiceError> {
        // 1. 验证凭据
        let user = self.user_repository.find_by_email(&credentials.email).await?;
        
        if !self.auth_service.verify_password(&credentials.password, &user.password_hash) {
            return Err(ServiceError::InvalidCredentials);
        }
        
        // 2. 生成认证令牌
        let token = self.auth_service.generate_token(&user).await?;
        
        // 3. 记录登录事件
        self.record_login_event(&user).await?;
        
        Ok(token)
    }
    
    async fn validate_registration(&self, registration: &UserRegistration) -> Result<(), ServiceError> {
        // 验证邮箱格式
        if !self.is_valid_email(&registration.email) {
            return Err(ServiceError::InvalidEmail);
        }
        
        // 验证密码强度
        if !self.is_strong_password(&registration.password) {
            return Err(ServiceError::WeakPassword);
        }
        
        // 验证用户名
        if registration.username.len() < 3 || registration.username.len() > 20 {
            return Err(ServiceError::InvalidUsername);
        }
        
        Ok(())
    }
}

// 产品服务
pub struct ProductService {
    product_repository: Arc<ProductRepository>,
    search_engine: Arc<SearchEngine>,
    cache: Arc<RedisCache>,
}

impl ProductService {
    pub async fn create_product(&self, product_data: CreateProductRequest) -> Result<Product, ServiceError> {
        // 1. 验证产品数据
        self.validate_product_data(&product_data).await?;
        
        // 2. 生成SKU
        let sku = self.generate_sku(&product_data).await?;
        
        // 3. 创建产品
        let product = Product::new(product_data, sku);
        
        // 4. 保存产品
        let saved_product = self.product_repository.save(&product).await?;
        
        // 5. 索引到搜索引擎
        self.search_engine.index_product(&saved_product).await?;
        
        // 6. 缓存产品信息
        self.cache.set_product(&saved_product).await?;
        
        Ok(saved_product)
    }
    
    pub async fn search_products(&self, query: SearchQuery) -> Result<SearchResult, ServiceError> {
        // 1. 检查缓存
        if let Some(cached_result) = self.cache.get_search_result(&query).await? {
            return Ok(cached_result);
        }
        
        // 2. 执行搜索
        let search_result = self.search_engine.search(&query).await?;
        
        // 3. 缓存结果
        self.cache.set_search_result(&query, &search_result).await?;
        
        Ok(search_result)
    }
    
    pub async fn update_product_price(&self, product_id: &str, new_price: Money) -> Result<(), ServiceError> {
        // 1. 更新产品价格
        self.product_repository.update_price(product_id, new_price).await?;
        
        // 2. 更新搜索引擎索引
        self.search_engine.update_product_price(product_id, new_price).await?;
        
        // 3. 清除缓存
        self.cache.invalidate_product(product_id).await?;
        
        // 4. 发布价格变更事件
        self.publish_price_change_event(product_id, new_price).await?;
        
        Ok(())
    }
}
```

---

## 4. 事件驱动电商架构

### 4.1 事件定义

```rust
use tokio::sync::broadcast;
use serde::{Deserialize, Serialize};

#[derive(Clone, Serialize, Deserialize)]
pub struct ECommerceEvent {
    pub id: String,
    pub event_type: ECommerceEventType,
    pub user_id: Option<String>,
    pub data: serde_json::Value,
    pub timestamp: DateTime<Utc>,
    pub correlation_id: String,
}

#[derive(Clone, Serialize, Deserialize)]
pub enum ECommerceEventType {
    UserRegistered,
    UserLoggedIn,
    ProductViewed,
    ProductAddedToCart,
    ProductRemovedFromCart,
    OrderCreated,
    OrderPaid,
    OrderShipped,
    OrderDelivered,
    PaymentProcessed,
    PaymentFailed,
    InventoryUpdated,
    PriceChanged,
}

// 具体事件类型
#[derive(Clone, Serialize, Deserialize)]
pub struct UserRegisteredEvent {
    pub user_id: String,
    pub email: String,
    pub username: String,
    pub registration_date: DateTime<Utc>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct ProductViewedEvent {
    pub user_id: String,
    pub product_id: String,
    pub view_duration: Duration,
    pub source: String,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct OrderCreatedEvent {
    pub order_id: String,
    pub user_id: String,
    pub items: Vec<OrderItem>,
    pub total_amount: Money,
    pub shipping_address: Address,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct PaymentProcessedEvent {
    pub payment_id: String,
    pub order_id: String,
    pub amount: Money,
    pub payment_method: PaymentMethod,
    pub status: PaymentStatus,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct InventoryUpdatedEvent {
    pub product_id: String,
    pub old_quantity: i32,
    pub new_quantity: i32,
    pub reason: InventoryUpdateReason,
}
```

### 4.2 事件处理器

```rust
pub struct EventDrivenECommerce {
    event_bus: EventBus,
    event_handlers: HashMap<ECommerceEventType, Vec<Box<dyn EventHandler>>>,
    saga_orchestrator: SagaOrchestrator,
    notification_service: NotificationService,
}

impl EventDrivenECommerce {
    pub async fn process_event(&self, event: ECommerceEvent) -> Result<(), EventError> {
        // 1. 发布事件到事件总线
        self.event_bus.publish(event.clone()).await?;
        
        // 2. 处理事件
        if let Some(handlers) = self.event_handlers.get(&event.event_type) {
            for handler in handlers {
                handler.handle(&event).await?;
            }
        }
        
        // 3. 处理分布式事务
        if self.requires_saga(&event.event_type) {
            self.saga_orchestrator.process_saga(&event).await?;
        }
        
        // 4. 发送通知
        self.notification_service.send_notifications(&event).await?;
        
        Ok(())
    }
    
    pub async fn subscribe_to_events(
        &mut self,
        event_type: ECommerceEventType,
        handler: Box<dyn EventHandler>,
    ) {
        self.event_handlers
            .entry(event_type)
            .or_insert_with(Vec::new)
            .push(handler);
    }
}

pub trait EventHandler {
    async fn handle(&self, event: &ECommerceEvent) -> Result<(), EventError>;
}

// 用户注册事件处理器
pub struct UserRegistrationHandler {
    notification_service: Arc<NotificationService>,
    recommendation_service: Arc<RecommendationService>,
}

impl EventHandler for UserRegistrationHandler {
    async fn handle(&self, event: &ECommerceEvent) -> Result<(), EventError> {
        if let ECommerceEventType::UserRegistered = event.event_type {
            let registration_data: UserRegisteredEvent = serde_json::from_value(event.data.clone())?;
            
            // 发送欢迎邮件
            self.notification_service.send_welcome_email(&registration_data).await?;
            
            // 初始化推荐系统
            self.recommendation_service.initialize_user_profile(&registration_data.user_id).await?;
        }
        Ok(())
    }
}

// 产品浏览事件处理器
pub struct ProductViewHandler {
    recommendation_service: Arc<RecommendationService>,
    analytics_service: Arc<AnalyticsService>,
}

impl EventHandler for ProductViewHandler {
    async fn handle(&self, event: &ECommerceEvent) -> Result<(), EventError> {
        if let ECommerceEventType::ProductViewed = event.event_type {
            let view_data: ProductViewedEvent = serde_json::from_value(event.data.clone())?;
            
            // 更新用户行为数据
            self.analytics_service.record_product_view(&view_data).await?;
            
            // 更新推荐模型
            self.recommendation_service.update_user_preferences(&view_data).await?;
        }
        Ok(())
    }
}

// 订单创建事件处理器
pub struct OrderCreatedHandler {
    inventory_service: Arc<InventoryService>,
    payment_service: Arc<PaymentService>,
    notification_service: Arc<NotificationService>,
}

impl EventHandler for OrderCreatedHandler {
    async fn handle(&self, event: &ECommerceEvent) -> Result<(), EventError> {
        if let ECommerceEventType::OrderCreated = event.event_type {
            let order_data: OrderCreatedEvent = serde_json::from_value(event.data.clone())?;
            
            // 预留库存
            self.inventory_service.reserve_inventory(&order_data).await?;
            
            // 创建支付意图
            self.payment_service.create_payment_intent(&order_data).await?;
            
            // 发送订单确认邮件
            self.notification_service.send_order_confirmation(&order_data).await?;
        }
        Ok(())
    }
}

// 支付处理事件处理器
pub struct PaymentProcessedHandler {
    order_service: Arc<OrderService>,
    inventory_service: Arc<InventoryService>,
    notification_service: Arc<NotificationService>,
}

impl EventHandler for PaymentProcessedHandler {
    async fn handle(&self, event: &ECommerceEvent) -> Result<(), EventError> {
        if let ECommerceEventType::PaymentProcessed = event.event_type {
            let payment_data: PaymentProcessedEvent = serde_json::from_value(event.data.clone())?;
            
            if payment_data.status == PaymentStatus::Succeeded {
                // 更新订单状态
                self.order_service.update_order_status(&payment_data.order_id, OrderStatus::Paid).await?;
                
                // 确认库存扣减
                self.inventory_service.confirm_inventory_deduction(&payment_data.order_id).await?;
                
                // 发送支付成功通知
                self.notification_service.send_payment_success(&payment_data).await?;
            } else {
                // 处理支付失败
                self.order_service.update_order_status(&payment_data.order_id, OrderStatus::PaymentFailed).await?;
                
                // 释放预留库存
                self.inventory_service.release_reserved_inventory(&payment_data.order_id).await?;
                
                // 发送支付失败通知
                self.notification_service.send_payment_failure(&payment_data).await?;
            }
        }
        Ok(())
    }
}
```

---

## 5. 用户与产品管理

### 5.1 用户管理

```rust
#[derive(Serialize, Deserialize)]
pub struct User {
    pub id: String,
    pub email: String,
    pub username: String,
    pub profile: UserProfile,
    pub preferences: UserPreferences,
    pub addresses: Vec<Address>,
    pub payment_methods: Vec<PaymentMethod>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Serialize, Deserialize)]
pub struct UserProfile {
    pub first_name: String,
    pub last_name: String,
    pub phone: Option<String>,
    pub date_of_birth: Option<Date<Utc>>,
    pub avatar_url: Option<String>,
    pub language: String,
    pub currency: String,
}

#[derive(Serialize, Deserialize)]
pub struct UserPreferences {
    pub email_notifications: bool,
    pub sms_notifications: bool,
    pub push_notifications: bool,
    pub marketing_emails: bool,
    pub theme: Theme,
    pub timezone: String,
}

#[derive(Serialize, Deserialize)]
pub enum Theme {
    Light,
    Dark,
    Auto,
}

#[derive(Serialize, Deserialize)]
pub struct Address {
    pub id: String,
    pub type_: AddressType,
    pub first_name: String,
    pub last_name: String,
    pub company: Option<String>,
    pub address_line1: String,
    pub address_line2: Option<String>,
    pub city: String,
    pub state: String,
    pub postal_code: String,
    pub country: String,
    pub phone: String,
    pub is_default: bool,
}

#[derive(Serialize, Deserialize)]
pub enum AddressType {
    Billing,
    Shipping,
    Both,
}

#[derive(Serialize, Deserialize)]
pub struct PaymentMethod {
    pub id: String,
    pub type_: PaymentMethodType,
    pub card_last4: Option<String>,
    pub card_brand: Option<CardBrand>,
    pub expiry_month: Option<u8>,
    pub expiry_year: Option<u16>,
    pub is_default: bool,
    pub created_at: DateTime<Utc>,
}

#[derive(Serialize, Deserialize)]
pub enum PaymentMethodType {
    CreditCard,
    DebitCard,
    PayPal,
    ApplePay,
    GooglePay,
}

#[derive(Serialize, Deserialize)]
pub enum CardBrand {
    Visa,
    Mastercard,
    AmericanExpress,
    Discover,
}
```

### 5.2 产品管理

```rust
#[derive(Serialize, Deserialize)]
pub struct Product {
    pub id: String,
    pub name: String,
    pub description: String,
    pub category: Category,
    pub brand: String,
    pub sku: String,
    pub price: Money,
    pub sale_price: Option<Money>,
    pub inventory: InventoryInfo,
    pub images: Vec<ProductImage>,
    pub attributes: HashMap<String, String>,
    pub variants: Vec<ProductVariant>,
    pub status: ProductStatus,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Serialize, Deserialize)]
pub struct Category {
    pub id: String,
    pub name: String,
    pub parent_id: Option<String>,
    pub level: u32,
    pub path: Vec<String>,
}

#[derive(Serialize, Deserialize)]
pub struct Money {
    pub amount: Decimal,
    pub currency: Currency,
}

#[derive(Serialize, Deserialize)]
pub enum Currency {
    USD,
    EUR,
    GBP,
    JPY,
    CNY,
}

#[derive(Serialize, Deserialize)]
pub struct InventoryInfo {
    pub quantity: i32,
    pub reserved_quantity: i32,
    pub available_quantity: i32,
    pub low_stock_threshold: i32,
    pub reorder_point: i32,
}

#[derive(Serialize, Deserialize)]
pub struct ProductImage {
    pub id: String,
    pub url: String,
    pub alt_text: String,
    pub is_primary: bool,
    pub sort_order: i32,
}

#[derive(Serialize, Deserialize)]
pub struct ProductVariant {
    pub id: String,
    pub sku: String,
    pub attributes: HashMap<String, String>,
    pub price: Money,
    pub inventory: InventoryInfo,
    pub images: Vec<ProductImage>,
}

#[derive(Serialize, Deserialize)]
pub enum ProductStatus {
    Draft,
    Active,
    Inactive,
    Discontinued,
}

// 产品搜索
#[derive(Serialize, Deserialize)]
pub struct SearchQuery {
    pub query: String,
    pub category_id: Option<String>,
    pub brand: Option<String>,
    pub price_min: Option<Money>,
    pub price_max: Option<Money>,
    pub attributes: HashMap<String, String>,
    pub sort_by: SortBy,
    pub sort_order: SortOrder,
    pub page: u32,
    pub page_size: u32,
}

#[derive(Serialize, Deserialize)]
pub enum SortBy {
    Relevance,
    Price,
    Name,
    Rating,
    Newest,
}

#[derive(Serialize, Deserialize)]
pub enum SortOrder {
    Asc,
    Desc,
}

#[derive(Serialize, Deserialize)]
pub struct SearchResult {
    pub products: Vec<Product>,
    pub total_count: u64,
    pub page: u32,
    pub page_size: u32,
    pub facets: Vec<Facet>,
}

#[derive(Serialize, Deserialize)]
pub struct Facet {
    pub field: String,
    pub values: Vec<FacetValue>,
}

#[derive(Serialize, Deserialize)]
pub struct FacetValue {
    pub value: String,
    pub count: u64,
}
```

---

## 6. 订单与支付系统

### 6.1 订单管理

```rust
#[derive(Serialize, Deserialize)]
pub struct Order {
    pub id: String,
    pub user_id: String,
    pub order_number: String,
    pub status: OrderStatus,
    pub items: Vec<OrderItem>,
    pub subtotal: Money,
    pub tax: Money,
    pub shipping: Money,
    pub discount: Money,
    pub total: Money,
    pub billing_address: Address,
    pub shipping_address: Address,
    pub payment_method: PaymentMethod,
    pub shipping_method: ShippingMethod,
    pub notes: Option<String>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Serialize, Deserialize)]
pub enum OrderStatus {
    Pending,
    Confirmed,
    Paid,
    Processing,
    Shipped,
    Delivered,
    Cancelled,
    Refunded,
    PaymentFailed,
}

#[derive(Serialize, Deserialize)]
pub struct OrderItem {
    pub id: String,
    pub product_id: String,
    pub variant_id: Option<String>,
    pub name: String,
    pub sku: String,
    pub quantity: u32,
    pub unit_price: Money,
    pub total_price: Money,
    pub attributes: HashMap<String, String>,
}

#[derive(Serialize, Deserialize)]
pub struct ShippingMethod {
    pub id: String,
    pub name: String,
    pub carrier: String,
    pub service: String,
    pub cost: Money,
    pub estimated_days: u32,
}

// 订单服务
pub struct OrderService {
    order_repository: Arc<OrderRepository>,
    inventory_service: Arc<InventoryService>,
    payment_service: Arc<PaymentService>,
    notification_service: Arc<NotificationService>,
}

impl OrderService {
    pub async fn create_order(&self, order_request: CreateOrderRequest) -> Result<Order, ServiceError> {
        // 1. 验证订单数据
        self.validate_order_request(&order_request).await?;
        
        // 2. 检查库存
        self.check_inventory_availability(&order_request.items).await?;
        
        // 3. 计算价格
        let pricing = self.calculate_pricing(&order_request).await?;
        
        // 4. 创建订单
        let order = Order::new(order_request, pricing);
        
        // 5. 保存订单
        let saved_order = self.order_repository.save(&order).await?;
        
        // 6. 预留库存
        self.inventory_service.reserve_inventory(&saved_order).await?;
        
        // 7. 发送订单确认
        self.notification_service.send_order_confirmation(&saved_order).await?;
        
        Ok(saved_order)
    }
    
    pub async fn process_payment(&self, order_id: &str, payment_data: PaymentData) -> Result<PaymentResult, ServiceError> {
        // 1. 获取订单
        let order = self.order_repository.get(order_id).await?;
        
        // 2. 验证订单状态
        if order.status != OrderStatus::Pending {
            return Err(ServiceError::InvalidOrderStatus);
        }
        
        // 3. 处理支付
        let payment_result = self.payment_service.process_payment(&order, &payment_data).await?;
        
        // 4. 更新订单状态
        match payment_result.status {
            PaymentStatus::Succeeded => {
                self.order_repository.update_status(order_id, OrderStatus::Paid).await?;
                self.inventory_service.confirm_inventory_deduction(order_id).await?;
            }
            PaymentStatus::Failed => {
                self.order_repository.update_status(order_id, OrderStatus::PaymentFailed).await?;
                self.inventory_service.release_reserved_inventory(order_id).await?;
            }
        }
        
        Ok(payment_result)
    }
    
    async fn validate_order_request(&self, request: &CreateOrderRequest) -> Result<(), ServiceError> {
        // 验证用户
        if !self.user_exists(&request.user_id).await? {
            return Err(ServiceError::UserNotFound);
        }
        
        // 验证产品
        for item in &request.items {
            if !self.product_exists(&item.product_id).await? {
                return Err(ServiceError::ProductNotFound);
            }
        }
        
        // 验证地址
        if !self.address_valid(&request.shipping_address).await? {
            return Err(ServiceError::InvalidAddress);
        }
        
        Ok(())
    }
    
    async fn calculate_pricing(&self, request: &CreateOrderRequest) -> Result<OrderPricing, ServiceError> {
        let mut subtotal = Money::zero(request.currency);
        
        // 计算商品小计
        for item in &request.items {
            let product = self.get_product(&item.product_id).await?;
            let unit_price = product.get_price();
            let item_total = unit_price * Decimal::from(item.quantity);
            subtotal = subtotal + item_total;
        }
        
        // 计算税费
        let tax = self.calculate_tax(&subtotal, &request.shipping_address).await?;
        
        // 计算运费
        let shipping = self.calculate_shipping(&request.items, &request.shipping_address).await?;
        
        // 计算折扣
        let discount = self.calculate_discount(&subtotal, &request.user_id).await?;
        
        // 计算总计
        let total = subtotal + tax + shipping - discount;
        
        Ok(OrderPricing {
            subtotal,
            tax,
            shipping,
            discount,
            total,
        })
    }
}
```

### 6.2 支付系统

```rust
#[derive(Serialize, Deserialize)]
pub struct Payment {
    pub id: String,
    pub order_id: String,
    pub amount: Money,
    pub currency: Currency,
    pub payment_method: PaymentMethod,
    pub status: PaymentStatus,
    pub gateway_response: Option<GatewayResponse>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Serialize, Deserialize)]
pub enum PaymentStatus {
    Pending,
    Processing,
    Succeeded,
    Failed,
    Cancelled,
    Refunded,
}

#[derive(Serialize, Deserialize)]
pub struct GatewayResponse {
    pub gateway: String,
    pub transaction_id: String,
    pub response_code: String,
    pub response_message: String,
    pub raw_response: serde_json::Value,
}

// 支付服务
pub struct PaymentService {
    payment_repository: Arc<PaymentRepository>,
    stripe_client: Arc<StripeClient>,
    paypal_client: Arc<PayPalClient>,
    encryption_service: Arc<EncryptionService>,
}

impl PaymentService {
    pub async fn process_payment(&self, order: &Order, payment_data: &PaymentData) -> Result<PaymentResult, ServiceError> {
        // 1. 创建支付记录
        let payment = Payment::new(order, payment_data);
        let saved_payment = self.payment_repository.save(&payment).await?;
        
        // 2. 根据支付方式处理
        let result = match payment_data.method {
            PaymentMethodType::CreditCard | PaymentMethodType::DebitCard => {
                self.process_card_payment(&saved_payment, payment_data).await?
            }
            PaymentMethodType::PayPal => {
                self.process_paypal_payment(&saved_payment, payment_data).await?
            }
            _ => return Err(ServiceError::UnsupportedPaymentMethod),
        };
        
        // 3. 更新支付状态
        self.payment_repository.update_status(&saved_payment.id, result.status).await?;
        
        Ok(result)
    }
    
    async fn process_card_payment(&self, payment: &Payment, payment_data: &PaymentData) -> Result<PaymentResult, ServiceError> {
        // 加密卡号
        let encrypted_card = self.encryption_service.encrypt_card_data(&payment_data.card_data).await?;
        
        // 调用Stripe API
        let stripe_response = self.stripe_client.create_payment_intent(
            payment.amount,
            &encrypted_card,
            &payment.order_id,
        ).await?;
        
        Ok(PaymentResult {
            status: stripe_response.status,
            transaction_id: stripe_response.transaction_id,
            gateway_response: Some(stripe_response),
        })
    }
    
    async fn process_paypal_payment(&self, payment: &Payment, payment_data: &PaymentData) -> Result<PaymentResult, ServiceError> {
        // 调用PayPal API
        let paypal_response = self.paypal_client.create_order(
            payment.amount,
            &payment.order_id,
            &payment_data.paypal_data,
        ).await?;
        
        Ok(PaymentResult {
            status: paypal_response.status,
            transaction_id: paypal_response.transaction_id,
            gateway_response: Some(paypal_response),
        })
    }
}

// Stripe客户端
pub struct StripeClient {
    secret_key: String,
    http_client: reqwest::Client,
}

impl StripeClient {
    pub async fn create_payment_intent(
        &self,
        amount: Money,
        card_data: &EncryptedCardData,
        order_id: &str,
    ) -> Result<StripeResponse, ServiceError> {
        let request_body = serde_json::json!({
            "amount": amount.amount,
            "currency": amount.currency.to_string().to_lowercase(),
            "payment_method_data": {
                "type": "card",
                "card": {
                    "token": card_data.token,
                }
            },
            "metadata": {
                "order_id": order_id,
            },
            "confirm": true,
        });
        
        let response = self.http_client
            .post("https://api.stripe.com/v1/payment_intents")
            .header("Authorization", format!("Bearer {}", self.secret_key))
            .header("Content-Type", "application/x-www-form-urlencoded")
            .body(request_body.to_string())
            .send()
            .await?;
        
        let stripe_response: StripeResponse = response.json().await?;
        Ok(stripe_response)
    }
}
```

---

## 7. 推荐与库存管理

### 7.1 推荐系统

```rust
pub struct RecommendationService {
    user_repository: Arc<UserRepository>,
    product_repository: Arc<ProductRepository>,
    behavior_repository: Arc<BehaviorRepository>,
    ml_model: Arc<RecommendationModel>,
    cache: Arc<RedisCache>,
}

impl RecommendationService {
    pub async fn get_recommendations(&self, user_id: &str, limit: u32) -> Result<Vec<Product>, ServiceError> {
        // 1. 检查缓存
        if let Some(cached_recommendations) = self.cache.get_recommendations(user_id).await? {
            return Ok(cached_recommendations);
        }
        
        // 2. 获取用户行为数据
        let user_behaviors = self.behavior_repository.get_user_behaviors(user_id).await?;
        
        // 3. 生成推荐
        let recommendations = self.generate_recommendations(user_id, &user_behaviors, limit).await?;
        
        // 4. 缓存推荐结果
        self.cache.set_recommendations(user_id, &recommendations).await?;
        
        Ok(recommendations)
    }
    
    pub async fn update_user_preferences(&self, view_data: &ProductViewedEvent) -> Result<(), ServiceError> {
        // 1. 记录用户行为
        let behavior = UserBehavior {
            user_id: view_data.user_id.clone(),
            product_id: view_data.product_id.clone(),
            behavior_type: BehaviorType::View,
            timestamp: view_data.timestamp,
            metadata: serde_json::json!({
                "duration": view_data.view_duration.as_secs(),
                "source": view_data.source,
            }),
        };
        
        self.behavior_repository.save(&behavior).await?;
        
        // 2. 更新推荐模型
        self.ml_model.update_user_preferences(&behavior).await?;
        
        Ok(())
    }
    
    async fn generate_recommendations(
        &self,
        user_id: &str,
        behaviors: &[UserBehavior],
        limit: u32,
    ) -> Result<Vec<Product>, ServiceError> {
        // 1. 协同过滤推荐
        let collaborative_recommendations = self.ml_model.get_collaborative_recommendations(user_id, limit).await?;
        
        // 2. 基于内容的推荐
        let content_based_recommendations = self.ml_model.get_content_based_recommendations(behaviors, limit).await?;
        
        // 3. 混合推荐
        let mixed_recommendations = self.mix_recommendations(
            &collaborative_recommendations,
            &content_based_recommendations,
            limit,
        );
        
        // 4. 获取产品详情
        let mut products = Vec::new();
        for product_id in mixed_recommendations {
            if let Some(product) = self.product_repository.get(&product_id).await? {
                products.push(product);
            }
        }
        
        Ok(products)
    }
    
    fn mix_recommendations(
        &self,
        collaborative: &[String],
        content_based: &[String],
        limit: u32,
    ) -> Vec<String> {
        let mut mixed = Vec::new();
        let mut collaborative_iter = collaborative.iter();
        let mut content_based_iter = content_based.iter();
        
        while mixed.len() < limit as usize {
            // 交替添加两种推荐结果
            if let Some(id) = collaborative_iter.next() {
                if !mixed.contains(id) {
                    mixed.push(id.clone());
                }
            }
            
            if mixed.len() >= limit as usize {
                break;
            }
            
            if let Some(id) = content_based_iter.next() {
                if !mixed.contains(id) {
                    mixed.push(id.clone());
                }
            }
        }
        
        mixed
    }
}

#[derive(Serialize, Deserialize)]
pub struct UserBehavior {
    pub id: String,
    pub user_id: String,
    pub product_id: String,
    pub behavior_type: BehaviorType,
    pub timestamp: DateTime<Utc>,
    pub metadata: serde_json::Value,
}

#[derive(Serialize, Deserialize)]
pub enum BehaviorType {
    View,
    AddToCart,
    Purchase,
    Search,
    Click,
}
```

### 7.2 库存管理

```rust
pub struct InventoryService {
    inventory_repository: Arc<InventoryRepository>,
    order_repository: Arc<OrderRepository>,
    notification_service: Arc<NotificationService>,
    cache: Arc<RedisCache>,
}

impl InventoryService {
    pub async fn reserve_inventory(&self, order: &Order) -> Result<(), ServiceError> {
        for item in &order.items {
            // 1. 检查可用库存
            let available = self.get_available_quantity(&item.product_id).await?;
            
            if available < item.quantity {
                return Err(ServiceError::InsufficientInventory);
            }
            
            // 2. 预留库存
            self.inventory_repository.reserve_inventory(
                &item.product_id,
                item.quantity,
                &order.id,
            ).await?;
        }
        
        Ok(())
    }
    
    pub async fn confirm_inventory_deduction(&self, order_id: &str) -> Result<(), ServiceError> {
        let order = self.order_repository.get(order_id).await?;
        
        for item in &order.items {
            // 确认扣减库存
            self.inventory_repository.confirm_reservation(
                &item.product_id,
                item.quantity,
                order_id,
            ).await?;
            
            // 检查是否需要补货
            self.check_reorder_point(&item.product_id).await?;
        }
        
        Ok(())
    }
    
    pub async fn release_reserved_inventory(&self, order_id: &str) -> Result<(), ServiceError> {
        let order = self.order_repository.get(order_id).await?;
        
        for item in &order.items {
            // 释放预留库存
            self.inventory_repository.release_reservation(
                &item.product_id,
                item.quantity,
                order_id,
            ).await?;
        }
        
        Ok(())
    }
    
    pub async fn update_inventory(&self, product_id: &str, quantity: i32, reason: InventoryUpdateReason) -> Result<(), ServiceError> {
        // 1. 更新库存
        self.inventory_repository.update_quantity(product_id, quantity).await?;
        
        // 2. 清除缓存
        self.cache.invalidate_inventory(product_id).await?;
        
        // 3. 检查库存阈值
        self.check_inventory_thresholds(product_id).await?;
        
        // 4. 发布库存更新事件
        self.publish_inventory_event(product_id, quantity, reason).await?;
        
        Ok(())
    }
    
    async fn check_reorder_point(&self, product_id: &str) -> Result<(), ServiceError> {
        let inventory = self.inventory_repository.get(product_id).await?;
        
        if inventory.available_quantity <= inventory.reorder_point {
            // 发送补货通知
            self.notification_service.send_reorder_notification(product_id, &inventory).await?;
        }
        
        Ok(())
    }
    
    async fn check_inventory_thresholds(&self, product_id: &str) -> Result<(), ServiceError> {
        let inventory = self.inventory_repository.get(product_id).await?;
        
        if inventory.available_quantity <= inventory.low_stock_threshold {
            // 发送低库存通知
            self.notification_service.send_low_stock_notification(product_id, &inventory).await?;
        }
        
        if inventory.available_quantity == 0 {
            // 发送缺货通知
            self.notification_service.send_out_of_stock_notification(product_id).await?;
        }
        
        Ok(())
    }
}

#[derive(Serialize, Deserialize)]
pub enum InventoryUpdateReason {
    Purchase,
    Return,
    Adjustment,
    Damage,
    Expiry,
}
```

---

## 总结

本文档提供了电商行业的完整架构指南，包括：

1. **技术栈选型**: 基于Rust的电商开发技术栈
2. **微服务架构**: 用户服务、产品服务、订单服务、支付服务等
3. **事件驱动**: 电商事件定义、事件处理器、事件总线
4. **用户管理**: 用户注册、认证、地址管理、支付方式等
5. **产品管理**: 产品信息、分类、搜索、库存等
6. **订单系统**: 订单创建、支付处理、状态管理等
7. **推荐系统**: 协同过滤、基于内容的推荐、混合推荐等
8. **库存管理**: 库存预留、确认、释放、补货等

这些最佳实践为构建高性能、可扩展的电商系统提供了全面的指导。
