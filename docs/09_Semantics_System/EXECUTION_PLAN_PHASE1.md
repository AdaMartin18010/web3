# Web3语义知识系统第一阶段执行计划 / Web3 Semantics Knowledge System Phase 1 Execution Plan

## 概述 / Overview

本文档详细规划Web3语义知识系统第一阶段的具体执行任务，包括基础架构开发、核心服务实现和开发环境搭建。

This document details the specific execution tasks for Phase 1 of the Web3 semantics knowledge system, including basic architecture development, core service implementation, and development environment setup.

## 1. 第一阶段目标 / Phase 1 Objectives

### 1.1 主要目标 / Main Objectives

- **建立技术平台基础架构** / Establish technical platform basic architecture
- **实现核心微服务** / Implement core microservices
- **搭建开发环境** / Set up development environment
- **建立数据存储系统** / Establish data storage system

### 1.2 成功标准 / Success Criteria

- ✅ 微服务架构运行正常
- ✅ 数据存储系统就绪
- ✅ 开发环境完善
- ✅ 基础API接口可用

## 2. 具体执行任务 / Specific Execution Tasks

### 2.1 任务1：项目初始化 (Task 1: Project Initialization)

**时间**: 第1周 / **Time**: Week 1

**具体步骤 / Specific Steps:**

#### 2.1.1 创建项目结构

```bash
# 创建项目目录
mkdir -p web3-semantics-platform
cd web3-semantics-platform

# 创建子目录
mkdir -p {frontend,backend,infrastructure,docs,tests}
mkdir -p backend/{services,models,controllers,utils}
mkdir -p frontend/{src,public,components,pages}
mkdir -p infrastructure/{docker,kubernetes,monitoring}
```

#### 2.1.2 初始化Git仓库

```bash
# 初始化Git
git init
git add .
git commit -m "Initial commit: Web3 Semantics Knowledge System Platform"

# 创建.gitignore
cat > .gitignore << 'EOF'
# Dependencies
node_modules/
target/
*.lock

# Environment
.env
.env.local
.env.production

# Logs
*.log
npm-debug.log*

# IDE
.vscode/
.idea/
*.swp
*.swo

# OS
.DS_Store
Thumbs.db

# Build
dist/
build/
EOF
```

#### 2.1.3 创建Docker环境

```yaml
# docker-compose.yml
version: '3.8'
services:
  postgres:
    image: postgres:15
    environment:
      POSTGRES_DB: web3_semantics
      POSTGRES_USER: admin
      POSTGRES_PASSWORD: password
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis_data:/data

  elasticsearch:
    image: elasticsearch:8.8.0
    environment:
      - discovery.type=single-node
      - xpack.security.enabled=false
    ports:
      - "9200:9200"
    volumes:
      - elasticsearch_data:/usr/share/elasticsearch/data

  neo4j:
    image: neo4j:5.8
    environment:
      NEO4J_AUTH: neo4j/password
    ports:
      - "7474:7474"
      - "7687:7687"
    volumes:
      - neo4j_data:/data

volumes:
  postgres_data:
  redis_data:
  elasticsearch_data:
  neo4j_data:
```

### 2.2 任务2：后端服务开发 (Task 2: Backend Service Development)

**时间**: 第2-4周 / **Time**: Weeks 2-4

**具体步骤 / Specific Steps:**

#### 2.2.1 创建Rust项目

```bash
cd backend
cargo new web3-semantics-api
cd web3-semantics-api
```

#### 2.2.2 配置Cargo.toml

```toml
[package]
name = "web3-semantics-api"
version = "0.1.0"
edition = "2021"

[dependencies]
actix-web = "4.3"
actix-rt = "2.8"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
tokio = { version = "1.0", features = ["full"] }
sqlx = { version = "0.6", features = ["runtime-tokio-rustls", "postgres"] }
redis = { version = "0.23", features = ["tokio-comp"] }
elasticsearch = "8.8"
neo4rs = "0.6"
uuid = { version = "1.0", features = ["v4"] }
chrono = { version = "0.4", features = ["serde"] }
log = "0.4"
env_logger = "0.10"
dotenv = "0.15"
anyhow = "1.0"
thiserror = "1.0"
validator = { version = "0.16", features = ["derive"] }
bcrypt = "0.15"
jsonwebtoken = "8.3"
reqwest = { version = "0.11", features = ["json"] }
futures = "0.3"
async-trait = "0.1"
tracing = "0.1"
tracing-subscriber = "0.3"
```

#### 2.2.3 实现用户服务

```rust
// src/services/user/user_service.rs
use actix_web::{web, HttpResponse, Result};
use serde::{Deserialize, Serialize};
use sqlx::PgPool;
use uuid::Uuid;
use chrono::{DateTime, Utc};

#[derive(Debug, Serialize, Deserialize)]
pub struct User {
    pub id: Uuid,
    pub username: String,
    pub email: String,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Deserialize)]
pub struct CreateUserRequest {
    pub username: String,
    pub email: String,
    pub password: String,
}

pub struct UserService {
    pool: PgPool,
}

impl UserService {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }

    pub async fn create_user(&self, request: CreateUserRequest) -> Result<User, sqlx::Error> {
        let user_id = Uuid::new_v4();
        let hashed_password = bcrypt::hash(request.password.as_bytes(), bcrypt::DEFAULT_COST)?;
        
        let user = sqlx::query_as!(
            User,
            r#"
            INSERT INTO users (id, username, email, password_hash, created_at, updated_at)
            VALUES ($1, $2, $3, $4, $5, $5)
            RETURNING id, username, email, created_at, updated_at
            "#,
            user_id,
            request.username,
            request.email,
            hashed_password,
            Utc::now()
        )
        .fetch_one(&self.pool)
        .await?;

        Ok(user)
    }

    pub async fn get_user_by_id(&self, user_id: Uuid) -> Result<Option<User>, sqlx::Error> {
        let user = sqlx::query_as!(
            User,
            r#"
            SELECT id, username, email, created_at, updated_at
            FROM users
            WHERE id = $1
            "#,
            user_id
        )
        .fetch_optional(&self.pool)
        .await?;

        Ok(user)
    }
}
```

#### 2.2.4 实现内容服务

```rust
// src/services/content/content_service.rs
use actix_web::{web, HttpResponse, Result};
use serde::{Deserialize, Serialize};
use sqlx::PgPool;
use uuid::Uuid;
use chrono::{DateTime, Utc};

#[derive(Debug, Serialize, Deserialize)]
pub struct Content {
    pub id: Uuid,
    pub title: String,
    pub content: String,
    pub content_type: String,
    pub author_id: Uuid,
    pub status: String,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Deserialize)]
pub struct CreateContentRequest {
    pub title: String,
    pub content: String,
    pub content_type: String,
    pub author_id: Uuid,
}

pub struct ContentService {
    pool: PgPool,
}

impl ContentService {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }

    pub async fn create_content(&self, request: CreateContentRequest) -> Result<Content, sqlx::Error> {
        let content_id = Uuid::new_v4();
        
        let content = sqlx::query_as!(
            Content,
            r#"
            INSERT INTO contents (id, title, content, content_type, author_id, status, created_at, updated_at)
            VALUES ($1, $2, $3, $4, $5, 'draft', $6, $6)
            RETURNING id, title, content, content_type, author_id, status, created_at, updated_at
            "#,
            content_id,
            request.title,
            request.content,
            request.content_type,
            request.author_id,
            Utc::now()
        )
        .fetch_one(&self.pool)
        .await?;

        Ok(content)
    }

    pub async fn search_contents(&self, query: &str) -> Result<Vec<Content>, sqlx::Error> {
        let contents = sqlx::query_as!(
            Content,
            r#"
            SELECT id, title, content, content_type, author_id, status, created_at, updated_at
            FROM contents
            WHERE title ILIKE $1 OR content ILIKE $1
            ORDER BY created_at DESC
            "#,
            format!("%{}%", query)
        )
        .fetch_all(&self.pool)
        .await?;

        Ok(contents)
    }
}
```

### 2.3 任务3：数据库初始化 (Task 3: Database Initialization)

**时间**: 第3周 / **Time**: Week 3

**具体步骤 / Specific Steps:**

#### 2.3.1 创建数据库表

```sql
-- 数据库初始化脚本
-- Database Initialization Script

-- 创建用户表
CREATE TABLE users (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    username VARCHAR(50) UNIQUE NOT NULL,
    email VARCHAR(255) UNIQUE NOT NULL,
    password_hash VARCHAR(255) NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- 创建内容表
CREATE TABLE contents (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    title VARCHAR(255) NOT NULL,
    content TEXT NOT NULL,
    content_type VARCHAR(50) NOT NULL,
    author_id UUID NOT NULL REFERENCES users(id),
    status VARCHAR(20) DEFAULT 'draft',
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- 创建知识图谱节点表
CREATE TABLE knowledge_nodes (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    name VARCHAR(255) NOT NULL,
    node_type VARCHAR(50) NOT NULL,
    properties JSONB DEFAULT '{}',
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- 创建知识图谱关系表
CREATE TABLE knowledge_relationships (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    source_node_id UUID NOT NULL REFERENCES knowledge_nodes(id),
    target_node_id UUID NOT NULL REFERENCES knowledge_nodes(id),
    relationship_type VARCHAR(50) NOT NULL,
    properties JSONB DEFAULT '{}',
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- 创建学习路径表
CREATE TABLE learning_paths (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    user_id UUID NOT NULL REFERENCES users(id),
    path_name VARCHAR(255) NOT NULL,
    path_data JSONB NOT NULL,
    progress JSONB DEFAULT '{}',
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- 创建用户活动表
CREATE TABLE user_activities (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    user_id UUID NOT NULL REFERENCES users(id),
    activity_type VARCHAR(50) NOT NULL,
    activity_data JSONB DEFAULT '{}',
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- 创建索引
CREATE INDEX idx_contents_author_id ON contents(author_id);
CREATE INDEX idx_contents_status ON contents(status);
CREATE INDEX idx_contents_created_at ON contents(created_at);
CREATE INDEX idx_knowledge_nodes_type ON knowledge_nodes(node_type);
CREATE INDEX idx_knowledge_relationships_type ON knowledge_relationships(relationship_type);
CREATE INDEX idx_user_activities_user_id ON user_activities(user_id);
CREATE INDEX idx_user_activities_type ON user_activities(activity_type);
CREATE INDEX idx_user_activities_created_at ON user_activities(created_at);

-- 创建全文搜索索引
CREATE INDEX idx_contents_search ON contents USING gin(to_tsvector('english', title || ' ' || content));
```

#### 2.3.2 创建数据库迁移脚本

```rust
// src/bin/migrate.rs
use sqlx::PgPool;
use std::env;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let database_url = env::var("DATABASE_URL")
        .unwrap_or_else(|_| "postgres://admin:password@localhost:5432/web3_semantics".to_string());
    
    let pool = PgPool::connect(&database_url).await?;
    
    // 运行迁移
    sqlx::migrate!("./migrations").run(&pool).await?;
    
    println!("✅ Database migration completed successfully");
    Ok(())
}
```

### 2.4 任务4：API路由配置 (Task 4: API Route Configuration)

**时间**: 第4周 / **Time**: Week 4

**具体步骤 / Specific Steps:**

#### 2.4.1 主应用配置

```rust
// src/main.rs
use actix_web::{web, App, HttpServer, middleware};
use sqlx::PgPool;
use elasticsearch::Elasticsearch;

mod services;
mod controllers;
mod models;
mod middleware;
mod utils;

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    // 初始化日志
    env_logger::init_from_env(env_logger::Env::new().default_filter_or("info"));

    // 数据库连接
    let database_url = std::env::var("DATABASE_URL")
        .unwrap_or_else(|_| "postgres://admin:password@localhost:5432/web3_semantics".to_string());
    
    let pool = PgPool::connect(&database_url)
        .await
        .expect("Failed to connect to database");

    // Elasticsearch连接
    let elasticsearch_url = std::env::var("ELASTICSEARCH_URL")
        .unwrap_or_else(|_| "http://localhost:9200".to_string());
    
    let elasticsearch = Elasticsearch::new(
        elasticsearch::http::transport::SingleNodeConnection::new(elasticsearch_url)
            .expect("Failed to connect to Elasticsearch")
    );

    // 启动HTTP服务器
    HttpServer::new(move || {
        App::new()
            .wrap(middleware::Logger::default())
            .wrap(middleware::Compress::default())
            .app_data(web::Data::new(pool.clone()))
            .app_data(web::Data::new(elasticsearch.clone()))
            .service(
                web::scope("/api/v1")
                    .configure(controllers::user::configure)
                    .configure(controllers::content::configure)
                    .configure(controllers::search::configure)
                    .configure(controllers::analytics::configure)
            )
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}
```

#### 2.4.2 用户控制器

```rust
// src/controllers/user.rs
use actix_web::{web, HttpResponse, Result};
use crate::services::user::UserService;
use crate::models::user::{CreateUserRequest, UserUpdates};

pub fn configure(cfg: &mut web::ServiceConfig) {
    cfg.service(
        web::scope("/users")
            .route("", web::post().to(create_user))
            .route("/{id}", web::get().to(get_user))
            .route("/{id}", web::put().to(update_user))
            .route("/{id}", web::delete().to(delete_user))
    );
}

async fn create_user(
    pool: web::Data<PgPool>,
    request: web::Json<CreateUserRequest>,
) -> Result<HttpResponse> {
    let user_service = UserService::new(pool.get_ref().clone());
    
    match user_service.create_user(request.into_inner()).await {
        Ok(user) => Ok(HttpResponse::Created().json(user)),
        Err(e) => Ok(HttpResponse::InternalServerError().body(e.to_string())),
    }
}

async fn get_user(
    pool: web::Data<PgPool>,
    path: web::Path<uuid::Uuid>,
) -> Result<HttpResponse> {
    let user_service = UserService::new(pool.get_ref().clone());
    
    match user_service.get_user_by_id(path.into_inner()).await {
        Ok(Some(user)) => Ok(HttpResponse::Ok().json(user)),
        Ok(None) => Ok(HttpResponse::NotFound().body("User not found")),
        Err(e) => Ok(HttpResponse::InternalServerError().body(e.to_string())),
    }
}
```

### 2.5 任务5：前端基础开发 (Task 5: Frontend Basic Development)

**时间**: 第5-6周 / **Time**: Weeks 5-6

**具体步骤 / Specific Steps:**

#### 2.5.1 创建React应用

```bash
cd ../frontend
npx create-react-app web3-semantics-ui --template typescript
cd web3-semantics-ui
```

#### 2.5.2 安装依赖

```bash
npm install @mui/material @emotion/react @emotion/styled
npm install @mui/icons-material @mui/lab
npm install @reduxjs/toolkit react-redux
npm install react-router-dom
npm install axios
npm install d3 @types/d3
npm install recharts
npm install @types/node
```

#### 2.5.3 创建主应用组件

```typescript
// src/App.tsx
import React from 'react';
import { BrowserRouter as Router, Routes, Route } from 'react-router-dom';
import { ThemeProvider, createTheme } from '@mui/material/styles';
import CssBaseline from '@mui/material/CssBaseline';
import { Provider } from 'react-redux';
import { store } from './store';

import Layout from './components/layout/Layout';
import Home from './pages/Home';
import Dashboard from './pages/Dashboard';
import Knowledge from './pages/Knowledge';
import Search from './pages/Search';
import Profile from './pages/Profile';

const theme = createTheme({
  palette: {
    mode: 'dark',
    primary: {
      main: '#1976d2',
    },
    secondary: {
      main: '#dc004e',
    },
  },
});

function App() {
  return (
    <Provider store={store}>
      <ThemeProvider theme={theme}>
        <CssBaseline />
        <Router>
          <Layout>
            <Routes>
              <Route path="/" element={<Home />} />
              <Route path="/dashboard" element={<Dashboard />} />
              <Route path="/knowledge" element={<Knowledge />} />
              <Route path="/search" element={<Search />} />
              <Route path="/profile" element={<Profile />} />
            </Routes>
          </Layout>
        </Router>
      </ThemeProvider>
    </Provider>
  );
}

export default App;
```

## 3. 测试和验证 / Testing and Validation

### 3.1 单元测试

```rust
// tests/user_service_test.rs
#[cfg(test)]
mod tests {
    use super::*;
    use sqlx::PgPool;

    #[tokio::test]
    async fn test_create_user() {
        let pool = PgPool::connect("postgres://admin:password@localhost:5432/web3_semantics_test").await.unwrap();
        let user_service = UserService::new(pool);
        
        let request = CreateUserRequest {
            username: "testuser".to_string(),
            email: "test@example.com".to_string(),
            password: "password123".to_string(),
        };
        
        let result = user_service.create_user(request).await;
        assert!(result.is_ok());
    }
}
```

### 3.2 集成测试

```rust
// tests/api_integration_test.rs
use actix_web::{test, web, App};
use web3_semantics_api::controllers::user::configure;

#[actix_web::test]
async fn test_create_user_api() {
    let app = test::init_service(
        App::new()
            .service(web::scope("/api/v1").configure(configure))
    ).await;

    let req = test::TestRequest::post()
        .uri("/api/v1/users")
        .set_json(json!({
            "username": "testuser",
            "email": "test@example.com",
            "password": "password123"
        }))
        .to_request();

    let resp = test::call_service(&app, req).await;
    assert!(resp.status().is_success());
}
```

## 4. 部署和监控 / Deployment and Monitoring

### 4.1 Docker部署

```bash
#!/bin/bash
# Docker部署脚本
# Docker Deployment Script

echo "🐳 开始Docker部署..."
echo "🐳 Starting Docker deployment..."

# 构建后端镜像
echo "🔧 构建后端镜像..."
docker build -t web3-semantics-api:latest ./backend

# 构建前端镜像
echo "🔧 构建前端镜像..."
docker build -t web3-semantics-ui:latest ./frontend

# 启动服务
echo "🚀 启动服务..."
docker-compose up -d

# 等待服务启动
echo "⏳ 等待服务启动..."
sleep 30

# 检查服务状态
echo "🔍 检查服务状态..."
docker-compose ps

# 运行数据库迁移
echo "🗄️ 运行数据库迁移..."
docker-compose exec backend cargo run --bin migrate

echo "✅ Docker部署完成"
echo "✅ Docker deployment completed"
```

### 4.2 监控配置

```yaml
# prometheus.yml
global:
  scrape_interval: 15s

scrape_configs:
  - job_name: 'web3-semantics-api'
    static_configs:
      - targets: ['web3-semantics-api:8080']
    metrics_path: '/metrics'
    scrape_interval: 5s

  - job_name: 'postgres'
    static_configs:
      - targets: ['postgres:5432']

  - job_name: 'redis'
    static_configs:
      - targets: ['redis:6379']
```

## 5. 里程碑和检查点 / Milestones and Checkpoints

### 5.1 第1周检查点

- [ ] 项目目录结构创建完成
- [ ] Git仓库初始化完成
- [ ] Docker环境配置完成
- [ ] 基础文档创建完成

### 5.2 第2周检查点

- [ ] Rust项目创建完成
- [ ] 依赖配置完成
- [ ] 基础服务结构创建完成
- [ ] 用户服务实现完成

### 5.3 第3周检查点

- [ ] 数据库表创建完成
- [ ] 数据库迁移脚本完成
- [ ] 内容服务实现完成
- [ ] 基础API测试通过

### 5.4 第4周检查点

- [ ] API路由配置完成
- [ ] 控制器实现完成
- [ ] 集成测试通过
- [ ] 基础功能验证完成

### 5.5 第5-6周检查点

- [ ] React应用创建完成
- [ ] 基础组件实现完成
- [ ] 路由配置完成
- [ ] 前后端联调完成

## 6. 风险控制 / Risk Control

### 6.1 技术风险

**风险识别 / Risk Identification:**

- 技术栈选择风险
- 性能瓶颈风险
- 安全漏洞风险

**应对策略 / Response Strategies:**

- 建立技术评估机制
- 实施性能测试
- 建立安全审计流程

### 6.2 进度风险

**风险识别 / Risk Identification:**

- 开发进度延迟
- 资源分配不足
- 需求变更风险

**应对策略 / Response Strategies:**

- 建立敏捷开发流程
- 实施资源监控
- 建立变更管理机制

## 7. 总结 / Summary

第一阶段执行计划提供了详细的实施路径，包括：

1. **项目初始化**: 建立基础项目结构和开发环境
2. **后端开发**: 实现核心微服务和API接口
3. **数据库设计**: 建立数据存储和索引系统
4. **前端开发**: 创建基础用户界面
5. **测试验证**: 确保代码质量和功能正确性
6. **部署监控**: 建立部署和监控体系

Phase 1 execution plan provides detailed implementation path, including:

1. **Project Initialization**: Establish basic project structure and development environment
2. **Backend Development**: Implement core microservices and API interfaces
3. **Database Design**: Establish data storage and indexing system
4. **Frontend Development**: Create basic user interface
5. **Testing Validation**: Ensure code quality and functional correctness
6. **Deployment Monitoring**: Establish deployment and monitoring system

通过这个计划，我们将成功建立Web3语义知识系统技术平台的基础架构，为后续的功能开发奠定坚实基础。

Through this plan, we will successfully establish the basic architecture of the Web3 semantics knowledge system technical platform, laying a solid foundation for subsequent functional development.
