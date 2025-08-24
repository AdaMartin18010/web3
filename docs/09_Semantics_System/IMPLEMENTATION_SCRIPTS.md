# Web3语义知识系统实施脚本 / Web3 Semantics Knowledge System Implementation Scripts

## 概述 / Overview

本文档提供具体的实施脚本，用于推进Web3语义知识系统技术平台的开发。包括环境搭建、代码生成、测试部署等自动化脚本。

This document provides specific implementation scripts for advancing the development of the Web3 semantics knowledge system technical platform. Including environment setup, code generation, testing deployment and other automated scripts.

## 1. 开发环境搭建脚本 / Development Environment Setup Scripts

### 1.1 项目初始化脚本

```bash
#!/bin/bash
# Web3语义知识系统项目初始化脚本
# Web3 Semantics Knowledge System Project Initialization Script

echo "🚀 开始初始化Web3语义知识系统项目..."
echo "🚀 Starting Web3 Semantics Knowledge System Project Initialization..."

# 创建项目目录结构
mkdir -p web3-semantics-platform/{frontend,backend,infrastructure,docs,tests}
mkdir -p web3-semantics-platform/backend/{services,models,controllers,utils}
mkdir -p web3-semantics-platform/frontend/{src,public,components,pages}
mkdir -p web3-semantics-platform/infrastructure/{docker,kubernetes,monitoring}

# 初始化Git仓库
cd web3-semantics-platform
git init
git add .
git commit -m "Initial commit: Web3 Semantics Knowledge System Platform"

# 创建Docker环境
cat > docker-compose.yml << 'EOF'
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
EOF

echo "✅ 项目目录结构创建完成"
echo "✅ Project directory structure created successfully"
```

### 1.2 后端服务初始化脚本

```bash
#!/bin/bash
# 后端服务初始化脚本
# Backend Service Initialization Script

echo "🔧 初始化后端服务..."
echo "🔧 Initializing backend services..."

# 创建Rust项目
cd backend
cargo new web3-semantics-api
cd web3-semantics-api

# 更新Cargo.toml
cat > Cargo.toml << 'EOF'
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
EOF

# 创建基础服务结构
mkdir -p src/{services,models,controllers,utils,middleware}
mkdir -p src/services/{user,content,search,analytics}

echo "✅ 后端服务初始化完成"
echo "✅ Backend service initialization completed"
```

### 1.3 前端应用初始化脚本

```bash
#!/bin/bash
# 前端应用初始化脚本
# Frontend Application Initialization Script

echo "🎨 初始化前端应用..."
echo "🎨 Initializing frontend application..."

# 创建React应用
cd ../frontend
npx create-react-app web3-semantics-ui --template typescript
cd web3-semantics-ui

# 安装依赖
npm install @mui/material @emotion/react @emotion/styled
npm install @mui/icons-material @mui/lab
npm install @reduxjs/toolkit react-redux
npm install react-router-dom
npm install axios
npm install d3 @types/d3
npm install recharts
npm install @types/node

# 创建应用结构
mkdir -p src/{components,pages,services,store,utils,hooks}
mkdir -p src/components/{common,layout,forms,charts}
mkdir -p src/pages/{home,dashboard,knowledge,search,profile}

echo "✅ 前端应用初始化完成"
echo "✅ Frontend application initialization completed"
```

## 2. 核心服务实现脚本 / Core Service Implementation Scripts

### 2.1 用户服务实现

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

    pub async fn update_user(&self, user_id: Uuid, updates: UserUpdates) -> Result<User, sqlx::Error> {
        let user = sqlx::query_as!(
            User,
            r#"
            UPDATE users
            SET username = COALESCE($2, username),
                email = COALESCE($3, email),
                updated_at = $4
            WHERE id = $1
            RETURNING id, username, email, created_at, updated_at
            "#,
            user_id,
            updates.username,
            updates.email,
            Utc::now()
        )
        .fetch_one(&self.pool)
        .await?;

        Ok(user)
    }
}

#[derive(Debug, Deserialize)]
pub struct UserUpdates {
    pub username: Option<String>,
    pub email: Option<String>,
}
```

### 2.2 内容管理服务实现

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

    pub async fn get_content_by_id(&self, content_id: Uuid) -> Result<Option<Content>, sqlx::Error> {
        let content = sqlx::query_as!(
            Content,
            r#"
            SELECT id, title, content, content_type, author_id, status, created_at, updated_at
            FROM contents
            WHERE id = $1
            "#,
            content_id
        )
        .fetch_optional(&self.pool)
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

    pub async fn update_content(&self, content_id: Uuid, updates: ContentUpdates) -> Result<Content, sqlx::Error> {
        let content = sqlx::query_as!(
            Content,
            r#"
            UPDATE contents
            SET title = COALESCE($2, title),
                content = COALESCE($3, content),
                content_type = COALESCE($4, content_type),
                status = COALESCE($5, status),
                updated_at = $6
            WHERE id = $1
            RETURNING id, title, content, content_type, author_id, status, created_at, updated_at
            "#,
            content_id,
            updates.title,
            updates.content,
            updates.content_type,
            updates.status,
            Utc::now()
        )
        .fetch_one(&self.pool)
        .await?;

        Ok(content)
    }
}

#[derive(Debug, Deserialize)]
pub struct ContentUpdates {
    pub title: Option<String>,
    pub content: Option<String>,
    pub content_type: Option<String>,
    pub status: Option<String>,
}
```

### 2.3 搜索服务实现

```rust
// src/services/search/search_service.rs
use actix_web::{web, HttpResponse, Result};
use serde::{Deserialize, Serialize};
use sqlx::PgPool;
use uuid::Uuid;
use elasticsearch::{Elasticsearch, SearchParts};
use serde_json::json;

#[derive(Debug, Serialize, Deserialize)]
pub struct SearchResult {
    pub id: Uuid,
    pub title: String,
    pub content: String,
    pub content_type: String,
    pub score: f64,
    pub highlights: Vec<String>,
}

#[derive(Debug, Deserialize)]
pub struct SearchRequest {
    pub query: String,
    pub content_type: Option<String>,
    pub page: Option<i32>,
    pub size: Option<i32>,
}

pub struct SearchService {
    pool: PgPool,
    elasticsearch: Elasticsearch,
}

impl SearchService {
    pub fn new(pool: PgPool, elasticsearch: Elasticsearch) -> Self {
        Self { pool, elasticsearch }
    }

    pub async fn search(&self, request: SearchRequest) -> Result<Vec<SearchResult>, Box<dyn std::error::Error>> {
        let page = request.page.unwrap_or(1);
        let size = request.size.unwrap_or(10);
        let from = (page - 1) * size;

        let search_body = json!({
            "query": {
                "bool": {
                    "must": [
                        {
                            "multi_match": {
                                "query": request.query,
                                "fields": ["title^2", "content"],
                                "type": "best_fields"
                            }
                        }
                    ],
                    "filter": request.content_type.map(|ct| json!({
                        "term": { "content_type": ct }
                    }))
                }
            },
            "highlight": {
                "fields": {
                    "title": {},
                    "content": {
                        "fragment_size": 150,
                        "number_of_fragments": 3
                    }
                }
            },
            "from": from,
            "size": size
        });

        let response = self.elasticsearch
            .search(SearchParts::Index(&["contents"]))
            .body(search_body)
            .send()
            .await?;

        let search_response: serde_json::Value = response.json().await?;
        
        // 解析搜索结果
        let hits = search_response["hits"]["hits"].as_array().unwrap_or(&vec![]);
        let mut results = Vec::new();

        for hit in hits {
            let source = &hit["_source"];
            let highlights = hit["highlight"].as_object()
                .map(|h| {
                    h.values()
                        .flat_map(|v| v.as_array().unwrap_or(&vec![]))
                        .filter_map(|v| v.as_str())
                        .map(|s| s.to_string())
                        .collect()
                })
                .unwrap_or_else(Vec::new);

            let result = SearchResult {
                id: Uuid::parse_str(hit["_id"].as_str().unwrap_or("")).unwrap_or_default(),
                title: source["title"].as_str().unwrap_or("").to_string(),
                content: source["content"].as_str().unwrap_or("").to_string(),
                content_type: source["content_type"].as_str().unwrap_or("").to_string(),
                score: hit["_score"].as_f64().unwrap_or(0.0),
                highlights,
            };

            results.push(result);
        }

        Ok(results)
    }

    pub async fn index_content(&self, content: &Content) -> Result<(), Box<dyn std::error::Error>> {
        let document = json!({
            "id": content.id.to_string(),
            "title": content.title,
            "content": content.content,
            "content_type": content.content_type,
            "author_id": content.author_id.to_string(),
            "created_at": content.created_at.to_rfc3339(),
            "updated_at": content.updated_at.to_rfc3339(),
        });

        self.elasticsearch
            .index(elasticsearch::IndexParts::IndexId("contents", &content.id.to_string()))
            .body(document)
            .send()
            .await?;

        Ok(())
    }
}
```

## 3. 数据库初始化脚本 / Database Initialization Scripts

### 3.1 PostgreSQL数据库初始化

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

### 3.2 Redis缓存配置

```bash
#!/bin/bash
# Redis缓存配置脚本
# Redis Cache Configuration Script

echo "🔧 配置Redis缓存..."
echo "🔧 Configuring Redis cache..."

# 创建Redis配置文件
cat > redis.conf << 'EOF'
# Redis配置文件
# Redis Configuration File

# 基本配置
port 6379
bind 0.0.0.0
timeout 300
tcp-keepalive 60

# 内存配置
maxmemory 256mb
maxmemory-policy allkeys-lru

# 持久化配置
save 900 1
save 300 10
save 60 10000

# 日志配置
loglevel notice
logfile ""

# 安全配置
requirepass web3semantics2024

# 性能优化
tcp-backlog 511
databases 16
EOF

echo "✅ Redis缓存配置完成"
echo "✅ Redis cache configuration completed"
```

## 4. API路由配置脚本 / API Route Configuration Scripts

### 4.1 主应用路由配置

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

### 4.2 用户控制器配置

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

async fn update_user(
    pool: web::Data<PgPool>,
    path: web::Path<uuid::Uuid>,
    request: web::Json<UserUpdates>,
) -> Result<HttpResponse> {
    let user_service = UserService::new(pool.get_ref().clone());
    
    match user_service.update_user(path.into_inner(), request.into_inner()).await {
        Ok(user) => Ok(HttpResponse::Ok().json(user)),
        Err(e) => Ok(HttpResponse::InternalServerError().body(e.to_string())),
    }
}

async fn delete_user(
    pool: web::Data<PgPool>,
    path: web::Path<uuid::Uuid>,
) -> Result<HttpResponse> {
    let user_service = UserService::new(pool.get_ref().clone());
    
    match user_service.delete_user(path.into_inner()).await {
        Ok(_) => Ok(HttpResponse::NoContent().finish()),
        Err(e) => Ok(HttpResponse::InternalServerError().body(e.to_string())),
    }
}
```

## 5. 前端组件实现脚本 / Frontend Component Implementation Scripts

### 5.1 主应用组件

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

### 5.2 知识图谱可视化组件

```typescript
// src/components/KnowledgeGraph.tsx
import React, { useEffect, useRef } from 'react';
import * as d3 from 'd3';

interface Node {
  id: string;
  name: string;
  type: string;
  x?: number;
  y?: number;
}

interface Link {
  source: string;
  target: string;
  type: string;
}

interface KnowledgeGraphProps {
  nodes: Node[];
  links: Link[];
  width?: number;
  height?: number;
}

const KnowledgeGraph: React.FC<KnowledgeGraphProps> = ({
  nodes,
  links,
  width = 800,
  height = 600,
}) => {
  const svgRef = useRef<SVGSVGElement>(null);

  useEffect(() => {
    if (!svgRef.current) return;

    const svg = d3.select(svgRef.current);
    svg.selectAll("*").remove();

    const g = svg.append("g");

    // 创建力导向图
    const simulation = d3.forceSimulation(nodes)
      .force("link", d3.forceLink(links).id((d: any) => d.id))
      .force("charge", d3.forceManyBody().strength(-300))
      .force("center", d3.forceCenter(width / 2, height / 2));

    // 绘制连接线
    const link = g.append("g")
      .selectAll("line")
      .data(links)
      .enter().append("line")
      .attr("stroke", "#999")
      .attr("stroke-opacity", 0.6)
      .attr("stroke-width", 2);

    // 绘制节点
    const node = g.append("g")
      .selectAll("circle")
      .data(nodes)
      .enter().append("circle")
      .attr("r", 8)
      .attr("fill", (d) => {
        const colors = {
          concept: "#1976d2",
          technology: "#dc004e",
          protocol: "#388e3c",
          application: "#f57c00",
        };
        return colors[d.type as keyof typeof colors] || "#999";
      })
      .call(d3.drag()
        .on("start", dragstarted)
        .on("drag", dragged)
        .on("end", dragended));

    // 添加节点标签
    const label = g.append("g")
      .selectAll("text")
      .data(nodes)
      .enter().append("text")
      .text((d) => d.name)
      .attr("font-size", "12px")
      .attr("fill", "#fff")
      .attr("text-anchor", "middle")
      .attr("dy", "0.35em");

    // 更新位置
    simulation.on("tick", () => {
      link
        .attr("x1", (d: any) => d.source.x)
        .attr("y1", (d: any) => d.source.y)
        .attr("x2", (d: any) => d.target.x)
        .attr("y2", (d: any) => d.target.y);

      node
        .attr("cx", (d: any) => d.x)
        .attr("cy", (d: any) => d.y);

      label
        .attr("x", (d: any) => d.x)
        .attr("y", (d: any) => d.y);
    });

    function dragstarted(event: any, d: any) {
      if (!event.active) simulation.alphaTarget(0.3).restart();
      d.fx = d.x;
      d.fy = d.y;
    }

    function dragged(event: any, d: any) {
      d.fx = event.x;
      d.fy = event.y;
    }

    function dragended(event: any, d: any) {
      if (!event.active) simulation.alphaTarget(0);
      d.fx = null;
      d.fy = null;
    }

    return () => {
      simulation.stop();
    };
  }, [nodes, links, width, height]);

  return (
    <svg
      ref={svgRef}
      width={width}
      height={height}
      style={{ border: "1px solid #333" }}
    />
  );
};

export default KnowledgeGraph;
```

## 6. 部署脚本 / Deployment Scripts

### 6.1 Docker部署脚本

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

### 6.2 Kubernetes部署脚本

```yaml
# k8s-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web3-semantics-api
spec:
  replicas: 3
  selector:
    matchLabels:
      app: web3-semantics-api
  template:
    metadata:
      labels:
        app: web3-semantics-api
    spec:
      containers:
      - name: api
        image: web3-semantics-api:latest
        ports:
        - containerPort: 8080
        env:
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: web3-semantics-secrets
              key: database-url
        - name: ELASTICSEARCH_URL
          value: "http://elasticsearch:9200"
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
            cpu: "500m"
---
apiVersion: v1
kind: Service
metadata:
  name: web3-semantics-api-service
spec:
  selector:
    app: web3-semantics-api
  ports:
  - protocol: TCP
    port: 80
    targetPort: 8080
  type: LoadBalancer
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web3-semantics-ui
spec:
  replicas: 2
  selector:
    matchLabels:
      app: web3-semantics-ui
  template:
    metadata:
      labels:
        app: web3-semantics-ui
    spec:
      containers:
      - name: ui
        image: web3-semantics-ui:latest
        ports:
        - containerPort: 3000
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "256Mi"
            cpu: "200m"
---
apiVersion: v1
kind: Service
metadata:
  name: web3-semantics-ui-service
spec:
  selector:
    app: web3-semantics-ui
  ports:
  - protocol: TCP
    port: 80
    targetPort: 3000
  type: LoadBalancer
```

## 7. 监控和日志脚本 / Monitoring and Logging Scripts

### 7.1 Prometheus监控配置

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

  - job_name: 'elasticsearch'
    static_configs:
      - targets: ['elasticsearch:9200']
```

### 7.2 Grafana仪表板配置

```json
{
  "dashboard": {
    "title": "Web3 Semantics Platform Dashboard",
    "panels": [
      {
        "title": "API Request Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(http_requests_total[5m])",
            "legendFormat": "{{method}} {{endpoint}}"
          }
        ]
      },
      {
        "title": "Database Connections",
        "type": "graph",
        "targets": [
          {
            "expr": "pg_stat_database_numbackends",
            "legendFormat": "{{datname}}"
          }
        ]
      },
      {
        "title": "Cache Hit Rate",
        "type": "singlestat",
        "targets": [
          {
            "expr": "rate(redis_keyspace_hits_total[5m]) / (rate(redis_keyspace_hits_total[5m]) + rate(redis_keyspace_misses_total[5m])) * 100"
          }
        ]
      }
    ]
  }
}
```

## 8. 总结 / Summary

本实施脚本提供了完整的Web3语义知识系统技术平台开发工具，包括：

1. **环境搭建脚本**: 自动化开发环境配置
2. **核心服务实现**: 用户、内容、搜索服务
3. **数据库初始化**: PostgreSQL和Redis配置
4. **API路由配置**: RESTful API实现
5. **前端组件**: React组件和可视化
6. **部署脚本**: Docker和Kubernetes部署
7. **监控配置**: Prometheus和Grafana

These implementation scripts provide complete development tools for the Web3 semantics knowledge system technical platform, including:

1. **Environment Setup Scripts**: Automated development environment configuration
2. **Core Service Implementation**: User, content, search services
3. **Database Initialization**: PostgreSQL and Redis configuration
4. **API Route Configuration**: RESTful API implementation
5. **Frontend Components**: React components and visualization
6. **Deployment Scripts**: Docker and Kubernetes deployment
7. **Monitoring Configuration**: Prometheus and Grafana

通过这些脚本，我们可以快速启动和推进Web3语义知识系统技术平台的开发工作。

Through these scripts, we can quickly start and advance the development work of the Web3 semantics knowledge system technical platform.
