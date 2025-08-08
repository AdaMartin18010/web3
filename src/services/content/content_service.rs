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
    pub tags: Vec<String>,
    pub metadata: serde_json::Value,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Deserialize)]
pub struct CreateContentRequest {
    pub title: String,
    pub content: String,
    pub content_type: String,
    pub author_id: Uuid,
    pub tags: Option<Vec<String>>,
    pub metadata: Option<serde_json::Value>,
}

#[derive(Debug, Deserialize)]
pub struct ContentUpdates {
    pub title: Option<String>,
    pub content: Option<String>,
    pub content_type: Option<String>,
    pub status: Option<String>,
    pub tags: Option<Vec<String>>,
    pub metadata: Option<serde_json::Value>,
}

#[derive(Debug, Deserialize)]
pub struct ContentSearchRequest {
    pub query: String,
    pub content_type: Option<String>,
    pub author_id: Option<Uuid>,
    pub status: Option<String>,
    pub tags: Option<Vec<String>>,
    pub page: Option<i32>,
    pub size: Option<i32>,
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
        let tags = request.tags.unwrap_or_else(Vec::new);
        let metadata = request.metadata.unwrap_or_else(|| serde_json::json!({}));
        
        let content = sqlx::query_as!(
            Content,
            r#"
            INSERT INTO contents (id, title, content, content_type, author_id, status, tags, metadata, created_at, updated_at)
            VALUES ($1, $2, $3, $4, $5, 'draft', $6, $7, $8, $8)
            RETURNING id, title, content, content_type, author_id, status, tags, metadata, created_at, updated_at
            "#,
            content_id,
            request.title,
            request.content,
            request.content_type,
            request.author_id,
            &tags,
            metadata,
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
            SELECT id, title, content, content_type, author_id, status, tags, metadata, created_at, updated_at
            FROM contents
            WHERE id = $1
            "#,
            content_id
        )
        .fetch_optional(&self.pool)
        .await?;

        Ok(content)
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
                tags = COALESCE($6, tags),
                metadata = COALESCE($7, metadata),
                updated_at = $8
            WHERE id = $1
            RETURNING id, title, content, content_type, author_id, status, tags, metadata, created_at, updated_at
            "#,
            content_id,
            updates.title,
            updates.content,
            updates.content_type,
            updates.status,
            updates.tags.as_ref(),
            updates.metadata,
            Utc::now()
        )
        .fetch_one(&self.pool)
        .await?;

        Ok(content)
    }

    pub async fn delete_content(&self, content_id: Uuid) -> Result<(), sqlx::Error> {
        sqlx::query!(
            r#"
            DELETE FROM contents
            WHERE id = $1
            "#,
            content_id
        )
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    pub async fn search_contents(&self, request: ContentSearchRequest) -> Result<Vec<Content>, sqlx::Error> {
        let page = request.page.unwrap_or(1);
        let size = request.size.unwrap_or(20);
        let offset = (page - 1) * size;

        let mut query = String::from(
            r#"
            SELECT id, title, content, content_type, author_id, status, tags, metadata, created_at, updated_at
            FROM contents
            WHERE 1=1
            "#
        );

        let mut params: Vec<Box<dyn sqlx::Encode<'_, sqlx::Postgres> + Send + Sync>> = Vec::new();
        let mut param_count = 0;

        if !request.query.is_empty() {
            param_count += 1;
            query.push_str(&format!(" AND (title ILIKE ${} OR content ILIKE ${})", param_count, param_count));
            params.push(Box::new(format!("%{}%", request.query)));
        }

        if let Some(content_type) = request.content_type {
            param_count += 1;
            query.push_str(&format!(" AND content_type = ${}", param_count));
            params.push(Box::new(content_type));
        }

        if let Some(author_id) = request.author_id {
            param_count += 1;
            query.push_str(&format!(" AND author_id = ${}", param_count));
            params.push(Box::new(author_id));
        }

        if let Some(status) = request.status {
            param_count += 1;
            query.push_str(&format!(" AND status = ${}", param_count));
            params.push(Box::new(status));
        }

        if let Some(tags) = request.tags {
            param_count += 1;
            query.push_str(&format!(" AND tags && ${}", param_count));
            params.push(Box::new(tags));
        }

        query.push_str(" ORDER BY created_at DESC");
        query.push_str(&format!(" LIMIT {} OFFSET {}", size, offset));

        // 执行查询
        let mut query_builder = sqlx::query_as::<_, Content>(&query);
        for param in params {
            query_builder = query_builder.bind(param);
        }

        let contents = query_builder.fetch_all(&self.pool).await?;

        Ok(contents)
    }

    pub async fn get_contents_by_author(&self, author_id: Uuid, limit: Option<i64>, offset: Option<i64>) -> Result<Vec<Content>, sqlx::Error> {
        let limit = limit.unwrap_or(50);
        let offset = offset.unwrap_or(0);

        let contents = sqlx::query_as!(
            Content,
            r#"
            SELECT id, title, content, content_type, author_id, status, tags, metadata, created_at, updated_at
            FROM contents
            WHERE author_id = $1
            ORDER BY created_at DESC
            LIMIT $2 OFFSET $3
            "#,
            author_id,
            limit,
            offset
        )
        .fetch_all(&self.pool)
        .await?;

        Ok(contents)
    }

    pub async fn publish_content(&self, content_id: Uuid) -> Result<Content, sqlx::Error> {
        let content = sqlx::query_as!(
            Content,
            r#"
            UPDATE contents
            SET status = 'published', updated_at = $2
            WHERE id = $1
            RETURNING id, title, content, content_type, author_id, status, tags, metadata, created_at, updated_at
            "#,
            content_id,
            Utc::now()
        )
        .fetch_one(&self.pool)
        .await?;

        Ok(content)
    }

    pub async fn get_content_statistics(&self) -> Result<serde_json::Value, sqlx::Error> {
        let total_count = sqlx::query!(
            r#"
            SELECT COUNT(*) as count
            FROM contents
            "#
        )
        .fetch_one(&self.pool)
        .await?;

        let published_count = sqlx::query!(
            r#"
            SELECT COUNT(*) as count
            FROM contents
            WHERE status = 'published'
            "#
        )
        .fetch_one(&self.pool)
        .await?;

        let draft_count = sqlx::query!(
            r#"
            SELECT COUNT(*) as count
            FROM contents
            WHERE status = 'draft'
            "#
        )
        .fetch_one(&self.pool)
        .await?;

        let stats = serde_json::json!({
            "total": total_count.count,
            "published": published_count.count,
            "draft": draft_count.count,
        });

        Ok(stats)
    }
} 