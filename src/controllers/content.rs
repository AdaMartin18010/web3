use actix_web::{web, HttpResponse, Result};
use crate::services::content::{ContentService, CreateContentRequest, ContentUpdates, ContentSearchRequest};
use sqlx::PgPool;
use uuid::Uuid;

pub fn configure(cfg: &mut web::ServiceConfig) {
    cfg.service(
        web::scope("/contents")
            .route("", web::post().to(create_content))
            .route("", web::get().to(search_contents))
            .route("/{id}", web::get().to(get_content))
            .route("/{id}", web::put().to(update_content))
            .route("/{id}", web::delete().to(delete_content))
            .route("/{id}/publish", web::post().to(publish_content))
            .route("/author/{author_id}", web::get().to(get_contents_by_author))
            .route("/statistics", web::get().to(get_content_statistics))
    );
}

async fn create_content(
    pool: web::Data<PgPool>,
    request: web::Json<CreateContentRequest>,
) -> Result<HttpResponse> {
    let content_service = ContentService::new(pool.get_ref().clone());
    
    match content_service.create_content(request.into_inner()).await {
        Ok(content) => {
            log::info!("Content created successfully: {}", content.title);
            Ok(HttpResponse::Created().json(content))
        }
        Err(e) => {
            log::error!("Failed to create content: {}", e);
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": "Failed to create content",
                "message": e.to_string()
            })))
        }
    }
}

async fn get_content(
    pool: web::Data<PgPool>,
    path: web::Path<Uuid>,
) -> Result<HttpResponse> {
    let content_service = ContentService::new(pool.get_ref().clone());
    
    match content_service.get_content_by_id(path.into_inner()).await {
        Ok(Some(content)) => {
            log::info!("Content retrieved successfully: {}", content.title);
            Ok(HttpResponse::Ok().json(content))
        }
        Ok(None) => {
            log::warn!("Content not found");
            Ok(HttpResponse::NotFound().json(serde_json::json!({
                "error": "Content not found"
            })))
        }
        Err(e) => {
            log::error!("Failed to get content: {}", e);
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": "Failed to get content",
                "message": e.to_string()
            })))
        }
    }
}

async fn update_content(
    pool: web::Data<PgPool>,
    path: web::Path<Uuid>,
    request: web::Json<ContentUpdates>,
) -> Result<HttpResponse> {
    let content_service = ContentService::new(pool.get_ref().clone());
    
    match content_service.update_content(path.into_inner(), request.into_inner()).await {
        Ok(content) => {
            log::info!("Content updated successfully: {}", content.title);
            Ok(HttpResponse::Ok().json(content))
        }
        Err(e) => {
            log::error!("Failed to update content: {}", e);
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": "Failed to update content",
                "message": e.to_string()
            })))
        }
    }
}

async fn delete_content(
    pool: web::Data<PgPool>,
    path: web::Path<Uuid>,
) -> Result<HttpResponse> {
    let content_service = ContentService::new(pool.get_ref().clone());
    
    match content_service.delete_content(path.into_inner()).await {
        Ok(_) => {
            log::info!("Content deleted successfully");
            Ok(HttpResponse::NoContent().finish())
        }
        Err(e) => {
            log::error!("Failed to delete content: {}", e);
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": "Failed to delete content",
                "message": e.to_string()
            })))
        }
    }
}

async fn search_contents(
    pool: web::Data<PgPool>,
    query: web::Query<std::collections::HashMap<String, String>>,
) -> Result<HttpResponse> {
    let content_service = ContentService::new(pool.get_ref().clone());
    
    let search_request = ContentSearchRequest {
        query: query.get("q").unwrap_or(&String::new()).clone(),
        content_type: query.get("type").cloned(),
        author_id: query.get("author_id").and_then(|s| s.parse::<Uuid>().ok()),
        status: query.get("status").cloned(),
        tags: query.get("tags").map(|s| s.split(',').map(|t| t.trim().to_string()).collect()),
        page: query.get("page").and_then(|s| s.parse::<i32>().ok()),
        size: query.get("size").and_then(|s| s.parse::<i32>().ok()),
    };
    
    match content_service.search_contents(search_request).await {
        Ok(contents) => {
            log::info!("Retrieved {} contents", contents.len());
            Ok(HttpResponse::Ok().json(contents))
        }
        Err(e) => {
            log::error!("Failed to search contents: {}", e);
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": "Failed to search contents",
                "message": e.to_string()
            })))
        }
    }
}

async fn publish_content(
    pool: web::Data<PgPool>,
    path: web::Path<Uuid>,
) -> Result<HttpResponse> {
    let content_service = ContentService::new(pool.get_ref().clone());
    
    match content_service.publish_content(path.into_inner()).await {
        Ok(content) => {
            log::info!("Content published successfully: {}", content.title);
            Ok(HttpResponse::Ok().json(content))
        }
        Err(e) => {
            log::error!("Failed to publish content: {}", e);
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": "Failed to publish content",
                "message": e.to_string()
            })))
        }
    }
}

async fn get_contents_by_author(
    pool: web::Data<PgPool>,
    path: web::Path<Uuid>,
    query: web::Query<std::collections::HashMap<String, String>>,
) -> Result<HttpResponse> {
    let content_service = ContentService::new(pool.get_ref().clone());
    
    let limit = query.get("limit").and_then(|s| s.parse::<i64>().ok());
    let offset = query.get("offset").and_then(|s| s.parse::<i64>().ok());
    
    match content_service.get_contents_by_author(path.into_inner(), limit, offset).await {
        Ok(contents) => {
            log::info!("Retrieved {} contents for author", contents.len());
            Ok(HttpResponse::Ok().json(contents))
        }
        Err(e) => {
            log::error!("Failed to get contents by author: {}", e);
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": "Failed to get contents by author",
                "message": e.to_string()
            })))
        }
    }
}

async fn get_content_statistics(
    pool: web::Data<PgPool>,
) -> Result<HttpResponse> {
    let content_service = ContentService::new(pool.get_ref().clone());
    
    match content_service.get_content_statistics().await {
        Ok(stats) => {
            log::info!("Retrieved content statistics");
            Ok(HttpResponse::Ok().json(stats))
        }
        Err(e) => {
            log::error!("Failed to get content statistics: {}", e);
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": "Failed to get content statistics",
                "message": e.to_string()
            })))
        }
    }
} 