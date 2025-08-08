use actix_web::{web, HttpResponse, Result};
use crate::services::user::{UserService, CreateUserRequest, UserUpdates, LoginRequest};
use sqlx::PgPool;
use uuid::Uuid;

pub fn configure(cfg: &mut web::ServiceConfig) {
    cfg.service(
        web::scope("/users")
            .route("", web::post().to(create_user))
            .route("", web::get().to(list_users))
            .route("/{id}", web::get().to(get_user))
            .route("/{id}", web::put().to(update_user))
            .route("/{id}", web::delete().to(delete_user))
            .route("/login", web::post().to(login_user))
    );
}

async fn create_user(
    pool: web::Data<PgPool>,
    request: web::Json<CreateUserRequest>,
) -> Result<HttpResponse> {
    let user_service = UserService::new(pool.get_ref().clone());
    
    match user_service.create_user(request.into_inner()).await {
        Ok(user) => {
            log::info!("User created successfully: {}", user.username);
            Ok(HttpResponse::Created().json(user))
        }
        Err(e) => {
            log::error!("Failed to create user: {}", e);
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": "Failed to create user",
                "message": e.to_string()
            })))
        }
    }
}

async fn get_user(
    pool: web::Data<PgPool>,
    path: web::Path<Uuid>,
) -> Result<HttpResponse> {
    let user_service = UserService::new(pool.get_ref().clone());
    
    match user_service.get_user_by_id(path.into_inner()).await {
        Ok(Some(user)) => {
            log::info!("User retrieved successfully: {}", user.username);
            Ok(HttpResponse::Ok().json(user))
        }
        Ok(None) => {
            log::warn!("User not found");
            Ok(HttpResponse::NotFound().json(serde_json::json!({
                "error": "User not found"
            })))
        }
        Err(e) => {
            log::error!("Failed to get user: {}", e);
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": "Failed to get user",
                "message": e.to_string()
            })))
        }
    }
}

async fn update_user(
    pool: web::Data<PgPool>,
    path: web::Path<Uuid>,
    request: web::Json<UserUpdates>,
) -> Result<HttpResponse> {
    let user_service = UserService::new(pool.get_ref().clone());
    
    match user_service.update_user(path.into_inner(), request.into_inner()).await {
        Ok(user) => {
            log::info!("User updated successfully: {}", user.username);
            Ok(HttpResponse::Ok().json(user))
        }
        Err(e) => {
            log::error!("Failed to update user: {}", e);
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": "Failed to update user",
                "message": e.to_string()
            })))
        }
    }
}

async fn delete_user(
    pool: web::Data<PgPool>,
    path: web::Path<Uuid>,
) -> Result<HttpResponse> {
    let user_service = UserService::new(pool.get_ref().clone());
    
    match user_service.delete_user(path.into_inner()).await {
        Ok(_) => {
            log::info!("User deleted successfully");
            Ok(HttpResponse::NoContent().finish())
        }
        Err(e) => {
            log::error!("Failed to delete user: {}", e);
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": "Failed to delete user",
                "message": e.to_string()
            })))
        }
    }
}

async fn list_users(
    pool: web::Data<PgPool>,
    query: web::Query<std::collections::HashMap<String, String>>,
) -> Result<HttpResponse> {
    let user_service = UserService::new(pool.get_ref().clone());
    
    let limit = query.get("limit").and_then(|s| s.parse::<i64>().ok());
    let offset = query.get("offset").and_then(|s| s.parse::<i64>().ok());
    
    match user_service.list_users(limit, offset).await {
        Ok(users) => {
            log::info!("Retrieved {} users", users.len());
            Ok(HttpResponse::Ok().json(users))
        }
        Err(e) => {
            log::error!("Failed to list users: {}", e);
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": "Failed to list users",
                "message": e.to_string()
            })))
        }
    }
}

async fn login_user(
    pool: web::Data<PgPool>,
    request: web::Json<LoginRequest>,
) -> Result<HttpResponse> {
    let user_service = UserService::new(pool.get_ref().clone());
    let login_request = request.into_inner();
    
    match user_service.verify_password(&login_request.username, &login_request.password).await {
        Ok(true) => {
            // 在实际应用中，这里应该生成JWT token
            log::info!("User login successful: {}", login_request.username);
            Ok(HttpResponse::Ok().json(serde_json::json!({
                "message": "Login successful",
                "username": login_request.username
            })))
        }
        Ok(false) => {
            log::warn!("Login failed for user: {}", login_request.username);
            Ok(HttpResponse::Unauthorized().json(serde_json::json!({
                "error": "Invalid credentials"
            })))
        }
        Err(e) => {
            log::error!("Login error: {}", e);
            Ok(HttpResponse::InternalServerError().json(serde_json::json!({
                "error": "Login failed",
                "message": e.to_string()
            })))
        }
    }
} 