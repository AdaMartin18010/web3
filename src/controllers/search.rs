use actix_web::{web, HttpResponse, Result};

pub fn configure(cfg: &mut web::ServiceConfig) {
    cfg.service(
        web::scope("/search")
            .route("", web::get().to(search))
            .route("/semantic", web::get().to(semantic_search))
            .route("/advanced", web::post().to(advanced_search))
    );
}

async fn search() -> Result<HttpResponse> {
    Ok(HttpResponse::Ok().json(serde_json::json!({
        "message": "Search endpoint - to be implemented"
    })))
}

async fn semantic_search() -> Result<HttpResponse> {
    Ok(HttpResponse::Ok().json(serde_json::json!({
        "message": "Semantic search endpoint - to be implemented"
    })))
}

async fn advanced_search() -> Result<HttpResponse> {
    Ok(HttpResponse::Ok().json(serde_json::json!({
        "message": "Advanced search endpoint - to be implemented"
    })))
} 