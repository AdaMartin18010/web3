use actix_web::{web, HttpResponse, Result};

pub fn configure(cfg: &mut web::ServiceConfig) {
    cfg.service(
        web::scope("/analytics")
            .route("", web::get().to(get_analytics))
            .route("/learning", web::get().to(get_learning_analytics))
            .route("/usage", web::get().to(get_usage_analytics))
    );
}

async fn get_analytics() -> Result<HttpResponse> {
    Ok(HttpResponse::Ok().json(serde_json::json!({
        "message": "Analytics endpoint - to be implemented"
    })))
}

async fn get_learning_analytics() -> Result<HttpResponse> {
    Ok(HttpResponse::Ok().json(serde_json::json!({
        "message": "Learning analytics endpoint - to be implemented"
    })))
}

async fn get_usage_analytics() -> Result<HttpResponse> {
    Ok(HttpResponse::Ok().json(serde_json::json!({
        "message": "Usage analytics endpoint - to be implemented"
    })))
} 