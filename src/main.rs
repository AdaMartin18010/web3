use actix_web::{web, App, HttpServer, middleware};
use sqlx::PgPool;
use elasticsearch::Elasticsearch;
use std::env;

mod services;
mod controllers;
mod models;
mod middleware;
mod utils;

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    // 初始化日志
    env_logger::init_from_env(env_logger::Env::new().default_filter_or("info"));

    // 加载环境变量
    dotenv::dotenv().ok();

    // 数据库连接
    let database_url = env::var("DATABASE_URL")
        .unwrap_or_else(|_| "postgres://admin:password@localhost:5432/web3_semantics".to_string());
    
    let pool = PgPool::connect(&database_url)
        .await
        .expect("Failed to connect to database");

    // Elasticsearch连接
    let elasticsearch_url = env::var("ELASTICSEARCH_URL")
        .unwrap_or_else(|_| "http://localhost:9200".to_string());
    
    let elasticsearch = Elasticsearch::new(
        elasticsearch::http::transport::SingleNodeConnection::new(elasticsearch_url)
            .expect("Failed to connect to Elasticsearch")
    );

    println!("🚀 Starting Web3 Semantics Knowledge System API Server...");
    println!("📊 Database: {}", database_url);
    println!("🔍 Elasticsearch: {}", elasticsearch_url);

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
            .service(
                web::scope("/health")
                    .route("", web::get().to(health_check))
            )
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}

async fn health_check() -> actix_web::HttpResponse {
    actix_web::HttpResponse::Ok().json(serde_json::json!({
        "status": "healthy",
        "service": "web3-semantics-api",
        "version": "0.1.0"
    }))
} 