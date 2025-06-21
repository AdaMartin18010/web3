# 游戏开发行业架构最佳实践

## 目录

1. 行业概述与核心挑战
2. 技术栈选型与架构模式
3. ECS架构设计
4. 客户端-服务器架构
5. 状态同步与网络
6. 游戏引擎与渲染
7. 性能优化与调试

---

## 1. 行业概述与核心挑战

### 1.1 行业特点

游戏开发行业需要高性能、低延迟的实时系统，从游戏引擎到网络服务器都需要卓越的性能表现。

### 1.2 核心挑战

- **性能要求**: 60FPS渲染、低延迟网络
- **实时性**: 实时游戏逻辑、物理模拟
- **并发处理**: 多玩家同步、AI计算
- **资源管理**: 内存优化、资源加载
- **跨平台**: 多平台支持、移动端优化

---

## 2. 技术栈选型与架构模式

### 2.1 核心框架

```toml
[dependencies]
# 游戏引擎
bevy = "0.12"
amethyst = "0.20"
ggez = "0.9"

# 图形渲染
wgpu = "0.18"
vulkano = "0.34"
glium = "0.32"

# 音频
rodio = "0.17"
cpal = "0.15"
kira = "0.8"

# 物理引擎
rapier2d = "0.17"
rapier3d = "0.17"
nphysics3d = "0.16"

# 网络
tokio = { version = "1.35", features = ["full"] }
quinn = "0.10"
webrtc = "0.8"

# 序列化
serde = { version = "1.0", features = ["derive"] }
bincode = "1.3"
```

### 2.2 行业特定库

```toml
[dependencies]
# 数学库
glam = "0.25"
nalgebra = "0.32"
cgmath = "0.18"

# 资源管理
asset = "0.1"
notify = "6.1"

# 输入处理
winit = "0.29"
gilrs = "0.9"

# 调试和性能
tracy-client = "0.20"
perf-event = "0.4"
```

---

## 3. ECS架构设计

### 3.1 ECS核心概念

```rust
use bevy::prelude::*;

// 组件定义
#[derive(Component)]
pub struct Position {
    pub x: f32,
    pub y: f32,
}

#[derive(Component)]
pub struct Velocity {
    pub x: f32,
    pub y: f32,
}

#[derive(Component)]
pub struct Health {
    pub current: f32,
    pub maximum: f32,
}

#[derive(Component)]
pub struct Player {
    pub id: PlayerId,
    pub name: String,
}

#[derive(Component)]
pub struct Enemy {
    pub enemy_type: EnemyType,
    pub ai_state: AIState,
}

#[derive(Component)]
pub struct Collider {
    pub width: f32,
    pub height: f32,
    pub collider_type: ColliderType,
}

#[derive(Component)]
pub struct Sprite {
    pub texture_id: TextureId,
    pub width: f32,
    pub height: f32,
    pub animation: Option<Animation>,
}

// 系统定义
fn movement_system(
    mut query: Query<(&mut Position, &Velocity)>,
    time: Res<Time>,
) {
    for (mut position, velocity) in query.iter_mut() {
        position.x += velocity.x * time.delta_seconds();
        position.y += velocity.y * time.delta_seconds();
    }
}

fn health_system(
    mut query: Query<(&mut Health, Entity)>,
    mut commands: Commands,
) {
    for (mut health, entity) in query.iter_mut() {
        if health.current <= 0.0 {
            // 处理死亡逻辑
            commands.entity(entity).despawn();
        }
    }
}

fn collision_system(
    mut query: Query<(Entity, &Position, &Collider)>,
    mut collision_events: EventWriter<CollisionEvent>,
) {
    let entities: Vec<_> = query.iter().collect();
    
    for i in 0..entities.len() {
        for j in (i + 1)..entities.len() {
            let (entity_a, pos_a, collider_a) = entities[i];
            let (entity_b, pos_b, collider_b) = entities[j];
            
            if check_collision(pos_a, collider_a, pos_b, collider_b) {
                collision_events.send(CollisionEvent {
                    entity_a,
                    entity_b,
                });
            }
        }
    }
}

fn ai_system(
    mut query: Query<(&mut Enemy, &Position, &mut Velocity)>,
    player_query: Query<&Position, With<Player>>,
) {
    for (mut enemy, enemy_pos, mut enemy_vel) in query.iter_mut() {
        if let Ok(player_pos) = player_query.get_single() {
            // 简单的AI逻辑：朝向玩家移动
            let direction = (player_pos.x - enemy_pos.x, player_pos.y - enemy_pos.y);
            let distance = (direction.0 * direction.0 + direction.1 * direction.1).sqrt();
            
            if distance > 0.0 {
                enemy_vel.x = direction.0 / distance * 50.0; // 50 units per second
                enemy_vel.y = direction.1 / distance * 50.0;
            }
        }
    }
}

// 应用配置
fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_systems(Update, (
            movement_system,
            health_system,
            collision_system,
            ai_system,
        ))
        .run();
}
```

### 3.2 事件系统

```rust
#[derive(Event)]
pub struct CollisionEvent {
    pub entity_a: Entity,
    pub entity_b: Entity,
}

#[derive(Event)]
pub struct DamageEvent {
    pub target: Entity,
    pub damage: f32,
    pub source: Entity,
}

#[derive(Event)]
pub struct PlayerDeathEvent {
    pub player: Entity,
    pub killer: Option<Entity>,
}

fn collision_handler(
    mut collision_events: EventReader<CollisionEvent>,
    mut damage_events: EventWriter<DamageEvent>,
    player_query: Query<&Player>,
    enemy_query: Query<&Enemy>,
) {
    for event in collision_events.read() {
        let is_player_a = player_query.get(event.entity_a).is_ok();
        let is_player_b = player_query.get(event.entity_b).is_ok();
        let is_enemy_a = enemy_query.get(event.entity_a).is_ok();
        let is_enemy_b = enemy_query.get(event.entity_b).is_ok();
        
        // 玩家与敌人碰撞
        if (is_player_a && is_enemy_b) || (is_player_b && is_enemy_a) {
            let (player, enemy) = if is_player_a {
                (event.entity_a, event.entity_b)
            } else {
                (event.entity_b, event.entity_a)
            };
            
            damage_events.send(DamageEvent {
                target: player,
                damage: 10.0,
                source: enemy,
            });
        }
    }
}

fn damage_handler(
    mut damage_events: EventReader<DamageEvent>,
    mut health_query: Query<&mut Health>,
    mut player_death_events: EventWriter<PlayerDeathEvent>,
    player_query: Query<&Player>,
) {
    for event in damage_events.read() {
        if let Ok(mut health) = health_query.get_mut(event.target) {
            health.current -= event.damage;
            
            // 检查玩家死亡
            if health.current <= 0.0 && player_query.get(event.target).is_ok() {
                player_death_events.send(PlayerDeathEvent {
                    player: event.target,
                    killer: Some(event.source),
                });
            }
        }
    }
}
```

---

## 4. 客户端-服务器架构

### 4.1 客户端实现

```rust
pub struct GameClient {
    connection: Connection,
    game_state: GameState,
    input_handler: InputHandler,
    renderer: Renderer,
    prediction_engine: PredictionEngine,
}

impl GameClient {
    pub async fn run(&mut self) -> Result<(), GameError> {
        let mut last_update_time = Instant::now();
        
        loop {
            let current_time = Instant::now();
            let delta_time = current_time.duration_since(last_update_time);
            
            // 处理输入
            let input = self.input_handler.poll_input();
            
            // 本地预测
            if let Some(input) = input {
                self.prediction_engine.predict(input, delta_time);
            }
            
            // 发送输入到服务器
            if let Some(input) = input {
                self.connection.send_input(input).await?;
            }
            
            // 接收服务器更新
            if let Ok(update) = self.connection.receive_update().await {
                // 服务器权威更新
                self.game_state.apply_update(update);
                
                // 修正预测
                self.prediction_engine.reconcile(&self.game_state);
            }
            
            // 渲染
            self.renderer.render(&self.game_state);
            
            // 控制帧率
            let frame_time = Instant::now().duration_since(current_time);
            let target_frame_time = Duration::from_millis(16); // ~60 FPS
            
            if frame_time < target_frame_time {
                tokio::time::sleep(target_frame_time - frame_time).await;
            }
            
            last_update_time = current_time;
        }
    }
}

pub struct InputHandler {
    window: Window,
    gamepad: Option<Gamepad>,
}

impl InputHandler {
    pub fn poll_input(&mut self) -> Option<PlayerInput> {
        let mut input = PlayerInput::default();
        
        // 键盘输入
        if self.window.is_key_pressed(KeyCode::W) {
            input.forward = true;
        }
        if self.window.is_key_pressed(KeyCode::S) {
            input.backward = true;
        }
        if self.window.is_key_pressed(KeyCode::A) {
            input.left = true;
        }
        if self.window.is_key_pressed(KeyCode::D) {
            input.right = true;
        }
        if self.window.is_key_pressed(KeyCode::Space) {
            input.jump = true;
        }
        
        // 游戏手柄输入
        if let Some(gamepad) = &self.gamepad {
            input.forward = gamepad.left_stick_y > 0.5;
            input.backward = gamepad.left_stick_y < -0.5;
            input.left = gamepad.left_stick_x < -0.5;
            input.right = gamepad.left_stick_x > 0.5;
            input.jump = gamepad.button_a;
        }
        
        if input.is_any_pressed() {
            Some(input)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct PlayerInput {
    pub forward: bool,
    pub backward: bool,
    pub left: bool,
    pub right: bool,
    pub jump: bool,
    pub timestamp: u64,
}

impl PlayerInput {
    pub fn is_any_pressed(&self) -> bool {
        self.forward || self.backward || self.left || self.right || self.jump
    }
}
```

### 4.2 服务器实现

```rust
pub struct GameServer {
    clients: HashMap<ClientId, ClientConnection>,
    game_world: GameWorld,
    physics_engine: PhysicsEngine,
    tick_rate: u32,
    last_tick: Instant,
}

impl GameServer {
    pub async fn run(&mut self) -> Result<(), ServerError> {
        let tick_interval = Duration::from_millis(1000 / self.tick_rate as u64);
        
        loop {
            let current_time = Instant::now();
            
            // 处理客户端输入
            self.process_client_inputs().await?;
            
            // 更新游戏逻辑
            self.update_game_logic();
            
            // 物理模拟
            self.physics_engine.step(tick_interval);
            
            // 检测碰撞
            self.detect_collisions();
            
            // 发送状态更新给所有客户端
            self.broadcast_state_updates().await?;
            
            // 控制更新频率
            let elapsed = current_time.elapsed();
            if elapsed < tick_interval {
                tokio::time::sleep(tick_interval - elapsed).await;
            }
            
            self.last_tick = current_time;
        }
    }
    
    async fn process_client_inputs(&mut self) -> Result<(), ServerError> {
        for (client_id, connection) in &mut self.clients {
            while let Ok(input) = connection.receive_input().await {
                // 验证输入
                if self.validate_input(&input) {
                    // 应用输入到游戏世界
                    self.apply_input(*client_id, input);
                }
            }
        }
        Ok(())
    }
    
    fn update_game_logic(&mut self) {
        // 更新AI
        self.update_ai();
        
        // 更新游戏状态
        self.update_game_state();
        
        // 处理事件
        self.process_events();
    }
    
    fn update_ai(&mut self) {
        for entity in self.game_world.get_ai_entities() {
            if let Some(ai_component) = self.game_world.get_ai_component(entity) {
                let new_state = ai_component.update(&self.game_world);
                self.game_world.update_ai_state(entity, new_state);
            }
        }
    }
    
    async fn broadcast_state_updates(&mut self) -> Result<(), ServerError> {
        let game_state = self.game_world.get_state();
        
        for connection in self.clients.values_mut() {
            connection.send_state_update(&game_state).await?;
        }
        
        Ok(())
    }
}

pub struct GameWorld {
    entities: HashMap<EntityId, Entity>,
    spatial_index: SpatialIndex,
    event_queue: VecDeque<GameEvent>,
}

impl GameWorld {
    pub fn get_state(&self) -> GameState {
        GameState {
            entities: self.entities.clone(),
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_millis() as u64,
        }
    }
    
    pub fn apply_input(&mut self, client_id: ClientId, input: PlayerInput) {
        if let Some(player_entity) = self.get_player_entity(client_id) {
            if let Some(entity) = self.entities.get_mut(&player_entity) {
                // 更新玩家位置
                let movement = self.calculate_movement(&input);
                entity.position.x += movement.x;
                entity.position.y += movement.y;
                
                // 更新空间索引
                self.spatial_index.update_entity(player_entity, &entity.position);
            }
        }
    }
    
    fn calculate_movement(&self, input: &PlayerInput) -> Vector2<f32> {
        let mut movement = Vector2::new(0.0, 0.0);
        let speed = 100.0; // units per second
        
        if input.forward {
            movement.y += speed;
        }
        if input.backward {
            movement.y -= speed;
        }
        if input.left {
            movement.x -= speed;
        }
        if input.right {
            movement.x += speed;
        }
        
        movement
    }
}
```

---

## 5. 状态同步与网络

### 5.1 状态同步模式

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GameState {
    pub entities: HashMap<EntityId, Entity>,
    pub timestamp: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Entity {
    pub id: EntityId,
    pub entity_type: EntityType,
    pub position: Vector2<f32>,
    pub velocity: Vector2<f32>,
    pub health: f32,
    pub state: EntityState,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EntityType {
    Player,
    Enemy,
    Projectile,
    Item,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EntityState {
    Idle,
    Moving,
    Attacking,
    Dead,
}

// 增量状态更新
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateUpdate {
    pub timestamp: u64,
    pub entity_updates: HashMap<EntityId, EntityUpdate>,
    pub events: Vec<GameEvent>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EntityUpdate {
    Position(Vector2<f32>),
    Velocity(Vector2<f32>),
    Health(f32),
    State(EntityState),
    Full(Entity),
}

// 客户端预测
pub struct PredictionEngine {
    predicted_state: GameState,
    input_buffer: VecDeque<(PlayerInput, u64)>,
    reconciliation_buffer: VecDeque<GameState>,
}

impl PredictionEngine {
    pub fn predict(&mut self, input: PlayerInput, delta_time: Duration) {
        // 应用输入到预测状态
        self.apply_input_to_state(&mut self.predicted_state, input, delta_time);
        
        // 存储输入用于回滚
        self.input_buffer.push_back((input, self.predicted_state.timestamp));
        
        // 限制缓冲区大小
        if self.input_buffer.len() > 10 {
            self.input_buffer.pop_front();
        }
    }
    
    pub fn reconcile(&mut self, server_state: &GameState) {
        // 找到服务器状态对应的输入
        let mut input_index = 0;
        for (i, (_, timestamp)) in self.input_buffer.iter().enumerate() {
            if *timestamp >= server_state.timestamp {
                input_index = i;
                break;
            }
        }
        
        // 从服务器状态重新应用输入
        self.predicted_state = server_state.clone();
        
        for (input, _) in self.input_buffer.iter().skip(input_index) {
            self.apply_input_to_state(&mut self.predicted_state, input.clone(), Duration::from_millis(16));
        }
    }
    
    fn apply_input_to_state(&self, state: &mut GameState, input: PlayerInput, delta_time: Duration) {
        // 应用输入到游戏状态
        for entity in state.entities.values_mut() {
            if let EntityType::Player = entity.entity_type {
                let movement = self.calculate_movement(&input, delta_time);
                entity.position.x += movement.x;
                entity.position.y += movement.y;
                entity.velocity = movement;
            }
        }
    }
    
    fn calculate_movement(&self, input: &PlayerInput, delta_time: Duration) -> Vector2<f32> {
        let mut movement = Vector2::new(0.0, 0.0);
        let speed = 100.0;
        let dt = delta_time.as_secs_f32();
        
        if input.forward {
            movement.y += speed * dt;
        }
        if input.backward {
            movement.y -= speed * dt;
        }
        if input.left {
            movement.x -= speed * dt;
        }
        if input.right {
            movement.x += speed * dt;
        }
        
        movement
    }
}
```

### 5.2 网络协议

```rust
pub struct NetworkProtocol {
    compression: Compression,
    encryption: Encryption,
}

impl NetworkProtocol {
    pub fn serialize_state(&self, state: &GameState) -> Result<Vec<u8>, NetworkError> {
        // 序列化
        let serialized = bincode::serialize(state)?;
        
        // 压缩
        let compressed = self.compression.compress(&serialized)?;
        
        // 加密
        let encrypted = self.encryption.encrypt(&compressed)?;
        
        Ok(encrypted)
    }
    
    pub fn deserialize_state(&self, data: &[u8]) -> Result<GameState, NetworkError> {
        // 解密
        let decrypted = self.encryption.decrypt(data)?;
        
        // 解压
        let decompressed = self.compression.decompress(&decrypted)?;
        
        // 反序列化
        let state = bincode::deserialize(&decompressed)?;
        
        Ok(state)
    }
}

pub struct Compression;

impl Compression {
    pub fn compress(&self, data: &[u8]) -> Result<Vec<u8>, NetworkError> {
        // 使用LZ4压缩
        let mut compressed = Vec::new();
        lz4::block::compress_to_vec(data, Some(&mut compressed), true)?;
        Ok(compressed)
    }
    
    pub fn decompress(&self, data: &[u8]) -> Result<Vec<u8>, NetworkError> {
        // 使用LZ4解压
        let decompressed = lz4::block::decompress(data, None)?;
        Ok(decompressed)
    }
}

pub struct Encryption {
    key: [u8; 32],
}

impl Encryption {
    pub fn encrypt(&self, data: &[u8]) -> Result<Vec<u8>, NetworkError> {
        // 使用ChaCha20加密
        let mut encrypted = data.to_vec();
        let nonce = [0u8; 12];
        
        chacha20::ChaCha20::new(&self.key.into(), &nonce.into())
            .apply_keystream(&mut encrypted);
        
        Ok(encrypted)
    }
    
    pub fn decrypt(&self, data: &[u8]) -> Result<Vec<u8>, NetworkError> {
        // 使用ChaCha20解密
        let mut decrypted = data.to_vec();
        let nonce = [0u8; 12];
        
        chacha20::ChaCha20::new(&self.key.into(), &nonce.into())
            .apply_keystream(&mut decrypted);
        
        Ok(decrypted)
    }
}
```

---

## 6. 游戏引擎与渲染

### 6.1 渲染系统

```rust
pub struct Renderer {
    device: wgpu::Device,
    queue: wgpu::Queue,
    surface: wgpu::Surface,
    config: wgpu::SurfaceConfiguration,
    render_pipeline: wgpu::RenderPipeline,
    vertex_buffer: wgpu::Buffer,
    index_buffer: wgpu::Buffer,
    texture_bind_group: wgpu::BindGroup,
}

impl Renderer {
    pub async fn new(window: &Window) -> Result<Self, RenderError> {
        let size = window.inner_size();
        
        // 创建实例
        let instance = wgpu::Instance::new(wgpu::InstanceDescriptor {
            backends: wgpu::Backends::all(),
            ..Default::default()
        });
        
        // 创建表面
        let surface = unsafe { instance.create_surface(window) }?;
        
        // 选择适配器
        let adapter = instance
            .request_adapter(&wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::default(),
                compatible_surface: Some(&surface),
                force_fallback_adapter: false,
            })
            .await
            .ok_or(RenderError::NoAdapter)?;
        
        // 创建设备和队列
        let (device, queue) = adapter
            .request_device(
                &wgpu::DeviceDescriptor {
                    label: None,
                    features: wgpu::Features::empty(),
                    limits: wgpu::Limits::default(),
                },
                None,
            )
            .await?;
        
        // 配置表面
        let surface_caps = surface.get_capabilities(&adapter);
        let config = wgpu::SurfaceConfiguration {
            usage: wgpu::TextureUsages::RENDER_ATTACHMENT,
            format: surface_caps.formats[0],
            width: size.width,
            height: size.height,
            present_mode: wgpu::PresentMode::Fifo,
            alpha_mode: surface_caps.alpha_modes[0],
            view_formats: vec![],
        };
        surface.configure(&device, &config);
        
        // 创建渲染管线
        let render_pipeline = Self::create_render_pipeline(&device, &config);
        
        // 创建缓冲区
        let vertex_buffer = Self::create_vertex_buffer(&device);
        let index_buffer = Self::create_index_buffer(&device);
        
        // 创建纹理绑定组
        let texture_bind_group = Self::create_texture_bind_group(&device);
        
        Ok(Self {
            device,
            queue,
            surface,
            config,
            render_pipeline,
            vertex_buffer,
            index_buffer,
            texture_bind_group,
        })
    }
    
    pub fn render(&mut self, game_state: &GameState) -> Result<(), RenderError> {
        let frame = self.surface.get_current_texture()?;
        let view = frame.texture.create_view(&wgpu::TextureViewDescriptor::default());
        
        let mut encoder = self.device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
            label: Some("Render Encoder"),
        });
        
        {
            let mut render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                label: Some("Render Pass"),
                color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                    view: &view,
                    resolve_target: None,
                    ops: wgpu::Operations {
                        load: wgpu::LoadOp::Clear(wgpu::Color {
                            r: 0.1,
                            g: 0.2,
                            b: 0.3,
                            a: 1.0,
                        }),
                        store: true,
                    },
                })],
                depth_stencil_attachment: None,
            });
            
            render_pass.set_pipeline(&self.render_pipeline);
            render_pass.set_vertex_buffer(0, self.vertex_buffer.slice(..));
            render_pass.set_index_buffer(self.index_buffer.slice(..), wgpu::IndexFormat::Uint16);
            render_pass.set_bind_group(0, &self.texture_bind_group, &[]);
            
            // 渲染所有实体
            for entity in game_state.entities.values() {
                self.render_entity(&mut render_pass, entity);
            }
        }
        
        self.queue.submit(std::iter::once(encoder.finish()));
        frame.present();
        
        Ok(())
    }
    
    fn render_entity(&self, render_pass: &mut wgpu::RenderPass, entity: &Entity) {
        // 设置实体特定的uniform数据
        let transform = self.calculate_transform(entity);
        // 这里需要实现uniform缓冲区的更新和绑定
        
        // 绘制实体
        render_pass.draw_indexed(0..6, 0, 0..1);
    }
    
    fn calculate_transform(&self, entity: &Entity) -> Matrix4<f32> {
        Matrix4::from_translation(Vector3::new(entity.position.x, entity.position.y, 0.0))
    }
}
```

### 6.2 物理引擎集成

```rust
pub struct PhysicsEngine {
    rigid_body_set: RigidBodySet,
    collider_set: ColliderSet,
    island_manager: IslandManager,
    broad_phase: BroadPhase,
    narrow_phase: NarrowPhase,
    impulse_joint_set: ImpulseJointSet,
    multibody_joint_set: MultibodyJointSet,
    ccd_solver: CCDSolver,
    physics_hooks: (),
    event_handler: (),
}

impl PhysicsEngine {
    pub fn new() -> Self {
        Self {
            rigid_body_set: RigidBodySet::new(),
            collider_set: ColliderSet::new(),
            island_manager: IslandManager::new(),
            broad_phase: BroadPhase::new(),
            narrow_phase: NarrowPhase::new(),
            impulse_joint_set: ImpulseJointSet::new(),
            multibody_joint_set: MultibodyJointSet::new(),
            ccd_solver: CCDSolver::new(),
            physics_hooks: (),
            event_handler: (),
        }
    }
    
    pub fn step(&mut self, delta_time: Duration) {
        let gravity = Vector::y() * -9.81;
        let physics_pipeline = PhysicsPipeline::new(gravity);
        
        let physics_hooks = ();
        let event_handler = ();
        
        physics_pipeline.step(
            &gravity,
            IntegrationParameters::default(),
            &mut self.island_manager,
            &mut self.broad_phase,
            &mut self.narrow_phase,
            &mut self.rigid_body_set,
            &mut self.collider_set,
            &mut self.impulse_joint_set,
            &mut self.multibody_joint_set,
            &mut self.ccd_solver,
            &physics_hooks,
            &event_handler,
        );
    }
    
    pub fn add_rigid_body(&mut self, position: Vector2<f32>, body_type: RigidBodyType) -> RigidBodyHandle {
        let rigid_body = RigidBodyBuilder::new(body_type)
            .translation(position)
            .build();
        
        self.rigid_body_set.insert(rigid_body)
    }
    
    pub fn add_collider(&mut self, rigid_body: RigidBodyHandle, collider: Collider) -> ColliderHandle {
        self.collider_set.insert_with_parent(
            collider,
            rigid_body,
            &mut self.rigid_body_set,
        )
    }
    
    pub fn get_position(&self, rigid_body: RigidBodyHandle) -> Option<Vector2<f32>> {
        self.rigid_body_set
            .get(rigid_body)
            .map(|body| body.translation().xy())
    }
    
    pub fn set_position(&mut self, rigid_body: RigidBodyHandle, position: Vector2<f32>) {
        if let Some(body) = self.rigid_body_set.get_mut(rigid_body) {
            body.set_translation(position, true);
        }
    }
}
```

---

## 7. 性能优化与调试

### 7.1 性能监控

```rust
pub struct PerformanceMonitor {
    frame_times: VecDeque<Duration>,
    fps_counter: FPSCounter,
    memory_usage: MemoryUsage,
    cpu_usage: CPUUsage,
}

impl PerformanceMonitor {
    pub fn new() -> Self {
        Self {
            frame_times: VecDeque::with_capacity(60),
            fps_counter: FPSCounter::new(),
            memory_usage: MemoryUsage::new(),
            cpu_usage: CPUUsage::new(),
        }
    }
    
    pub fn record_frame(&mut self, frame_time: Duration) {
        self.frame_times.push_back(frame_time);
        
        // 保持最近60帧的数据
        if self.frame_times.len() > 60 {
            self.frame_times.pop_front();
        }
        
        self.fps_counter.record_frame(frame_time);
    }
    
    pub fn get_fps(&self) -> f32 {
        self.fps_counter.get_fps()
    }
    
    pub fn get_average_frame_time(&self) -> Duration {
        let total: Duration = self.frame_times.iter().sum();
        total / self.frame_times.len() as u32
    }
    
    pub fn get_memory_usage(&self) -> MemoryStats {
        self.memory_usage.get_stats()
    }
    
    pub fn get_cpu_usage(&self) -> CPUStats {
        self.cpu_usage.get_stats()
    }
}

pub struct FPSCounter {
    frame_count: u32,
    last_time: Instant,
    fps: f32,
}

impl FPSCounter {
    pub fn new() -> Self {
        Self {
            frame_count: 0,
            last_time: Instant::now(),
            fps: 0.0,
        }
    }
    
    pub fn record_frame(&mut self, frame_time: Duration) {
        self.frame_count += 1;
        
        let current_time = Instant::now();
        let elapsed = current_time.duration_since(self.last_time);
        
        if elapsed >= Duration::from_secs(1) {
            self.fps = self.frame_count as f32 / elapsed.as_secs_f32();
            self.frame_count = 0;
            self.last_time = current_time;
        }
    }
    
    pub fn get_fps(&self) -> f32 {
        self.fps
    }
}
```

### 7.2 调试工具

```rust
pub struct DebugRenderer {
    debug_shapes: Vec<DebugShape>,
    debug_text: Vec<DebugText>,
    enabled: bool,
}

impl DebugRenderer {
    pub fn new() -> Self {
        Self {
            debug_shapes: Vec::new(),
            debug_text: Vec::new(),
            enabled: false,
        }
    }
    
    pub fn draw_circle(&mut self, center: Vector2<f32>, radius: f32, color: Color) {
        if self.enabled {
            self.debug_shapes.push(DebugShape::Circle {
                center,
                radius,
                color,
            });
        }
    }
    
    pub fn draw_rectangle(&mut self, position: Vector2<f32>, size: Vector2<f32>, color: Color) {
        if self.enabled {
            self.debug_shapes.push(DebugShape::Rectangle {
                position,
                size,
                color,
            });
        }
    }
    
    pub fn draw_line(&mut self, start: Vector2<f32>, end: Vector2<f32>, color: Color) {
        if self.enabled {
            self.debug_shapes.push(DebugShape::Line {
                start,
                end,
                color,
            });
        }
    }
    
    pub fn draw_text(&mut self, text: String, position: Vector2<f32>, color: Color) {
        if self.enabled {
            self.debug_text.push(DebugText {
                text,
                position,
                color,
            });
        }
    }
    
    pub fn render(&self, renderer: &mut Renderer) {
        if !self.enabled {
            return;
        }
        
        // 渲染调试形状
        for shape in &self.debug_shapes {
            match shape {
                DebugShape::Circle { center, radius, color } => {
                    // 渲染圆形
                }
                DebugShape::Rectangle { position, size, color } => {
                    // 渲染矩形
                }
                DebugShape::Line { start, end, color } => {
                    // 渲染线条
                }
            }
        }
        
        // 渲染调试文本
        for text in &self.debug_text {
            // 渲染文本
        }
    }
    
    pub fn clear(&mut self) {
        self.debug_shapes.clear();
        self.debug_text.clear();
    }
}

#[derive(Debug)]
pub enum DebugShape {
    Circle {
        center: Vector2<f32>,
        radius: f32,
        color: Color,
    },
    Rectangle {
        position: Vector2<f32>,
        size: Vector2<f32>,
        color: Color,
    },
    Line {
        start: Vector2<f32>,
        end: Vector2<f32>,
        color: Color,
    },
}

#[derive(Debug)]
pub struct DebugText {
    pub text: String,
    pub position: Vector2<f32>,
    pub color: Color,
}
```

---

## 总结

本文档提供了游戏开发行业的完整架构指南，包括：

1. **技术栈选型**: 基于Rust的游戏开发技术栈
2. **ECS架构**: 实体-组件-系统架构设计
3. **客户端-服务器**: 网络游戏架构
4. **状态同步**: 预测、回滚、插值等网络同步技术
5. **渲染系统**: 基于wgpu的现代渲染管线
6. **物理引擎**: 基于Rapier的物理模拟
7. **性能优化**: 帧率监控、内存管理、调试工具

这些最佳实践为构建高性能、低延迟的游戏系统提供了全面的指导。
