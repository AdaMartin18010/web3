# 医疗健康行业架构最佳实践

## 目录

1. 行业概述与核心挑战
2. 技术栈选型与架构模式
3. 医疗微服务架构
4. 事件驱动医疗架构
5. 患者管理与临床服务
6. 医疗影像与AI诊断
7. 安全与合规

---

## 1. 行业概述与核心挑战

### 1.1 行业特点

医疗健康领域对数据安全、系统可靠性、实时性和合规性有极高要求。

### 1.2 核心挑战

- **数据安全**: 患者隐私保护、HIPAA合规
- **系统可靠性**: 7x24小时运行、故障恢复
- **实时性**: 紧急情况处理、实时监控
- **合规性**: 医疗标准、监管要求
- **互操作性**: 不同系统间数据交换

---

## 2. 技术栈选型与架构模式

### 2.1 核心技术栈

```toml
[dependencies]
# 医疗标准
hl7-rs = "0.1"
dicom-rs = "0.2"
fhir-rs = "0.3"

# 数据安全
ring = "0.17"
rustls = "0.21"
aes-gcm = "0.10"

# 实时处理
tokio = { version = "1.35", features = ["full"] }
async-std = "1.35"
actix-web = "4.4"

# 数据库
diesel = { version = "2.1", features = ["postgres"] }
sqlx = { version = "0.7", features = ["postgres", "runtime-tokio-rustls"] }
postgres = "0.19"

# 医疗设备集成
modbus-rs = "0.1"
opc-ua-rs = "0.2"
mqtt = "0.3"

# 传感器
embedded-hal = "0.2"
i2c-rs = "0.1"
spi-rs = "0.1"

# 实时监控
influxdb-rust = "0.1"
timescaledb-rust = "0.1"

# 人工智能/机器学习
opencv-rust = "0.1"
image-rs = "0.24"
tch-rs = "0.13"
rust-bert = "0.1"
tokenizers = "0.15"
polars = "0.35"
ndarray = "0.15"
statrs = "0.16"
```

---

## 3. 医疗微服务架构

### 3.1 架构层次

```text
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   API Gateway   │    │  Authentication │    │  Patient Service│
│   (Actix-web)   │    │   Service       │    │                 │
└─────────────────┘    └─────────────────┘    └─────────────────┘
         │                       │                       │
         └───────────────────────┼───────────────────────┘
                                 │
         ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
         │ Clinical Service│    │ Imaging Service │    │ Pharmacy Service│
         │                 │    │                 │    │                 │
         └─────────────────┘    └─────────────────┘    └─────────────────┘
```

### 3.2 微服务实现

```rust
use actix_web::{web, App, HttpServer, middleware};
use serde::{Deserialize, Serialize};

#[derive(Clone)]
pub struct HealthcareMicroservices {
    patient_service: PatientService,
    clinical_service: ClinicalService,
    imaging_service: ImagingService,
    pharmacy_service: PharmacyService,
    billing_service: BillingService,
}

impl HealthcareMicroservices {
    pub async fn start_services(&self) -> Result<(), ServiceError> {
        // 启动各个微服务
        let patient_server = HttpServer::new(|| {
            App::new()
                .wrap(middleware::Logger::default())
                .service(patient_routes())
        })
        .bind("127.0.0.1:8081")?
        .run();

        let clinical_server = HttpServer::new(|| {
            App::new()
                .wrap(middleware::Logger::default())
                .service(clinical_routes())
        })
        .bind("127.0.0.1:8082")?
        .run();

        // 并行运行所有服务
        tokio::try_join!(patient_server, clinical_server)?;
        Ok(())
    }
}

// 患者服务
pub struct PatientService {
    patient_repository: Arc<PatientRepository>,
    audit_logger: Arc<AuditLogger>,
}

impl PatientService {
    pub async fn create_patient(&self, patient_data: CreatePatientRequest) -> Result<Patient, ServiceError> {
        // 1. 验证患者数据
        self.validate_patient_data(&patient_data).await?;
        
        // 2. 创建患者记录
        let patient = Patient::new(patient_data);
        
        // 3. 保存到数据库
        let saved_patient = self.patient_repository.save(&patient).await?;
        
        // 4. 记录审计日志
        self.audit_logger.log_patient_creation(&saved_patient).await?;
        
        Ok(saved_patient)
    }
    
    pub async fn get_patient(&self, patient_id: &str) -> Result<Patient, ServiceError> {
        // 1. 检查访问权限
        self.check_access_permission(patient_id).await?;
        
        // 2. 获取患者信息
        let patient = self.patient_repository.get(patient_id).await?;
        
        // 3. 记录访问日志
        self.audit_logger.log_patient_access(patient_id).await?;
        
        Ok(patient)
    }
    
    async fn validate_patient_data(&self, data: &CreatePatientRequest) -> Result<(), ServiceError> {
        // 验证必填字段
        if data.demographics.first_name.is_empty() || data.demographics.last_name.is_empty() {
            return Err(ServiceError::ValidationError("姓名不能为空".to_string()));
        }
        
        // 验证日期格式
        if data.demographics.date_of_birth > Utc::now().date_naive() {
            return Err(ServiceError::ValidationError("出生日期不能晚于今天".to_string()));
        }
        
        // 验证保险信息
        if let Some(insurance) = &data.insurance {
            self.validate_insurance_info(insurance).await?;
        }
        
        Ok(())
    }
}

// 临床服务
pub struct ClinicalService {
    clinical_repository: Arc<ClinicalRepository>,
    lab_service: Arc<LabService>,
    medication_service: Arc<MedicationService>,
}

impl ClinicalService {
    pub async fn create_encounter(&self, encounter_data: CreateEncounterRequest) -> Result<Encounter, ServiceError> {
        // 1. 验证患者存在
        self.validate_patient_exists(&encounter_data.patient_id).await?;
        
        // 2. 创建就诊记录
        let encounter = Encounter::new(encounter_data);
        
        // 3. 保存就诊记录
        let saved_encounter = self.clinical_repository.save_encounter(&encounter).await?;
        
        // 4. 触发相关流程
        self.trigger_encounter_workflows(&saved_encounter).await?;
        
        Ok(saved_encounter)
    }
    
    pub async fn order_lab_test(&self, lab_order: LabOrder) -> Result<LabOrder, ServiceError> {
        // 1. 验证医嘱权限
        self.validate_ordering_privileges(&lab_order.ordering_provider).await?;
        
        // 2. 创建检验医嘱
        let order = self.clinical_repository.create_lab_order(&lab_order).await?;
        
        // 3. 发送到检验科
        self.lab_service.submit_order(&order).await?;
        
        Ok(order)
    }
    
    pub async fn prescribe_medication(&self, prescription: Prescription) -> Result<Prescription, ServiceError> {
        // 1. 检查药物相互作用
        self.check_drug_interactions(&prescription).await?;
        
        // 2. 检查过敏史
        self.check_allergies(&prescription).await?;
        
        // 3. 创建处方
        let saved_prescription = self.clinical_repository.save_prescription(&prescription).await?;
        
        // 4. 发送到药房
        self.medication_service.process_prescription(&saved_prescription).await?;
        
        Ok(saved_prescription)
    }
}
```

---

## 4. 事件驱动医疗架构

### 4.1 事件定义

```rust
use tokio::sync::mpsc;
use serde::{Deserialize, Serialize};

#[derive(Clone, Serialize, Deserialize)]
pub struct MedicalEvent {
    pub id: String,
    pub event_type: MedicalEventType,
    pub patient_id: String,
    pub timestamp: DateTime<Utc>,
    pub data: serde_json::Value,
    pub source: String,
    pub priority: EventPriority,
}

#[derive(Clone, Serialize, Deserialize)]
pub enum MedicalEventType {
    PatientAdmission,
    PatientDischarge,
    LabResult,
    MedicationOrder,
    MedicationAdministered,
    VitalSigns,
    Alert,
    Appointment,
}

#[derive(Clone, Serialize, Deserialize)]
pub enum EventPriority {
    Critical,
    High,
    Medium,
    Low,
}

// 具体事件类型
#[derive(Clone, Serialize, Deserialize)]
pub struct PatientAdmissionEvent {
    pub patient_id: String,
    pub admission_date: DateTime<Utc>,
    pub admitting_provider: String,
    pub diagnosis: String,
    pub room_number: String,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct LabResultEvent {
    pub patient_id: String,
    pub test_id: String,
    pub test_name: String,
    pub result_value: String,
    pub reference_range: String,
    pub is_abnormal: bool,
    pub reported_by: String,
    pub reported_at: DateTime<Utc>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct VitalSignsEvent {
    pub patient_id: String,
    pub temperature: Option<f32>,
    pub blood_pressure: Option<BloodPressure>,
    pub heart_rate: Option<i32>,
    pub respiratory_rate: Option<i32>,
    pub oxygen_saturation: Option<i32>,
    pub recorded_at: DateTime<Utc>,
    pub recorded_by: String,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct BloodPressure {
    pub systolic: i32,
    pub diastolic: i32,
}
```

### 4.2 事件处理器

```rust
pub struct EventDrivenHealthcare {
    event_bus: EventBus,
    event_handlers: HashMap<MedicalEventType, Vec<Box<dyn EventHandler>>>,
    alert_system: AlertSystem,
}

impl EventDrivenHealthcare {
    pub async fn process_event(&self, event: MedicalEvent) -> Result<(), EventError> {
        // 1. 发布事件到事件总线
        self.event_bus.publish(event.clone()).await?;
        
        // 2. 处理事件
        if let Some(handlers) = self.event_handlers.get(&event.event_type) {
            for handler in handlers {
                handler.handle(&event).await?;
            }
        }
        
        // 3. 检查是否需要告警
        if event.priority == EventPriority::Critical {
            self.alert_system.send_alert(&event).await?;
        }
        
        Ok(())
    }
    
    pub async fn subscribe_to_events(
        &mut self,
        event_type: MedicalEventType,
        handler: Box<dyn EventHandler>,
    ) {
        self.event_handlers
            .entry(event_type)
            .or_insert_with(Vec::new)
            .push(handler);
    }
}

pub trait EventHandler {
    async fn handle(&self, event: &MedicalEvent) -> Result<(), EventError>;
}

// 患者入院事件处理器
pub struct PatientAdmissionHandler {
    bed_management: Arc<BedManagementService>,
    notification_service: Arc<NotificationService>,
}

impl EventHandler for PatientAdmissionHandler {
    async fn handle(&self, event: &MedicalEvent) -> Result<(), EventError> {
        if let MedicalEventType::PatientAdmission = event.event_type {
            let admission_data: PatientAdmissionEvent = serde_json::from_value(event.data.clone())?;
            
            // 1. 分配床位
            self.bed_management.assign_bed(&admission_data).await?;
            
            // 2. 发送通知
            self.notification_service.notify_admission(&admission_data).await?;
            
            // 3. 触发入院流程
            self.trigger_admission_workflow(&admission_data).await?;
        }
        Ok(())
    }
}

// 检验结果事件处理器
pub struct LabResultHandler {
    clinical_service: Arc<ClinicalService>,
    alert_system: Arc<AlertSystem>,
}

impl EventHandler for LabResultHandler {
    async fn handle(&self, event: &MedicalEvent) -> Result<(), EventError> {
        if let MedicalEventType::LabResult = event.event_type {
            let lab_result: LabResultEvent = serde_json::from_value(event.data.clone())?;
            
            // 1. 保存检验结果
            self.clinical_service.save_lab_result(&lab_result).await?;
            
            // 2. 检查异常结果
            if lab_result.is_abnormal {
                self.alert_system.send_lab_alert(&lab_result).await?;
            }
            
            // 3. 通知相关医护人员
            self.notify_providers(&lab_result).await?;
        }
        Ok(())
    }
}

// 生命体征事件处理器
pub struct VitalSignsHandler {
    monitoring_service: Arc<MonitoringService>,
    alert_system: Arc<AlertSystem>,
}

impl EventHandler for VitalSignsHandler {
    async fn handle(&self, event: &MedicalEvent) -> Result<(), EventError> {
        if let MedicalEventType::VitalSigns = event.event_type {
            let vital_signs: VitalSignsEvent = serde_json::from_value(event.data.clone())?;
            
            // 1. 保存生命体征
            self.monitoring_service.save_vital_signs(&vital_signs).await?;
            
            // 2. 检查异常值
            if let Some(alerts) = self.check_vital_signs_alerts(&vital_signs).await? {
                for alert in alerts {
                    self.alert_system.send_vital_signs_alert(&alert).await?;
                }
            }
            
            // 3. 更新患者状态
            self.monitoring_service.update_patient_status(&vital_signs).await?;
        }
        Ok(())
    }
    
    async fn check_vital_signs_alerts(&self, vital_signs: &VitalSignsEvent) -> Result<Option<Vec<Alert>>, EventError> {
        let mut alerts = Vec::new();
        
        // 检查体温
        if let Some(temp) = vital_signs.temperature {
            if temp > 38.0 || temp < 35.0 {
                alerts.push(Alert::new(
                    AlertType::TemperatureAbnormal,
                    format!("患者体温异常: {}°C", temp),
                    AlertSeverity::High,
                ));
            }
        }
        
        // 检查血压
        if let Some(bp) = &vital_signs.blood_pressure {
            if bp.systolic > 180 || bp.systolic < 90 || bp.diastolic > 110 || bp.diastolic < 60 {
                alerts.push(Alert::new(
                    AlertType::BloodPressureAbnormal,
                    format!("患者血压异常: {}/{} mmHg", bp.systolic, bp.diastolic),
                    AlertSeverity::High,
                ));
            }
        }
        
        // 检查心率
        if let Some(hr) = vital_signs.heart_rate {
            if hr > 100 || hr < 60 {
                alerts.push(Alert::new(
                    AlertType::HeartRateAbnormal,
                    format!("患者心率异常: {} bpm", hr),
                    AlertSeverity::Medium,
                ));
            }
        }
        
        if alerts.is_empty() {
            Ok(None)
        } else {
            Ok(Some(alerts))
        }
    }
}
```

---

## 5. 患者管理与临床服务

### 5.1 患者记录

```rust
#[derive(Serialize, Deserialize)]
pub struct PatientRecord {
    pub id: String,
    pub mrn: String, // Medical Record Number
    pub demographics: Demographics,
    pub medical_history: MedicalHistory,
    pub current_medications: Vec<Medication>,
    pub allergies: Vec<Allergy>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Serialize, Deserialize)]
pub struct Demographics {
    pub first_name: String,
    pub last_name: String,
    pub date_of_birth: Date<Utc>,
    pub gender: Gender,
    pub address: Address,
    pub contact_info: ContactInfo,
}

#[derive(Serialize, Deserialize)]
pub enum Gender {
    Male,
    Female,
    Other,
    PreferNotToSay,
}

#[derive(Serialize, Deserialize)]
pub struct Address {
    pub street: String,
    pub city: String,
    pub state: String,
    pub zip_code: String,
    pub country: String,
}

#[derive(Serialize, Deserialize)]
pub struct ContactInfo {
    pub phone: String,
    pub email: Option<String>,
    pub emergency_contact: EmergencyContact,
}

#[derive(Serialize, Deserialize)]
pub struct EmergencyContact {
    pub name: String,
    pub relationship: String,
    pub phone: String,
}

#[derive(Serialize, Deserialize)]
pub struct MedicalHistory {
    pub conditions: Vec<MedicalCondition>,
    pub surgeries: Vec<Surgery>,
    pub family_history: Vec<FamilyHistory>,
}

#[derive(Serialize, Deserialize)]
pub struct MedicalCondition {
    pub condition: String,
    pub diagnosis_date: Date<Utc>,
    pub status: ConditionStatus,
    pub notes: Option<String>,
}

#[derive(Serialize, Deserialize)]
pub enum ConditionStatus {
    Active,
    Resolved,
    Chronic,
    Remission,
}

#[derive(Serialize, Deserialize)]
pub struct Medication {
    pub name: String,
    pub dosage: String,
    pub frequency: String,
    pub start_date: Date<Utc>,
    pub end_date: Option<Date<Utc>>,
    pub prescribed_by: String,
    pub notes: Option<String>,
}

#[derive(Serialize, Deserialize)]
pub struct Allergy {
    pub allergen: String,
    pub reaction: String,
    pub severity: AllergySeverity,
    pub notes: Option<String>,
}

#[derive(Serialize, Deserialize)]
pub enum AllergySeverity {
    Mild,
    Moderate,
    Severe,
    LifeThreatening,
}
```

### 5.2 临床服务

```rust
#[derive(Serialize, Deserialize)]
pub struct Encounter {
    pub id: String,
    pub patient_id: String,
    pub encounter_type: EncounterType,
    pub start_date: DateTime<Utc>,
    pub end_date: Option<DateTime<Utc>>,
    pub provider: String,
    pub diagnosis: Vec<Diagnosis>,
    pub procedures: Vec<Procedure>,
    pub medications: Vec<MedicationOrder>,
    pub vital_signs: Vec<VitalSigns>,
    pub notes: Vec<ClinicalNote>,
}

#[derive(Serialize, Deserialize)]
pub enum EncounterType {
    Inpatient,
    Outpatient,
    Emergency,
    Consultation,
}

#[derive(Serialize, Deserialize)]
pub struct Diagnosis {
    pub icd_code: String,
    pub description: String,
    pub diagnosis_date: DateTime<Utc>,
    pub provider: String,
    pub status: DiagnosisStatus,
}

#[derive(Serialize, Deserialize)]
pub enum DiagnosisStatus {
    Provisional,
    Confirmed,
    RuledOut,
}

#[derive(Serialize, Deserialize)]
pub struct Procedure {
    pub cpt_code: String,
    pub description: String,
    pub procedure_date: DateTime<Utc>,
    pub provider: String,
    pub notes: Option<String>,
}

#[derive(Serialize, Deserialize)]
pub struct MedicationOrder {
    pub medication: String,
    pub dosage: String,
    pub route: String,
    pub frequency: String,
    pub start_date: DateTime<Utc>,
    pub end_date: Option<DateTime<Utc>>,
    pub ordered_by: String,
    pub status: OrderStatus,
}

#[derive(Serialize, Deserialize)]
pub enum OrderStatus {
    Ordered,
    Dispensed,
    Administered,
    Discontinued,
}

#[derive(Serialize, Deserialize)]
pub struct ClinicalNote {
    pub note_type: NoteType,
    pub content: String,
    pub author: String,
    pub timestamp: DateTime<Utc>,
    pub is_confidential: bool,
}

#[derive(Serialize, Deserialize)]
pub enum NoteType {
    Progress,
    Discharge,
    Consultation,
    Procedure,
    Nursing,
}
```

---

## 6. 医疗影像与AI诊断

### 6.1 影像服务

```rust
pub struct ImagingService {
    image_repository: Arc<ImageRepository>,
    ai_diagnosis: Arc<AIDiagnosisService>,
    dicom_service: Arc<DicomService>,
}

impl ImagingService {
    pub async fn upload_image(&self, image_data: ImageUploadRequest) -> Result<ImageRecord, ServiceError> {
        // 1. 验证图像格式
        self.validate_image_format(&image_data).await?;
        
        // 2. 处理DICOM数据
        let processed_image = self.dicom_service.process_dicom(&image_data.data).await?;
        
        // 3. 保存图像
        let image_record = self.image_repository.save_image(&processed_image).await?;
        
        // 4. 触发AI分析
        self.trigger_ai_analysis(&image_record).await?;
        
        Ok(image_record)
    }
    
    pub async fn get_ai_diagnosis(&self, image_id: &str) -> Result<AIDiagnosis, ServiceError> {
        // 1. 获取图像记录
        let image_record = self.image_repository.get_image(image_id).await?;
        
        // 2. 获取AI诊断结果
        let diagnosis = self.ai_diagnosis.get_diagnosis(image_id).await?;
        
        // 3. 记录访问日志
        self.audit_logger.log_image_access(image_id).await?;
        
        Ok(diagnosis)
    }
    
    async fn trigger_ai_analysis(&self, image_record: &ImageRecord) -> Result<(), ServiceError> {
        // 异步触发AI分析
        let image_id = image_record.id.clone();
        let ai_service = self.ai_diagnosis.clone();
        
        tokio::spawn(async move {
            if let Err(e) = ai_service.analyze_image(&image_id).await {
                tracing::error!("AI analysis failed for image {}: {:?}", image_id, e);
            }
        });
        
        Ok(())
    }
}

// AI诊断服务
pub struct AIDiagnosisService {
    model_manager: Arc<ModelManager>,
    result_repository: Arc<DiagnosisResultRepository>,
}

impl AIDiagnosisService {
    pub async fn analyze_image(&self, image_id: &str) -> Result<AIDiagnosis, ServiceError> {
        // 1. 加载图像
        let image_data = self.load_image_data(image_id).await?;
        
        // 2. 预处理图像
        let preprocessed_image = self.preprocess_image(&image_data).await?;
        
        // 3. 运行AI模型
        let model_results = self.run_ai_models(&preprocessed_image).await?;
        
        // 4. 后处理结果
        let diagnosis = self.postprocess_results(&model_results).await?;
        
        // 5. 保存诊断结果
        self.result_repository.save_diagnosis(&diagnosis).await?;
        
        Ok(diagnosis)
    }
    
    async fn run_ai_models(&self, image: &PreprocessedImage) -> Result<Vec<ModelResult>, ServiceError> {
        let mut results = Vec::new();
        
        // 运行多个AI模型
        let models = self.model_manager.get_available_models().await?;
        
        for model in models {
            let result = self.run_single_model(&model, image).await?;
            results.push(result);
        }
        
        Ok(results)
    }
    
    async fn run_single_model(&self, model: &AIModel, image: &PreprocessedImage) -> Result<ModelResult, ServiceError> {
        match model.model_type {
            ModelType::Classification => {
                self.run_classification_model(model, image).await
            }
            ModelType::Segmentation => {
                self.run_segmentation_model(model, image).await
            }
            ModelType::Detection => {
                self.run_detection_model(model, image).await
            }
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct AIDiagnosis {
    pub id: String,
    pub image_id: String,
    pub findings: Vec<Finding>,
    pub confidence_score: f32,
    pub model_version: String,
    pub analysis_date: DateTime<Utc>,
    pub status: DiagnosisStatus,
}

#[derive(Serialize, Deserialize)]
pub struct Finding {
    pub finding_type: FindingType,
    pub description: String,
    pub location: Option<ImageLocation>,
    pub confidence: f32,
    pub severity: FindingSeverity,
}

#[derive(Serialize, Deserialize)]
pub enum FindingType {
    Tumor,
    Fracture,
    Pneumonia,
    Cardiomegaly,
    Other(String),
}

#[derive(Serialize, Deserialize)]
pub struct ImageLocation {
    pub x: f32,
    pub y: f32,
    pub width: f32,
    pub height: f32,
}

#[derive(Serialize, Deserialize)]
pub enum FindingSeverity {
    Normal,
    Mild,
    Moderate,
    Severe,
    Critical,
}
```

---

## 7. 安全与合规

### 7.1 HIPAA合规

```rust
pub struct HIPAAComplianceService {
    encryption_service: Arc<EncryptionService>,
    audit_logger: Arc<AuditLogger>,
    access_control: Arc<AccessControlService>,
}

impl HIPAAComplianceService {
    pub async fn encrypt_phi(&self, data: &[u8]) -> Result<Vec<u8>, ComplianceError> {
        // 使用AES-256加密PHI数据
        let encrypted = self.encryption_service.encrypt_aes256(data).await?;
        
        // 记录加密操作
        self.audit_logger.log_encryption(data.len()).await?;
        
        Ok(encrypted)
    }
    
    pub async fn decrypt_phi(&self, encrypted_data: &[u8], user_id: &str) -> Result<Vec<u8>, ComplianceError> {
        // 检查访问权限
        self.access_control.check_phi_access(user_id).await?;
        
        // 解密数据
        let decrypted = self.encryption_service.decrypt_aes256(encrypted_data).await?;
        
        // 记录访问日志
        self.audit_logger.log_phi_access(user_id, encrypted_data.len()).await?;
        
        Ok(decrypted)
    }
    
    pub async fn log_phi_access(&self, user_id: &str, patient_id: &str, action: &str) -> Result<(), ComplianceError> {
        let audit_entry = PHIAuditEntry {
            id: AuditId::new(),
            user_id: user_id.to_string(),
            patient_id: patient_id.to_string(),
            action: action.to_string(),
            timestamp: Utc::now(),
            ip_address: None, // 从上下文获取
            success: true,
        };
        
        self.audit_logger.log_phi_audit(&audit_entry).await?;
        Ok(())
    }
}

// 访问控制服务
pub struct AccessControlService {
    user_repository: Arc<UserRepository>,
    role_repository: Arc<RoleRepository>,
    permission_repository: Arc<PermissionRepository>,
}

impl AccessControlService {
    pub async fn check_phi_access(&self, user_id: &str) -> Result<(), AccessError> {
        // 1. 获取用户信息
        let user = self.user_repository.get_user(user_id).await?;
        
        // 2. 检查用户状态
        if user.status != UserStatus::Active {
            return Err(AccessError::UserInactive);
        }
        
        // 3. 检查角色权限
        let roles = self.role_repository.get_user_roles(user_id).await?;
        let has_phi_access = roles.iter().any(|role| role.has_phi_permission());
        
        if !has_phi_access {
            return Err(AccessError::InsufficientPermissions);
        }
        
        Ok(())
    }
    
    pub async fn check_patient_access(&self, user_id: &str, patient_id: &str) -> Result<(), AccessError> {
        // 1. 检查基本PHI访问权限
        self.check_phi_access(user_id).await?;
        
        // 2. 检查特定患者访问权限
        let permissions = self.permission_repository.get_user_patient_permissions(user_id).await?;
        
        if !permissions.contains(&patient_id.to_string()) {
            return Err(AccessError::PatientAccessDenied);
        }
        
        Ok(())
    }
}
```

### 7.2 审计日志

```rust
#[derive(Serialize, Deserialize)]
pub struct PHIAuditEntry {
    pub id: AuditId,
    pub user_id: String,
    pub patient_id: String,
    pub action: String,
    pub timestamp: DateTime<Utc>,
    pub ip_address: Option<String>,
    pub success: bool,
    pub details: Option<serde_json::Value>,
}

pub struct AuditLogger {
    audit_repository: Arc<AuditRepository>,
    compliance_service: Arc<HIPAAComplianceService>,
}

impl AuditLogger {
    pub async fn log_phi_audit(&self, entry: &PHIAuditEntry) -> Result<(), AuditError> {
        // 1. 保存审计记录
        self.audit_repository.save_phi_audit(entry).await?;
        
        // 2. 检查是否需要合规报告
        if self.should_generate_compliance_report(entry).await? {
            self.generate_compliance_report(entry).await?;
        }
        
        Ok(())
    }
    
    pub async fn log_patient_creation(&self, patient: &Patient) -> Result<(), AuditError> {
        let entry = PHIAuditEntry {
            id: AuditId::new(),
            user_id: "system".to_string(), // 从上下文获取
            patient_id: patient.id.clone(),
            action: "CREATE_PATIENT".to_string(),
            timestamp: Utc::now(),
            ip_address: None,
            success: true,
            details: Some(serde_json::to_value(patient)?),
        };
        
        self.log_phi_audit(&entry).await
    }
    
    pub async fn log_patient_access(&self, patient_id: &str) -> Result<(), AuditError> {
        let entry = PHIAuditEntry {
            id: AuditId::new(),
            user_id: "system".to_string(), // 从上下文获取
            patient_id: patient_id.to_string(),
            action: "ACCESS_PATIENT".to_string(),
            timestamp: Utc::now(),
            ip_address: None,
            success: true,
            details: None,
        };
        
        self.log_phi_audit(&entry).await
    }
}
```

---

## 总结

本文档提供了医疗健康行业的完整架构指南，包括：

1. **技术栈选型**: 基于Rust的医疗健康开发技术栈
2. **微服务架构**: 患者服务、临床服务、影像服务、药房服务等
3. **事件驱动**: 医疗事件定义、事件处理器、事件总线
4. **患者管理**: 患者记录、人口统计学、病史、药物、过敏史等
5. **临床服务**: 就诊记录、诊断、程序、药物医嘱、临床记录等
6. **医疗影像**: 图像处理、AI诊断、DICOM服务等
7. **安全合规**: HIPAA合规、访问控制、审计日志等

这些最佳实践为构建安全、可靠、合规的医疗健康系统提供了全面的指导。
