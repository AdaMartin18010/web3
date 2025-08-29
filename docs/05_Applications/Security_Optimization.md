# 安全性优化应用

## 概述

安全性优化应用是Phase 3第3个月"性能优化"阶段的重要组成部分，专注于安全审计、漏洞修复和安全监控。

## 核心功能

### 1. 智能合约安全审计

#### Solidity - 安全审计合约

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@openzeppelin/contracts/security/ReentrancyGuard.sol";
import "@openzeppelin/contracts/security/Pausable.sol";
import "@openzeppelin/contracts/access/Ownable.sol";

contract SecurityAuditContract is ReentrancyGuard, Pausable, Ownable {
    event SecurityAuditCompleted(address indexed auditor, uint256 timestamp, string findings);
    event VulnerabilityDetected(string vulnerabilityType, string description, uint256 severity);

    struct AuditRecord {
        address auditor;
        uint256 timestamp;
        string findings;
        uint256 score;
        bool passed;
    }

    struct Vulnerability {
        string id;
        string type;
        string description;
        uint256 severity;
        bool fixed;
        uint256 detectedAt;
    }

    mapping(address => bool) public authorizedAuditors;
    mapping(uint256 => AuditRecord) public auditRecords;
    mapping(string => Vulnerability) public vulnerabilities;
    uint256 public auditCount;
    uint256 public vulnerabilityCount;

    modifier onlyAuditor() {
        require(authorizedAuditors[msg.sender], "Only authorized auditors");
        _;
    }

    constructor() {}

    function addAuditor(address auditor) external onlyOwner {
        require(auditor != address(0), "Invalid auditor address");
        authorizedAuditors[auditor] = true;
    }

    function performSecurityAudit(
        string memory findings,
        uint256 score
    ) external onlyAuditor {
        require(bytes(findings).length > 0, "Findings cannot be empty");
        require(score <= 100, "Score must be <= 100");

        auditCount++;
        auditRecords[auditCount] = AuditRecord({
            auditor: msg.sender,
            timestamp: block.timestamp,
            findings: findings,
            score: score,
            passed: score >= 80
        });

        emit SecurityAuditCompleted(msg.sender, block.timestamp, findings);

        if (score < 80) {
            _detectVulnerabilities(findings);
        }
    }

    function _detectVulnerabilities(string memory findings) internal {
        if (_contains(findings, "reentrancy")) {
            _addVulnerability("REENTRANCY", "Reentrancy vulnerability detected", 9);
        }
        if (_contains(findings, "overflow")) {
            _addVulnerability("OVERFLOW", "Integer overflow vulnerability detected", 8);
        }
        if (_contains(findings, "access")) {
            _addVulnerability("ACCESS_CONTROL", "Access control vulnerability detected", 7);
        }
    }

    function _addVulnerability(
        string memory vulnType,
        string memory description,
        uint256 severity
    ) internal {
        vulnerabilityCount++;
        string memory vulnId = string(abi.encodePacked("VULN-", _uint2str(vulnerabilityCount)));
        
        vulnerabilities[vulnId] = Vulnerability({
            id: vulnId,
            type: vulnType,
            description: description,
            severity: severity,
            fixed: false,
            detectedAt: block.timestamp
        });

        emit VulnerabilityDetected(vulnType, description, severity);
    }

    function fixVulnerability(string memory vulnId) external onlyOwner {
        require(bytes(vulnerabilities[vulnId].id).length > 0, "Vulnerability not found");
        require(!vulnerabilities[vulnId].fixed, "Vulnerability already fixed");

        vulnerabilities[vulnId].fixed = true;
    }

    function _contains(string memory source, string memory search) internal pure returns (bool) {
        bytes memory sourceBytes = bytes(source);
        bytes memory searchBytes = bytes(search);

        if (searchBytes.length > sourceBytes.length) {
            return false;
        }

        for (uint256 i = 0; i <= sourceBytes.length - searchBytes.length; i++) {
            bool found = true;
            for (uint256 j = 0; j < searchBytes.length; j++) {
                if (sourceBytes[i + j] != searchBytes[j]) {
                    found = false;
                    break;
                }
            }
            if (found) {
                return true;
            }
        }
        return false;
    }

    function _uint2str(uint256 value) internal pure returns (string memory) {
        if (value == 0) {
            return "0";
        }
        uint256 temp = value;
        uint256 digits;
        while (temp != 0) {
            digits++;
            temp /= 10;
        }
        bytes memory buffer = new bytes(digits);
        while (value != 0) {
            digits -= 1;
            buffer[digits] = bytes1(uint8(48 + uint256(value % 10)));
            value /= 10;
        }
        return string(buffer);
    }
}
```

### 2. 安全监控系统

#### Python - 安全监控服务

```python
import asyncio
import aiohttp
import time
from dataclasses import dataclass
from typing import List, Dict
from prometheus_client import Counter, Histogram, Gauge
import logging

@dataclass
class SecurityEvent:
    event_id: str
    event_type: str
    severity: int
    description: str
    source: str
    timestamp: float
    metadata: Dict

@dataclass
class SecurityAlert:
    alert_id: str
    event_id: str
    severity: int
    message: str
    timestamp: float
    resolved: bool

class SecurityMonitor:
    def __init__(self):
        self.security_events_total = Counter('security_events_total', 'Total security events', ['type', 'severity'])
        self.security_alerts_total = Counter('security_alerts_total', 'Total security alerts', ['severity'])
        self.active_vulnerabilities = Gauge('active_vulnerabilities', 'Active vulnerabilities')
        
        self.alert_thresholds = {
            'reentrancy': 8,
            'overflow': 7,
            'access_control': 6,
            'logic_error': 5,
        }
        
        self.events: List[SecurityEvent] = []
        self.alerts: List[SecurityAlert] = []
        self.alert_count = 0
        
        logging.basicConfig(level=logging.INFO)
        self.logger = logging.getLogger(__name__)

    async def monitor_smart_contract(self, contract_address: str, rpc_url: str):
        async with aiohttp.ClientSession() as session:
            while True:
                try:
                    await self._check_contract_status(session, contract_address, rpc_url)
                    await self._check_transaction_anomalies(session, contract_address, rpc_url)
                    await asyncio.sleep(30)
                    
                except Exception as e:
                    self.logger.error(f"Error monitoring contract {contract_address}: {e}")
                    await asyncio.sleep(60)

    async def _check_contract_status(self, session: aiohttp.ClientSession, contract_address: str, rpc_url: str):
        try:
            payload = {
                "jsonrpc": "2.0",
                "method": "eth_getCode",
                "params": [contract_address, "latest"],
                "id": 1
            }
            
            async with session.post(rpc_url, json=payload) as response:
                result = await response.json()
                
                if result.get('result') == '0x':
                    self._create_security_event(
                        'contract_destroyed',
                        9,
                        f'Contract {contract_address} has been destroyed',
                        'contract_monitor'
                    )
                    
        except Exception as e:
            self.logger.error(f"Error checking contract status: {e}")

    async def _check_transaction_anomalies(self, session: aiohttp.ClientSession, contract_address: str, rpc_url: str):
        try:
            payload = {
                "jsonrpc": "2.0",
                "method": "eth_getLogs",
                "params": [{
                    "address": contract_address,
                    "fromBlock": "latest",
                    "toBlock": "latest"
                }],
                "id": 1
            }
            
            async with session.post(rpc_url, json=payload) as response:
                result = await response.json()
                logs = result.get('result', [])
                
                if len(logs) > 10:
                    self._create_security_event(
                        'high_frequency_transactions',
                        6,
                        f'High frequency transactions detected for {contract_address}',
                        'transaction_monitor',
                        {'transaction_count': len(logs)}
                    )
                    
        except Exception as e:
            self.logger.error(f"Error checking transaction anomalies: {e}")

    def _create_security_event(self, event_type: str, severity: int, description: str, source: str, metadata: Dict = None):
        event = SecurityEvent(
            event_id=f"EVENT-{int(time.time())}",
            event_type=event_type,
            severity=severity,
            description=description,
            source=source,
            timestamp=time.time(),
            metadata=metadata or {}
        )
        
        self.events.append(event)
        self.security_events_total.labels(type=event_type, severity=str(severity)).inc()
        
        if severity >= self.alert_thresholds.get(event_type, 5):
            self._create_security_alert(event)
        
        self.logger.info(f"Security event created: {event_type} - {description}")

    def _create_security_alert(self, event: SecurityEvent):
        self.alert_count += 1
        alert = SecurityAlert(
            alert_id=f"ALERT-{self.alert_count}",
            event_id=event.event_id,
            severity=event.severity,
            message=f"Security alert: {event.description}",
            timestamp=time.time(),
            resolved=False
        )
        
        self.alerts.append(alert)
        self.security_alerts_total.labels(severity=str(event.severity)).inc()
        
        self.logger.warning(f"Security alert created: {alert.message}")

    def get_security_stats(self) -> Dict:
        total_events = len(self.events)
        total_alerts = len(self.alerts)
        active_alerts = len([a for a in self.alerts if not a.resolved])
        
        severity_stats = {}
        for event in self.events:
            severity = str(event.severity)
            severity_stats[severity] = severity_stats.get(severity, 0) + 1
        
        return {
            'total_events': total_events,
            'total_alerts': total_alerts,
            'active_alerts': active_alerts,
            'severity_distribution': severity_stats,
        }

    async def start_monitoring(self, contracts: List[Dict]):
        self.logger.info("Starting security monitoring...")
        
        tasks = []
        for contract in contracts:
            task = asyncio.create_task(
                self.monitor_smart_contract(
                    contract['address'],
                    contract['rpc_url']
                )
            )
            tasks.append(task)
        
        await asyncio.gather(*tasks)

if __name__ == "__main__":
    monitor = SecurityMonitor()
    
    contracts = [
        {
            'address': '0x1234567890123456789012345678901234567890',
            'rpc_url': 'https://mainnet.infura.io/v3/YOUR_PROJECT_ID'
        }
    ]
    
    asyncio.run(monitor.start_monitoring(contracts))
```

### 3. 漏洞扫描器

#### Rust - 高性能漏洞扫描

```rust
use std::collections::HashMap;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VulnerabilityScan {
    pub scan_id: String,
    pub target: String,
    pub scan_type: ScanType,
    pub status: ScanStatus,
    pub findings: Vec<VulnerabilityFinding>,
    pub start_time: u64,
    pub end_time: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ScanType {
    SmartContract,
    Network,
    API,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ScanStatus {
    Pending,
    Running,
    Completed,
    Failed,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VulnerabilityFinding {
    pub id: String,
    pub title: String,
    pub description: String,
    pub severity: VulnerabilitySeverity,
    pub category: VulnerabilityCategory,
    pub location: String,
    pub evidence: String,
    pub recommendation: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VulnerabilitySeverity {
    Critical,
    High,
    Medium,
    Low,
    Info,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VulnerabilityCategory {
    Reentrancy,
    IntegerOverflow,
    AccessControl,
    LogicError,
    GasLimit,
    Other,
}

pub struct VulnerabilityScanner {
    scan_rules: HashMap<String, ScanRule>,
    scan_history: Vec<VulnerabilityScan>,
}

#[derive(Debug, Clone)]
pub struct ScanRule {
    pub name: String,
    pub pattern: String,
    pub severity: VulnerabilitySeverity,
    pub category: VulnerabilityCategory,
    pub description: String,
}

impl VulnerabilityScanner {
    pub fn new() -> Self {
        let mut scanner = Self {
            scan_rules: HashMap::new(),
            scan_history: Vec::new(),
        };
        
        scanner.initialize_rules();
        scanner
    }

    fn initialize_rules(&mut self) {
        self.scan_rules.insert(
            "reentrancy_1".to_string(),
            ScanRule {
                name: "Reentrancy Attack".to_string(),
                pattern: "call\\.value".to_string(),
                severity: VulnerabilitySeverity::Critical,
                category: VulnerabilityCategory::Reentrancy,
                description: "Potential reentrancy vulnerability detected".to_string(),
            },
        );

        self.scan_rules.insert(
            "overflow_1".to_string(),
            ScanRule {
                name: "Integer Overflow".to_string(),
                pattern: "\\+\\+|--".to_string(),
                severity: VulnerabilitySeverity::High,
                category: VulnerabilityCategory::IntegerOverflow,
                description: "Potential integer overflow vulnerability".to_string(),
            },
        );

        self.scan_rules.insert(
            "access_control_1".to_string(),
            ScanRule {
                name: "Access Control".to_string(),
                pattern: "public\\s+function".to_string(),
                severity: VulnerabilitySeverity::Medium,
                category: VulnerabilityCategory::AccessControl,
                description: "Public function without access control".to_string(),
            },
        );
    }

    pub async fn scan_smart_contract(&mut self, contract_address: &str, contract_code: &str) -> VulnerabilityScan {
        let scan_id = format!("SCAN-{}", chrono::Utc::now().timestamp());
        let start_time = chrono::Utc::now().timestamp() as u64;
        
        let mut scan = VulnerabilityScan {
            scan_id: scan_id.clone(),
            target: contract_address.to_string(),
            scan_type: ScanType::SmartContract,
            status: ScanStatus::Running,
            findings: Vec::new(),
            start_time,
            end_time: None,
        };

        self.scan_history.push(scan.clone());

        let findings = self.scan_contract_code(contract_code).await;
        scan.findings = findings;
        scan.status = ScanStatus::Completed;
        scan.end_time = Some(chrono::Utc::now().timestamp() as u64);

        if let Some(last_scan) = self.scan_history.last_mut() {
            *last_scan = scan.clone();
        }

        scan
    }

    async fn scan_contract_code(&self, contract_code: &str) -> Vec<VulnerabilityFinding> {
        let mut findings = Vec::new();

        for (rule_id, rule) in &self.scan_rules {
            if contract_code.contains(&rule.pattern) {
                let finding = VulnerabilityFinding {
                    id: format!("{}-{}", rule_id, chrono::Utc::now().timestamp()),
                    title: rule.name.clone(),
                    description: rule.description.clone(),
                    severity: rule.severity.clone(),
                    category: rule.category.clone(),
                    location: "Contract code".to_string(),
                    evidence: format!("Pattern '{}' found in contract", rule.pattern),
                    recommendation: self.get_recommendation(&rule.category),
                };
                
                findings.push(finding);
            }
        }

        findings
    }

    fn get_recommendation(&self, category: &VulnerabilityCategory) -> String {
        match category {
            VulnerabilityCategory::Reentrancy => {
                "Use ReentrancyGuard or implement checks-effects-interactions pattern".to_string()
            }
            VulnerabilityCategory::IntegerOverflow => {
                "Use SafeMath library or upgrade to Solidity 0.8+".to_string()
            }
            VulnerabilityCategory::AccessControl => {
                "Implement proper access control using modifiers".to_string()
            }
            VulnerabilityCategory::GasLimit => {
                "Avoid unbounded loops and implement pagination".to_string()
            }
            VulnerabilityCategory::LogicError => {
                "Review the logic and implement proper validation".to_string()
            }
            VulnerabilityCategory::Other => {
                "Review the code and implement appropriate security measures".to_string()
            }
        }
    }

    pub fn get_scan_history(&self) -> &Vec<VulnerabilityScan> {
        &self.scan_history
    }

    pub fn get_security_stats(&self) -> HashMap<String, usize> {
        let mut stats = HashMap::new();
        
        for scan in &self.scan_history {
            for finding in &scan.findings {
                let severity_key = format!("severity_{:?}", finding.severity);
                *stats.entry(severity_key).or_insert(0) += 1;
                
                let category_key = format!("category_{:?}", finding.category);
                *stats.entry(category_key).or_insert(0) += 1;
            }
        }
        
        stats
    }
}

#[tokio::main]
async fn main() {
    let mut scanner = VulnerabilityScanner::new();
    
    let contract_code = r#"
        pragma solidity ^0.8.19;
        
        contract VulnerableContract {
            mapping(address => uint256) public balances;
            
            function withdraw() public {
                uint256 amount = balances[msg.sender];
                require(amount > 0);
                
                (bool success, ) = msg.sender.call{value: amount}("");
                require(success);
                
                balances[msg.sender] = 0;
            }
        }
    "#;
    
    let scan_result = scanner.scan_smart_contract(
        "0x1234567890123456789012345678901234567890",
        contract_code
    ).await;
    
    println!("Scan completed: {:?}", scan_result);
    println!("Findings count: {}", scan_result.findings.len());
    
    for finding in &scan_result.findings {
        println!("Finding: {:?} - {:?}", finding.severity, finding.title);
    }
}
```

### 4. 部署配置

#### Docker Compose配置

```yaml
version: '3.8'

services:
  # 安全监控前端
  security-frontend:
    build:
      context: ./frontend
      dockerfile: Dockerfile
    ports:
      - "3000:3000"
    environment:
      - NEXT_PUBLIC_API_URL=http://localhost:8080
    depends_on:
      - security-backend
    networks:
      - security-network

  # 安全监控后端
  security-backend:
    build:
      context: ./backend
      dockerfile: Dockerfile
    ports:
      - "8080:8080"
    environment:
      - DATABASE_URL=postgresql://user:password@postgres:5432/security
      - REDIS_URL=redis://redis:6379
      - ETHEREUM_RPC_URL=https://mainnet.infura.io/v3/YOUR_PROJECT_ID
    depends_on:
      - postgres
      - redis
    networks:
      - security-network

  # 漏洞扫描器
  vulnerability-scanner:
    build:
      context: ./scanner
      dockerfile: Dockerfile
    environment:
      - SCAN_INTERVAL=3600
      - TARGET_CONTRACTS=0x1234,0x5678
    depends_on:
      - security-backend
    networks:
      - security-network

  # PostgreSQL数据库
  postgres:
    image: postgres:13
    environment:
      - POSTGRES_DB=security
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=password
    networks:
      - security-network

  # Redis缓存
  redis:
    image: redis:6-alpine
    networks:
      - security-network

networks:
  security-network:
    driver: bridge
```

## 总结

安全性优化应用提供了完整的安全保障解决方案：

1. **智能合约安全审计**: 自动化的安全审计合约
2. **安全监控系统**: 实时安全事件监控和告警
3. **漏洞扫描器**: 高性能的漏洞检测和分析
4. **完整部署**: Docker容器化部署方案

该系统显著提升了Web3应用的安全性，能够及时发现和修复安全漏洞，为用户提供安全可靠的使用环境。
