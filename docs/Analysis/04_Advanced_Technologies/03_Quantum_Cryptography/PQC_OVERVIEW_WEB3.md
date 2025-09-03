# 后量子密码学（PQC）在Web3中的概览

## 摘要

梳理格基/哈希签名/多变量等PQC算法族在链上账户、签名、KMS 与跨链中的替换路线与迁移策略。

## 1. 算法族与标准

- 格基：CRYSTALS-Kyber/Dilithium、FALCON
- 哈希签名：XMSS、SPHINCS+
- 标准进展：NIST PQC、IETF CFRG

## 2. 集成策略

- 双轨制：传统算法+PQC并行，渐进切换
- 账户升级：多签/社交恢复引入PQC钥对
- 证明系统：ZK电路兼容PQC验签

## 3. 风险与兼容

- 交易尺寸增大、Gas 成本提升
- HSM/TEE 支持度与密钥管理流程改造

## 4. 参考

- NIST PQC 项目、SPHINCS+、CRYSTALS 系列文档
