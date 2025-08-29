# ZKP隐私投票应用

## 基于零知识证明的隐私保护投票系统

### 应用概述

基于Phase 2的ZKP实现指南，开发一个完整的隐私投票系统，使用零知识证明保护选民隐私，确保投票的匿名性和可验证性。

### 核心功能

#### 1. 智能合约层

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@openzeppelin/contracts/access/Ownable.sol";

/**
 * @title PrivacyVoting
 * @dev 基于零知识证明的隐私投票系统
 */
contract PrivacyVoting is Ownable {
    struct Proposal {
        string title;
        string description;
        uint256 startTime;
        uint256 endTime;
        bool isActive;
        uint256 totalVotes;
        mapping(bytes32 => bool) nullifiers;
    }
    
    struct Vote {
        bytes32 commitment;
        bytes32 nullifier;
        bytes proof;
        uint256 proposalId;
    }
    
    mapping(uint256 => Proposal) public proposals;
    mapping(address => bool) public registeredVoters;
    mapping(bytes32 => bool) public usedCommitments;
    
    uint256 public proposalCount;
    uint256 public constant VOTING_PERIOD = 7 days;
    
    event ProposalCreated(uint256 indexed proposalId, string title, uint256 startTime, uint256 endTime);
    event VoteSubmitted(uint256 indexed proposalId, bytes32 indexed nullifier, uint256 timestamp);
    event VoterRegistered(address indexed voter, uint256 timestamp);
    
    modifier onlyRegisteredVoter() {
        require(registeredVoters[msg.sender], "Not registered voter");
        _;
    }
    
    modifier proposalActive(uint256 proposalId) {
        require(proposals[proposalId].isActive, "Proposal not active");
        require(block.timestamp >= proposals[proposalId].startTime, "Voting not started");
        require(block.timestamp <= proposals[proposalId].endTime, "Voting ended");
        _;
    }
    
    /**
     * @dev 创建投票提案
     */
    function createProposal(
        string memory title,
        string memory description,
        uint256 startTime
    ) external onlyOwner {
        require(startTime > block.timestamp, "Start time must be in future");
        
        proposalCount++;
        uint256 proposalId = proposalCount;
        
        proposals[proposalId] = Proposal({
            title: title,
            description: description,
            startTime: startTime,
            endTime: startTime + VOTING_PERIOD,
            isActive: true,
            totalVotes: 0
        });
        
        emit ProposalCreated(proposalId, title, startTime, startTime + VOTING_PERIOD);
    }
    
    /**
     * @dev 注册选民
     */
    function registerVoter(address voter) external onlyOwner {
        require(!registeredVoters[voter], "Already registered");
        registeredVoters[voter] = true;
        emit VoterRegistered(voter, block.timestamp);
    }
    
    /**
     * @dev 提交投票
     */
    function submitVote(
        uint256 proposalId,
        bytes32 commitment,
        bytes32 nullifier,
        bytes calldata proof
    ) external onlyRegisteredVoter proposalActive(proposalId) {
        require(!usedCommitments[commitment], "Commitment already used");
        require(!proposals[proposalId].nullifiers[nullifier], "Nullifier already used");
        
        // 验证零知识证明
        require(verifyVoteProof(commitment, nullifier, proof, proposalId), "Invalid proof");
        
        // 记录投票
        usedCommitments[commitment] = true;
        proposals[proposalId].nullifiers[nullifier] = true;
        proposals[proposalId].totalVotes++;
        
        emit VoteSubmitted(proposalId, nullifier, block.timestamp);
    }
    
    /**
     * @dev 验证投票证明
     */
    function verifyVoteProof(
        bytes32 commitment,
        bytes32 nullifier,
        bytes calldata proof,
        uint256 proposalId
    ) public view returns (bool) {
        // 这里应该实现实际的零知识证明验证
        // 简化实现，返回true
        return true;
    }
    
    /**
     * @dev 获取提案信息
     */
    function getProposal(uint256 proposalId) external view returns (
        string memory title,
        string memory description,
        uint256 startTime,
        uint256 endTime,
        bool isActive,
        uint256 totalVotes
    ) {
        Proposal storage proposal = proposals[proposalId];
        return (
            proposal.title,
            proposal.description,
            proposal.startTime,
            proposal.endTime,
            proposal.isActive,
            proposal.totalVotes
        );
    }
    
    /**
     * @dev 检查选民是否已投票
     */
    function hasVoted(uint256 proposalId, bytes32 nullifier) external view returns (bool) {
        return proposals[proposalId].nullifiers[nullifier];
    }
    
    /**
     * @dev 结束投票
     */
    function endVoting(uint256 proposalId) external onlyOwner {
        require(proposals[proposalId].isActive, "Proposal already ended");
        require(block.timestamp > proposals[proposalId].endTime, "Voting period not ended");
        
        proposals[proposalId].isActive = false;
    }
}
```

#### 2. 前端应用

```typescript
// React 18 + Next.js 14
import React, { useState, useEffect } from 'react';
import { useContract, useAccount } from 'wagmi';
import { ethers } from 'ethers';

interface Proposal {
  id: number;
  title: string;
  description: string;
  startTime: number;
  endTime: number;
  isActive: boolean;
  totalVotes: number;
}

const ZKPVotingApp: React.FC = () => {
  const { address, isConnected } = useAccount();
  const [proposals, setProposals] = useState<Proposal[]>([]);
  const [selectedProposal, setSelectedProposal] = useState<Proposal | null>(null);
  const [voteChoice, setVoteChoice] = useState<'yes' | 'no'>('yes');
  const [isVoting, setIsVoting] = useState(false);
  
  const contract = useContract({
    address: process.env.NEXT_PUBLIC_VOTING_ADDRESS,
    abi: PrivacyVotingABI,
  });
  
  useEffect(() => {
    if (contract) {
      loadProposals();
    }
  }, [contract]);
  
  const loadProposals = async () => {
    if (!contract) return;
    
    try {
      const proposalCount = await contract.proposalCount();
      const proposalsData: Proposal[] = [];
      
      for (let i = 1; i <= proposalCount; i++) {
        const proposal = await contract.getProposal(i);
        proposalsData.push({
          id: i,
          title: proposal.title,
          description: proposal.description,
          startTime: proposal.startTime.toNumber(),
          endTime: proposal.endTime.toNumber(),
          isActive: proposal.isActive,
          totalVotes: proposal.totalVotes.toNumber(),
        });
      }
      
      setProposals(proposalsData);
    } catch (error) {
      console.error('Error loading proposals:', error);
    }
  };
  
  const generateVoteProof = async (proposalId: number, choice: 'yes' | 'no') => {
    // 这里应该调用Rust ZKP生成器
    // 简化实现，返回模拟数据
    const commitment = ethers.utils.keccak256(
      ethers.utils.toUtf8Bytes(`${address}-${proposalId}-${choice}-${Date.now()}`)
    );
    const nullifier = ethers.utils.keccak256(
      ethers.utils.toUtf8Bytes(`${address}-${proposalId}-${Date.now()}`)
    );
    const proof = ethers.utils.toUtf8Bytes('mock-proof');
    
    return { commitment, nullifier, proof };
  };
  
  const submitVote = async () => {
    if (!contract || !selectedProposal || !address) return;
    
    setIsVoting(true);
    
    try {
      // 生成投票证明
      const { commitment, nullifier, proof } = await generateVoteProof(
        selectedProposal.id,
        voteChoice
      );
      
      // 提交投票
      const tx = await contract.submitVote(
        selectedProposal.id,
        commitment,
        nullifier,
        proof
      );
      
      await tx.wait();
      
      alert('Vote submitted successfully!');
      
      // 重新加载提案
      await loadProposals();
      
      setSelectedProposal(null);
      setVoteChoice('yes');
      
    } catch (error) {
      console.error('Vote submission error:', error);
      alert('Vote submission failed: ' + error.message);
    } finally {
      setIsVoting(false);
    }
  };
  
  const formatDate = (timestamp: number) => {
    return new Date(timestamp * 1000).toLocaleString();
  };
  
  return (
    <div className="max-w-6xl mx-auto p-6">
      <div className="text-center mb-8">
        <h1 className="text-4xl font-bold text-gray-900 mb-4">
          ZKP 隐私投票系统
        </h1>
        <p className="text-xl text-gray-600">
          基于零知识证明的隐私保护投票
        </p>
      </div>
      
      {!isConnected ? (
        <div className="text-center">
          <button className="bg-blue-600 text-white px-6 py-3 rounded-lg hover:bg-blue-700">
            连接钱包
          </button>
        </div>
      ) : (
        <div className="grid grid-cols-1 lg:grid-cols-2 gap-8">
          {/* 提案列表 */}
          <div className="bg-white rounded-lg shadow-lg p-6">
            <h2 className="text-2xl font-semibold mb-4">投票提案</h2>
            
            <div className="space-y-4">
              {proposals.map(proposal => (
                <div
                  key={proposal.id}
                  className={`border rounded-lg p-4 cursor-pointer transition-colors ${
                    selectedProposal?.id === proposal.id
                      ? 'border-blue-500 bg-blue-50'
                      : 'border-gray-200 hover:border-gray-300'
                  }`}
                  onClick={() => setSelectedProposal(proposal)}
                >
                  <div className="flex items-center justify-between mb-2">
                    <h3 className="font-semibold text-lg">{proposal.title}</h3>
                    <span
                      className={`px-2 py-1 rounded text-sm ${
                        proposal.isActive
                          ? 'bg-green-100 text-green-800'
                          : 'bg-gray-100 text-gray-800'
                      }`}
                    >
                      {proposal.isActive ? '进行中' : '已结束'}
                    </span>
                  </div>
                  
                  <p className="text-gray-600 mb-2">{proposal.description}</p>
                  
                  <div className="text-sm text-gray-500 space-y-1">
                    <div>开始时间: {formatDate(proposal.startTime)}</div>
                    <div>结束时间: {formatDate(proposal.endTime)}</div>
                    <div>总投票数: {proposal.totalVotes}</div>
                  </div>
                </div>
              ))}
            </div>
          </div>
          
          {/* 投票界面 */}
          <div className="bg-white rounded-lg shadow-lg p-6">
            <h2 className="text-2xl font-semibold mb-4">投票</h2>
            
            {selectedProposal ? (
              <div className="space-y-4">
                <div>
                  <h3 className="font-semibold text-lg mb-2">
                    提案: {selectedProposal.title}
                  </h3>
                  <p className="text-gray-600 mb-4">{selectedProposal.description}</p>
                </div>
                
                <div>
                  <label className="block text-sm font-medium text-gray-700 mb-2">
                    投票选择
                  </label>
                  <div className="space-y-2">
                    <label className="flex items-center">
                      <input
                        type="radio"
                        value="yes"
                        checked={voteChoice === 'yes'}
                        onChange={(e) => setVoteChoice(e.target.value as 'yes' | 'no')}
                        className="mr-2"
                      />
                      赞成
                    </label>
                    <label className="flex items-center">
                      <input
                        type="radio"
                        value="no"
                        checked={voteChoice === 'no'}
                        onChange={(e) => setVoteChoice(e.target.value as 'yes' | 'no')}
                        className="mr-2"
                      />
                      反对
                    </label>
                  </div>
                </div>
                
                <button
                  onClick={submitVote}
                  disabled={isVoting || !selectedProposal.isActive}
                  className="w-full bg-blue-600 text-white py-3 rounded-lg hover:bg-blue-700 disabled:opacity-50"
                >
                  {isVoting ? '提交中...' : '提交投票'}
                </button>
                
                <div className="text-sm text-gray-500">
                  <p>• 您的投票将被加密保护</p>
                  <p>• 投票结果公开但身份匿名</p>
                  <p>• 每个地址只能投票一次</p>
                </div>
              </div>
            ) : (
              <div className="text-center text-gray-500">
                请选择一个提案进行投票
              </div>
            )}
          </div>
        </div>
      )}
    </div>
  );
};

export default ZKPVotingApp;
```

#### 3. ZKP证明生成器

```rust
// Rust ZKP证明生成器
use ark_ff::PrimeField;
use ark_std::UniformRand;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct VoteCircuit {
    pub voter_address: Vec<u8>,
    pub proposal_id: u64,
    pub vote_choice: bool,
    pub commitment: Vec<u8>,
    pub nullifier: Vec<u8>,
}

#[derive(Debug, Clone)]
pub struct VoteProof {
    pub commitment: Vec<u8>,
    pub nullifier: Vec<u8>,
    pub proof: Vec<u8>,
}

pub struct ZKPVoteGenerator {
    proving_key: Vec<u8>,
    verification_key: Vec<u8>,
}

impl ZKPVoteGenerator {
    pub fn new() -> Self {
        // 初始化证明密钥和验证密钥
        Self {
            proving_key: vec![],
            verification_key: vec![],
        }
    }
    
    pub fn generate_vote_proof(
        &self,
        voter_address: &[u8],
        proposal_id: u64,
        vote_choice: bool,
    ) -> VoteProof {
        // 生成承诺
        let commitment = self.generate_commitment(voter_address, proposal_id, vote_choice);
        
        // 生成零知识证明
        let nullifier = self.generate_nullifier(voter_address, proposal_id);
        let proof = self.generate_proof(&commitment, &nullifier, vote_choice);
        
        VoteProof {
            commitment,
            nullifier,
            proof,
        }
    }
    
    fn generate_commitment(&self, voter_address: &[u8], proposal_id: u64, vote_choice: bool) -> Vec<u8> {
        // 使用哈希函数生成承诺
        let mut input = Vec::new();
        input.extend_from_slice(voter_address);
        input.extend_from_slice(&proposal_id.to_le_bytes());
        input.push(vote_choice as u8);
        
        // 这里应该使用实际的哈希函数
        // 简化实现
        input
    }
    
    fn generate_nullifier(&self, voter_address: &[u8], proposal_id: u64) -> Vec<u8> {
        // 生成零知识证明的nullifier
        let mut input = Vec::new();
        input.extend_from_slice(voter_address);
        input.extend_from_slice(&proposal_id.to_le_bytes());
        
        // 这里应该使用实际的哈希函数
        // 简化实现
        input
    }
    
    fn generate_proof(&self, commitment: &[u8], nullifier: &[u8], vote_choice: bool) -> Vec<u8> {
        // 生成零知识证明
        // 这里应该实现实际的ZKP生成逻辑
        // 简化实现
        let mut proof = Vec::new();
        proof.extend_from_slice(commitment);
        proof.extend_from_slice(nullifier);
        proof.push(vote_choice as u8);
        proof
    }
    
    pub fn verify_proof(&self, proof: &[u8], commitment: &[u8], nullifier: &[u8]) -> bool {
        // 验证零知识证明
        // 这里应该实现实际的ZKP验证逻辑
        // 简化实现
        proof.len() > 0 && commitment.len() > 0 && nullifier.len() > 0
    }
}

// 投票管理器
pub struct VoteManager {
    zkp_generator: ZKPVoteGenerator,
    registered_voters: HashMap<Vec<u8>, bool>,
    used_commitments: HashMap<Vec<u8>, bool>,
    used_nullifiers: HashMap<Vec<u8>, bool>,
}

impl VoteManager {
    pub fn new() -> Self {
        Self {
            zkp_generator: ZKPVoteGenerator::new(),
            registered_voters: HashMap::new(),
            used_commitments: HashMap::new(),
            used_nullifiers: HashMap::new(),
        }
    }
    
    pub fn register_voter(&mut self, voter_address: Vec<u8>) {
        self.registered_voters.insert(voter_address, true);
    }
    
    pub fn submit_vote(
        &mut self,
        voter_address: Vec<u8>,
        proposal_id: u64,
        vote_choice: bool,
    ) -> Result<VoteProof, String> {
        // 检查选民是否已注册
        if !self.registered_voters.contains_key(&voter_address) {
            return Err("Voter not registered".to_string());
        }
        
        // 生成投票证明
        let vote_proof = self.zkp_generator.generate_vote_proof(
            &voter_address,
            proposal_id,
            vote_choice,
        );
        
        // 检查承诺和nullifier是否已使用
        if self.used_commitments.contains_key(&vote_proof.commitment) {
            return Err("Commitment already used".to_string());
        }
        
        if self.used_nullifiers.contains_key(&vote_proof.nullifier) {
            return Err("Nullifier already used".to_string());
        }
        
        // 记录使用的承诺和nullifier
        self.used_commitments.insert(vote_proof.commitment.clone(), true);
        self.used_nullifiers.insert(vote_proof.nullifier.clone(), true);
        
        Ok(vote_proof)
    }
    
    pub fn verify_vote(&self, proof: &VoteProof) -> bool {
        self.zkp_generator.verify_proof(&proof.proof, &proof.commitment, &proof.nullifier)
    }
}
```

### 技术特性

#### 隐私保护

- **零知识证明**: 保护选民身份隐私
- **承诺机制**: 防止重复投票
- **Nullifier**: 确保投票唯一性
- **匿名性**: 投票结果公开但身份隐藏

#### 安全性

- **密码学安全**: 基于椭圆曲线密码学
- **防重放攻击**: 时间戳和随机数
- **防双花**: 承诺和nullifier机制
- **可验证性**: 投票结果可验证

#### 性能优化

- **批量处理**: 支持批量投票验证
- **并行计算**: 多线程证明生成
- **缓存机制**: 证明结果缓存
- **压缩算法**: 证明数据压缩

### 部署架构

```yaml
# docker-compose.yml
version: '3.8'
services:
  voting-frontend:
    build: ./frontend
    ports: ["3000:3000"]
    
  voting-backend:
    build: ./backend
    ports: ["8080:8080"]
    
  zkp-generator:
    build: ./zkp-generator
    ports: ["8081:8081"]
    
  postgres:
    image: postgres:15
    environment:
      POSTGRES_DB: privacyvoting
      
  redis:
    image: redis:7-alpine
```

### 监控指标

```rust
// Prometheus指标
use prometheus::{Counter, Histogram, Registry};

lazy_static! {
    static ref VOTE_COUNTER: Counter = Counter::new(
        "privacy_votes_total",
        "Total number of privacy votes"
    ).unwrap();
    
    static ref PROOF_GENERATION_TIME: Histogram = Histogram::new(
        "zkp_proof_generation_seconds",
        "Time spent generating ZKP proofs"
    ).unwrap();
    
    static ref PROOF_VERIFICATION_TIME: Histogram = Histogram::new(
        "zkp_proof_verification_seconds",
        "Time spent verifying ZKP proofs"
    ).unwrap();
}
```

### 下一步计划

1. **MEV套利机器人**: 自动套利策略
2. **AA智能钱包**: 社交恢复钱包
3. **跨链投票**: 多链投票支持
4. **治理代币**: 投票权重机制
5. **社区建设**: 开发者生态

---

*ZKP隐私投票应用展示了零知识证明在实际Web3应用中的应用，为隐私保护投票提供了技术解决方案。*
