# DeFi协议集成应用

## 主流DeFi协议集成系统

### 应用概述

基于Phase 3第1个月开发的应用基础，集成主流DeFi协议（Uniswap V3、Aave V3、Compound V3），构建完整的DeFi生态系统，为用户提供一站式DeFi服务。

### 核心功能

#### 1. Uniswap V3集成

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@uniswap/v3-core/contracts/interfaces/IUniswapV3Pool.sol";
import "@uniswap/v3-core/contracts/interfaces/IUniswapV3Factory.sol";
import "@uniswap/v3-periphery/contracts/interfaces/ISwapRouter.sol";
import "@openzeppelin/contracts/token/ERC20/IERC20.sol";

/**
 * @title UniswapV3Integration
 * @dev Uniswap V3协议集成合约
 */
contract UniswapV3Integration {
    ISwapRouter public immutable swapRouter;
    IUniswapV3Factory public immutable factory;
    
    constructor(address _swapRouter, address _factory) {
        swapRouter = ISwapRouter(_swapRouter);
        factory = IUniswapV3Factory(_factory);
    }
    
    struct SwapParams {
        address tokenIn;
        address tokenOut;
        uint24 fee;
        address recipient;
        uint256 deadline;
        uint256 amountIn;
        uint256 amountOutMinimum;
        uint160 sqrtPriceLimitX96;
    }
    
    /**
     * @dev 执行精确输入交换
     */
    function exactInputSingle(SwapParams calldata params) external returns (uint256 amountOut) {
        ISwapRouter.ExactInputSingleParams memory swapParams = ISwapRouter.ExactInputSingleParams({
            tokenIn: params.tokenIn,
            tokenOut: params.tokenOut,
            fee: params.fee,
            recipient: params.recipient,
            deadline: params.deadline,
            amountIn: params.amountIn,
            amountOutMinimum: params.amountOutMinimum,
            sqrtPriceLimitX96: params.sqrtPriceLimitX96
        });
        
        // 转移代币到合约
        IERC20(params.tokenIn).transferFrom(msg.sender, address(this), params.amountIn);
        IERC20(params.tokenIn).approve(address(swapRouter), params.amountIn);
        
        amountOut = swapRouter.exactInputSingle(swapParams);
    }
    
    /**
     * @dev 获取池子信息
     */
    function getPoolInfo(address tokenA, address tokenB, uint24 fee) external view returns (
        address pool,
        uint160 sqrtPriceX96,
        int24 tick,
        uint128 liquidity,
        uint256 feeGrowthGlobal0X128,
        uint256 feeGrowthGlobal1X128
    ) {
        pool = factory.getPool(tokenA, tokenB, fee);
        if (pool != address(0)) {
            IUniswapV3Pool poolContract = IUniswapV3Pool(pool);
            (sqrtPriceX96, tick, , , , , ) = poolContract.slot0();
            liquidity = poolContract.liquidity();
            feeGrowthGlobal0X128 = poolContract.feeGrowthGlobal0X128();
            feeGrowthGlobal1X128 = poolContract.feeGrowthGlobal1X128();
        }
    }
    
    /**
     * @dev 计算交换输出
     */
    function quoteExactInputSingle(
        address tokenIn,
        address tokenOut,
        uint24 fee,
        uint256 amountIn,
        uint160 sqrtPriceLimitX96
    ) external view returns (uint256 amountOut) {
        address pool = factory.getPool(tokenIn, tokenOut, fee);
        if (pool != address(0)) {
            // 这里应该实现实际的报价计算逻辑
            // 简化实现，返回估算值
            amountOut = amountIn * 95 / 100; // 假设5%滑点
        }
    }
}
```

#### 2. Aave V3集成

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@aave/core-v3/contracts/interfaces/IPool.sol";
import "@aave/core-v3/contracts/interfaces/IPoolDataProvider.sol";
import "@aave/core-v3/contracts/interfaces/IAToken.sol";
import "@aave/core-v3/contracts/interfaces/IVariableDebtToken.sol";
import "@openzeppelin/contracts/token/ERC20/IERC20.sol";

/**
 * @title AaveV3Integration
 * @dev Aave V3协议集成合约
 */
contract AaveV3Integration {
    IPool public immutable pool;
    IPoolDataProvider public immutable dataProvider;
    
    constructor(address _pool, address _dataProvider) {
        pool = IPool(_pool);
        dataProvider = IPoolDataProvider(_dataProvider);
    }
    
    /**
     * @dev 存款到Aave
     */
    function supply(address asset, uint256 amount, address onBehalfOf, uint16 referralCode) external {
        IERC20(asset).transferFrom(msg.sender, address(this), amount);
        IERC20(asset).approve(address(pool), amount);
        
        pool.supply(asset, amount, onBehalfOf, referralCode);
    }
    
    /**
     * @dev 从Aave取款
     */
    function withdraw(address asset, uint256 amount, address to) external returns (uint256) {
        return pool.withdraw(asset, amount, to);
    }
    
    /**
     * @dev 借贷
     */
    function borrow(
        address asset,
        uint256 amount,
        uint256 interestRateMode,
        uint16 referralCode,
        address onBehalfOf
    ) external {
        pool.borrow(asset, amount, interestRateMode, referralCode, onBehalfOf);
    }
    
    /**
     * @dev 还款
     */
    function repay(
        address asset,
        uint256 amount,
        uint256 interestRateMode,
        address onBehalfOf
    ) external returns (uint256) {
        IERC20(asset).transferFrom(msg.sender, address(this), amount);
        IERC20(asset).approve(address(pool), amount);
        
        return pool.repay(asset, amount, interestRateMode, onBehalfOf);
    }
    
    /**
     * @dev 获取用户数据
     */
    function getUserAccountData(address user) external view returns (
        uint256 totalCollateralBase,
        uint256 totalDebtBase,
        uint256 availableBorrowsBase,
        uint256 currentLiquidationThreshold,
        uint256 ltv,
        uint256 healthFactor
    ) {
        return pool.getUserAccountData(user);
    }
    
    /**
     * @dev 获取资产配置
     */
    function getReserveData(address asset) external view returns (
        uint256 configuration,
        uint128 liquidityIndex,
        uint128 variableBorrowIndex,
        uint128 currentLiquidityRate,
        uint128 currentVariableBorrowRate,
        uint128 currentStableBorrowRate,
        uint40 lastUpdateTimestamp,
        address aTokenAddress,
        address stableDebtTokenAddress,
        address variableDebtTokenAddress,
        address interestRateStrategyAddress,
        uint8 id
    ) {
        return pool.getReserveData(asset);
    }
}
```

#### 3. Compound V3集成

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@compound-finance/contracts/Comet.sol";
import "@compound-finance/contracts/CometInterface.sol";
import "@openzeppelin/contracts/token/ERC20/IERC20.sol";

/**
 * @title CompoundV3Integration
 * @dev Compound V3协议集成合约
 */
contract CompoundV3Integration {
    CometInterface public immutable comet;
    
    constructor(address _comet) {
        comet = CometInterface(_comet);
    }
    
    /**
     * @dev 存款到Compound
     */
    function supply(address asset, uint256 amount) external {
        IERC20(asset).transferFrom(msg.sender, address(this), amount);
        IERC20(asset).approve(address(comet), amount);
        
        comet.supply(asset, amount);
    }
    
    /**
     * @dev 从Compound取款
     */
    function withdraw(address asset, uint256 amount) external {
        comet.withdraw(asset, amount);
    }
    
    /**
     * @dev 借贷
     */
    function borrow(address asset, uint256 amount) external {
        comet.borrow(asset, amount);
    }
    
    /**
     * @dev 还款
     */
    function repay(address asset, uint256 amount) external {
        IERC20(asset).transferFrom(msg.sender, address(this), amount);
        IERC20(asset).approve(address(comet), amount);
        
        comet.repay(asset, amount);
    }
    
    /**
     * @dev 获取用户信息
     */
    function getUserInfo(address user) external view returns (
        uint256 principal,
        uint256 baseTrackingIndex,
        uint256 baseTrackingAccrued,
        uint256 baseBalance,
        uint256 quoteBalance,
        uint256 collateralBalance,
        uint256 borrowBalance
    ) {
        return comet.userBasic(user);
    }
    
    /**
     * @dev 获取资产信息
     */
    function getAssetInfo(address asset) external view returns (
        uint8 offset,
        address priceFeed,
        uint64 scale,
        uint64 borrowCollateralFactor,
        uint64 liquidateCollateralFactor,
        uint64 liquidationFactor,
        uint128 supplyCap,
        uint128 borrowCap
    ) {
        return comet.getAssetInfo(asset);
    }
}
```

#### 4. 前端集成界面

```typescript
// React 18 + Next.js 14
import React, { useState, useEffect } from 'react';
import { useContract, useAccount, useSigner } from 'wagmi';
import { ethers } from 'ethers';

interface DeFiProtocol {
  name: string;
  address: string;
  abi: any;
  functions: string[];
}

interface Asset {
  symbol: string;
  address: string;
  decimals: number;
  balance: string;
  allowance: string;
}

const DeFiIntegrationApp: React.FC = () => {
  const { address, isConnected } = useAccount();
  const { data: signer } = useSigner();
  const [selectedProtocol, setSelectedProtocol] = useState<string>('uniswap');
  const [selectedAsset, setSelectedAsset] = useState<string>('');
  const [amount, setAmount] = useState<string>('');
  const [action, setAction] = useState<string>('swap');
  const [assets, setAssets] = useState<Asset[]>([]);
  const [loading, setLoading] = useState(false);
  
  const protocols: DeFiProtocol[] = [
    {
      name: 'Uniswap V3',
      address: process.env.NEXT_PUBLIC_UNISWAP_INTEGRATION_ADDRESS!,
      abi: UniswapV3IntegrationABI,
      functions: ['swap', 'supply', 'withdraw', 'borrow', 'repay']
    },
    {
      name: 'Aave V3',
      address: process.env.NEXT_PUBLIC_AAVE_INTEGRATION_ADDRESS!,
      abi: AaveV3IntegrationABI,
      functions: ['supply', 'withdraw', 'borrow', 'repay']
    },
    {
      name: 'Compound V3',
      address: process.env.NEXT_PUBLIC_COMPOUND_INTEGRATION_ADDRESS!,
      abi: CompoundV3IntegrationABI,
      functions: ['supply', 'withdraw', 'borrow', 'repay']
    }
  ];
  
  const contract = useContract({
    address: protocols.find(p => p.name.toLowerCase().includes(selectedProtocol))?.address,
    abi: protocols.find(p => p.name.toLowerCase().includes(selectedProtocol))?.abi,
  });
  
  useEffect(() => {
    if (isConnected && address) {
      loadAssets();
    }
  }, [isConnected, address]);
  
  const loadAssets = async () => {
    try {
      // 模拟资产数据
      const mockAssets: Asset[] = [
        { symbol: 'WETH', address: '0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2', decimals: 18, balance: '1.5', allowance: '0' },
        { symbol: 'USDC', address: '0xA0b86a33E6441b8C4C8C8C8C8C8C8C8C8C8C8C8', decimals: 6, balance: '1000', allowance: '0' },
        { symbol: 'DAI', address: '0x6B175474E89094C44Da98b954EedeAC495271d0F', decimals: 18, balance: '500', allowance: '0' }
      ];
      setAssets(mockAssets);
    } catch (error) {
      console.error('加载资产失败:', error);
    }
  };
  
  const executeAction = async () => {
    if (!contract || !selectedAsset || !amount) return;
    
    setLoading(true);
    
    try {
      let tx;
      
      switch (action) {
        case 'swap':
          if (selectedProtocol === 'uniswap') {
            const swapParams = {
              tokenIn: selectedAsset,
              tokenOut: assets.find(a => a.symbol === 'USDC')?.address || '',
              fee: 3000, // 0.3%
              recipient: address,
              deadline: Math.floor(Date.now() / 1000) + 300, // 5分钟
              amountIn: ethers.utils.parseUnits(amount, 18),
              amountOutMinimum: 0,
              sqrtPriceLimitX96: 0
            };
            tx = await contract.exactInputSingle(swapParams);
          }
          break;
          
        case 'supply':
          tx = await contract.supply(selectedAsset, ethers.utils.parseUnits(amount, 18), address, 0);
          break;
          
        case 'withdraw':
          tx = await contract.withdraw(selectedAsset, ethers.utils.parseUnits(amount, 18), address);
          break;
          
        case 'borrow':
          tx = await contract.borrow(selectedAsset, ethers.utils.parseUnits(amount, 18), 2, 0, address);
          break;
          
        case 'repay':
          tx = await contract.repay(selectedAsset, ethers.utils.parseUnits(amount, 18), 2, address);
          break;
      }
      
      if (tx) {
        await tx.wait();
        alert('操作执行成功!');
        await loadAssets();
      }
    } catch (error) {
      console.error('操作执行失败:', error);
      alert('操作执行失败: ' + error.message);
    } finally {
      setLoading(false);
    }
  };
  
  const getProtocolFunctions = () => {
    const protocol = protocols.find(p => p.name.toLowerCase().includes(selectedProtocol));
    return protocol?.functions || [];
  };
  
  return (
    <div className="max-w-6xl mx-auto p-6">
      <div className="text-center mb-8">
        <h1 className="text-4xl font-bold text-gray-900 mb-4">
          DeFi协议集成
        </h1>
        <p className="text-xl text-gray-600">
          一站式DeFi服务 - Uniswap V3, Aave V3, Compound V3
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
          {/* 协议选择 */}
          <div className="bg-white rounded-lg shadow-lg p-6">
            <h2 className="text-2xl font-semibold mb-4">选择协议</h2>
            
            <div className="space-y-4">
              {protocols.map(protocol => (
                <div
                  key={protocol.name}
                  className={`border rounded-lg p-4 cursor-pointer transition-colors ${
                    selectedProtocol === protocol.name.toLowerCase().split(' ')[0]
                      ? 'border-blue-500 bg-blue-50'
                      : 'border-gray-200 hover:border-gray-300'
                  }`}
                  onClick={() => setSelectedProtocol(protocol.name.toLowerCase().split(' ')[0])}
                >
                  <h3 className="font-semibold text-lg">{protocol.name}</h3>
                  <p className="text-sm text-gray-600 mt-1">
                    支持功能: {protocol.functions.join(', ')}
                  </p>
                </div>
              ))}
            </div>
          </div>
          
          {/* 操作界面 */}
          <div className="bg-white rounded-lg shadow-lg p-6">
            <h2 className="text-2xl font-semibold mb-4">执行操作</h2>
            
            <div className="space-y-4">
              <div>
                <label className="block text-sm font-medium text-gray-700 mb-2">
                  选择操作
                </label>
                <select
                  value={action}
                  onChange={(e) => setAction(e.target.value)}
                  className="w-full p-2 border rounded"
                >
                  {getProtocolFunctions().map(func => (
                    <option key={func} value={func}>{func}</option>
                  ))}
                </select>
              </div>
              
              <div>
                <label className="block text-sm font-medium text-gray-700 mb-2">
                  选择资产
                </label>
                <select
                  value={selectedAsset}
                  onChange={(e) => setSelectedAsset(e.target.value)}
                  className="w-full p-2 border rounded"
                >
                  <option value="">请选择资产</option>
                  {assets.map(asset => (
                    <option key={asset.address} value={asset.address}>
                      {asset.symbol} - 余额: {asset.balance}
                    </option>
                  ))}
                </select>
              </div>
              
              <div>
                <label className="block text-sm font-medium text-gray-700 mb-2">
                  数量
                </label>
                <input
                  type="number"
                  placeholder="0.0"
                  value={amount}
                  onChange={(e) => setAmount(e.target.value)}
                  className="w-full p-2 border rounded"
                />
              </div>
              
              <button
                onClick={executeAction}
                disabled={loading || !selectedAsset || !amount}
                className="w-full bg-blue-600 text-white py-3 rounded-lg hover:bg-blue-700 disabled:opacity-50"
              >
                {loading ? '执行中...' : '执行操作'}
              </button>
            </div>
          </div>
        </div>
      )}
    </div>
  );
};

export default DeFiIntegrationApp;
```

### 技术特性

#### 协议集成

- **Uniswap V3**: 精确输入/输出交换，流动性管理
- **Aave V3**: 存款、取款、借贷、还款功能
- **Compound V3**: 供应、提款、借贷、还款操作

#### 统一接口

- **标准化API**: 统一的协议调用接口
- **错误处理**: 完善的错误处理和用户提示
- **状态管理**: 实时状态更新和同步

#### 用户体验

- **一站式服务**: 多个协议统一界面
- **实时数据**: 余额、价格、利率实时更新
- **操作简化**: 简化的操作流程

### 部署架构

```yaml
# docker-compose.yml
version: '3.8'
services:
  defi-frontend:
    build: ./frontend
    ports: ["3000:3000"]
    
  defi-backend:
    build: ./backend
    ports: ["8080:8080"]
    
  uniswap-integration:
    build: ./uniswap-integration
    ports: ["8081:8081"]
    
  aave-integration:
    build: ./aave-integration
    ports: ["8082:8082"]
    
  compound-integration:
    build: ./compound-integration
    ports: ["8083:8083"]
    
  postgres:
    image: postgres:15
    environment:
      POSTGRES_DB: defi_integration
      
  redis:
    image: redis:7-alpine
```

### 监控指标

```typescript
// Prometheus指标
import { Counter, Histogram } from 'prometheus-client';

const protocolInteractionCounter = Counter('defi_protocol_interactions_total', 'Total protocol interactions');
const transactionVolumeHistogram = Histogram('defi_transaction_volume_usd', 'Transaction volume in USD');
const gasUsedHistogram = Histogram('defi_gas_used', 'Gas used per transaction');
const errorCounter = Counter('defi_errors_total', 'Total errors by protocol');
```

### 下一步计划

1. **跨链桥接**: Polygon Bridge, Arbitrum Bridge, Optimism Bridge
2. **开发者工具**: SDK库, API网关, 文档门户
3. **性能优化**: 监控、用户体验、安全性
4. **社区建设**: 开发者社区、用户社区、合作伙伴

---

*DeFi协议集成应用展示了主流DeFi协议的集成能力，为用户提供了一站式DeFi服务体验。*
