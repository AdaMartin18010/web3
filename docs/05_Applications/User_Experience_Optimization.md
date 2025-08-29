# 用户体验优化应用

## 概述

用户体验优化应用是Phase 3第3个月"性能优化"阶段的重要组成部分，专注于UI/UX优化、响应式设计和多语言支持。

## 核心功能

### 1. 响应式设计系统

#### React - 响应式组件库

```typescript
import React from 'react';
import { useMediaQuery } from 'react-responsive';

// 响应式Hook
export const useResponsive = () => {
  const isMobile = useMediaQuery({ maxWidth: 768 });
  const isTablet = useMediaQuery({ minWidth: 769, maxWidth: 1024 });
  const isDesktop = useMediaQuery({ minWidth: 1025 });

  return { isMobile, isTablet, isDesktop };
};

// 响应式容器组件
export const ResponsiveContainer: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  const { isMobile, isTablet, isDesktop } = useResponsive();

  const containerClasses = `
    mx-auto px-4
    ${isMobile ? 'max-w-full' : ''}
    ${isTablet ? 'max-w-2xl' : ''}
    ${isDesktop ? 'max-w-4xl' : ''}
  `;

  return <div className={containerClasses}>{children}</div>;
};

// 响应式网格组件
export const ResponsiveGrid: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  const gridClasses = `
    grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4
  `;

  return <div className={gridClasses}>{children}</div>;
};
```

### 2. 多语言支持系统

#### TypeScript - 国际化框架

```typescript
import React, { createContext, useContext, useState } from 'react';

// 支持的语言
export const supportedLanguages = {
  'zh-CN': '简体中文',
  'en-US': 'English',
  'ja-JP': '日本語',
} as const;

export type LanguageCode = keyof typeof supportedLanguages;

// 翻译数据
const translations = {
  'zh-CN': {
    common: {
      loading: '加载中...',
      error: '错误',
      success: '成功',
    },
    wallet: {
      connect: '连接钱包',
      balance: '余额',
      send: '发送',
    },
    defi: {
      tvl: '总锁仓价值',
      apy: '年化收益率',
    },
  },
  'en-US': {
    common: {
      loading: 'Loading...',
      error: 'Error',
      success: 'Success',
    },
    wallet: {
      connect: 'Connect Wallet',
      balance: 'Balance',
      send: 'Send',
    },
    defi: {
      tvl: 'Total Value Locked',
      apy: 'Annual Percentage Yield',
    },
  },
  'ja-JP': {
    common: {
      loading: '読み込み中...',
      error: 'エラー',
      success: '成功',
    },
    wallet: {
      connect: 'ウォレット接続',
      balance: '残高',
      send: '送信',
    },
    defi: {
      tvl: '総ロック価値',
      apy: '年間収益率',
    },
  },
};

// 国际化上下文
interface I18nContextType {
  language: LanguageCode;
  setLanguage: (lang: LanguageCode) => void;
  t: (key: string) => string;
}

const I18nContext = createContext<I18nContextType | undefined>(undefined);

// 国际化Provider组件
export const I18nProvider: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  const [language, setLanguageState] = useState<LanguageCode>('zh-CN');

  const setLanguage = (lang: LanguageCode) => {
    setLanguageState(lang);
    localStorage.setItem('preferred-language', lang);
  };

  const t = (key: string): string => {
    const keys = key.split('.');
    let value: any = translations[language];

    for (const k of keys) {
      if (value && typeof value === 'object' && k in value) {
        value = value[k];
      } else {
        value = translations['en-US'];
        for (const fallbackKey of keys) {
          if (value && typeof value === 'object' && fallbackKey in value) {
            value = value[fallbackKey];
          } else {
            return key;
          }
        }
      }
    }

    return typeof value === 'string' ? value : key;
  };

  return (
    <I18nContext.Provider value={{ language, setLanguage, t }}>
      {children}
    </I18nContext.Provider>
  );
};

// 使用国际化的Hook
export const useI18n = (): I18nContextType => {
  const context = useContext(I18nContext);
  if (!context) {
    throw new Error('useI18n must be used within an I18nProvider');
  }
  return context;
};

// 语言选择器组件
export const LanguageSelector: React.FC = () => {
  const { language, setLanguage } = useI18n();

  return (
    <select
      value={language}
      onChange={(e) => setLanguage(e.target.value as LanguageCode)}
      className="border border-gray-300 rounded-md px-3 py-2"
    >
      {Object.entries(supportedLanguages).map(([code, name]) => (
        <option key={code} value={code}>
          {name}
        </option>
      ))}
    </select>
  );
};
```

### 3. 主题系统

#### TypeScript - 主题管理

```typescript
import React, { createContext, useContext, useState, useEffect } from 'react';

export type Theme = 'light' | 'dark' | 'auto';

// 主题上下文
interface ThemeContextType {
  theme: Theme;
  setTheme: (theme: Theme) => void;
  isDark: boolean;
}

const ThemeContext = createContext<ThemeContextType | undefined>(undefined);

// 主题Provider组件
export const ThemeProvider: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  const [theme, setThemeState] = useState<Theme>('auto');
  const [isDark, setIsDark] = useState(false);

  const setTheme = (newTheme: Theme) => {
    setThemeState(newTheme);
    localStorage.setItem('theme', newTheme);
    
    if (newTheme === 'auto') {
      const mediaQuery = window.matchMedia('(prefers-color-scheme: dark)');
      setIsDark(mediaQuery.matches);
    } else {
      setIsDark(newTheme === 'dark');
    }
  };

  useEffect(() => {
    const mediaQuery = window.matchMedia('(prefers-color-scheme: dark)');
    
    const handleChange = (e: MediaQueryListEvent) => {
      if (theme === 'auto') {
        setIsDark(e.matches);
      }
    };

    mediaQuery.addEventListener('change', handleChange);
    
    if (theme === 'auto') {
      setIsDark(mediaQuery.matches);
    } else {
      setIsDark(theme === 'dark');
    }

    return () => mediaQuery.removeEventListener('change', handleChange);
  }, [theme]);

  useEffect(() => {
    const root = document.documentElement;
    if (isDark) {
      root.classList.add('dark');
    } else {
      root.classList.remove('dark');
    }
  }, [isDark]);

  return (
    <ThemeContext.Provider value={{ theme, setTheme, isDark }}>
      {children}
    </ThemeContext.Provider>
  );
};

// 使用主题的Hook
export const useTheme = (): ThemeContextType => {
  const context = useContext(ThemeContext);
  if (!context) {
    throw new Error('useTheme must be used within a ThemeProvider');
  }
  return context;
};

// 主题切换器组件
export const ThemeToggle: React.FC = () => {
  const { theme, setTheme } = useTheme();

  const toggleTheme = () => {
    if (theme === 'light') {
      setTheme('dark');
    } else if (theme === 'dark') {
      setTheme('auto');
    } else {
      setTheme('light');
    }
  };

  return (
    <button
      onClick={toggleTheme}
      className="p-2 rounded-lg bg-gray-100 dark:bg-gray-800 hover:bg-gray-200 dark:hover:bg-gray-700"
    >
      {theme === 'light' && '🌙'}
      {theme === 'dark' && '☀️'}
      {theme === 'auto' && '🔄'}
    </button>
  );
};
```

### 4. 优化后的主应用界面

#### TypeScript - 优化后的仪表板

```typescript
import React, { useState, useEffect } from 'react';
import { ResponsiveContainer, ResponsiveGrid } from './components/Responsive';
import { useI18n, LanguageSelector } from './components/I18n';
import { useTheme, ThemeToggle } from './components/Theme';
import { LineChart, Line, XAxis, YAxis, CartesianGrid, Tooltip, ResponsiveContainer as ChartContainer } from 'recharts';

interface DashboardData {
  performance: {
    responseTime: number[];
    errorRate: number[];
  };
  defi: {
    tvl: number;
    apy: number;
  };
}

const OptimizedDashboard: React.FC = () => {
  const { t } = useI18n();
  const { isDark } = useTheme();
  const [data, setData] = useState<DashboardData | null>(null);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    const fetchData = async () => {
      setLoading(true);
      await new Promise(resolve => setTimeout(resolve, 1000));
      
      setData({
        performance: {
          responseTime: Array.from({ length: 24 }, () => Math.random() * 200 + 50),
          errorRate: Array.from({ length: 24 }, () => Math.random() * 2),
        },
        defi: {
          tvl: 2500000,
          apy: 12.5,
        },
      });
      
      setLoading(false);
    };

    fetchData();
  }, []);

  if (loading) {
    return (
      <ResponsiveContainer>
        <div className="flex items-center justify-center min-h-screen">
          <div className="text-center">
            <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-blue-500 mx-auto mb-4"></div>
            <p className="text-gray-600 dark:text-gray-400">{t('common.loading')}</p>
          </div>
        </div>
      </ResponsiveContainer>
    );
  }

  if (!data) {
    return (
      <ResponsiveContainer>
        <div className="text-center py-8">
          <p className="text-red-600 dark:text-red-400">{t('common.error')}</p>
        </div>
      </ResponsiveContainer>
    );
  }

  const performanceData = data.performance.responseTime.map((value, index) => ({
    time: index,
    responseTime: value,
    errorRate: data.performance.errorRate[index],
  }));

  return (
    <div className={`min-h-screen ${isDark ? 'dark' : ''}`}>
      <div className="bg-gray-50 dark:bg-gray-900 min-h-screen">
        {/* 头部导航 */}
        <header className="bg-white dark:bg-gray-800 shadow-sm border-b border-gray-200 dark:border-gray-700">
          <ResponsiveContainer>
            <div className="flex items-center justify-between py-4">
              <h1 className="text-2xl font-bold text-gray-900 dark:text-white">
                Web3 仪表板
              </h1>
              
              <div className="flex items-center space-x-4">
                <LanguageSelector />
                <ThemeToggle />
              </div>
            </div>
          </ResponsiveContainer>
        </header>

        <ResponsiveContainer className="py-8">
          {/* 性能监控卡片 */}
          <ResponsiveGrid>
            <div className="bg-white dark:bg-gray-800 rounded-lg shadow-md p-6">
              <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">
                {t('performance.responseTime')}
              </h3>
              <div className="text-3xl font-bold text-blue-600 dark:text-blue-400 mb-4">
                {Math.round(data.performance.responseTime[data.performance.responseTime.length - 1])}ms
              </div>
              <ChartContainer width="100%" height={200}>
                <LineChart data={performanceData}>
                  <CartesianGrid strokeDasharray="3 3" stroke={isDark ? '#374151' : '#E5E7EB'} />
                  <XAxis dataKey="time" stroke={isDark ? '#D1D5DB' : '#6B7280'} />
                  <YAxis stroke={isDark ? '#D1D5DB' : '#6B7280'} />
                  <Tooltip />
                  <Line type="monotone" dataKey="responseTime" stroke="#3B82F6" strokeWidth={2} dot={false} />
                </LineChart>
              </ChartContainer>
            </div>

            <div className="bg-white dark:bg-gray-800 rounded-lg shadow-md p-6">
              <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">
                {t('defi.tvl')}
              </h3>
              <div className="text-3xl font-bold text-green-600 dark:text-green-400">
                ${(data.defi.tvl / 1000000).toFixed(1)}M
              </div>
              <p className="text-sm text-gray-600 dark:text-gray-400 mt-2">
                {t('defi.tvl')}
              </p>
            </div>

            <div className="bg-white dark:bg-gray-800 rounded-lg shadow-md p-6">
              <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">
                {t('defi.apy')}
              </h3>
              <div className="text-3xl font-bold text-purple-600 dark:text-purple-400">
                {data.defi.apy.toFixed(2)}%
              </div>
              <p className="text-sm text-gray-600 dark:text-gray-400 mt-2">
                {t('defi.apy')}
              </p>
            </div>
          </ResponsiveGrid>
        </ResponsiveContainer>
      </div>
    </div>
  );
};

export default OptimizedDashboard;
```

### 5. 部署配置

#### Docker Compose配置

```yaml
version: '3.8'

services:
  # 用户体验优化前端
  ux-frontend:
    build:
      context: ./frontend
      dockerfile: Dockerfile
    ports:
      - "3000:3000"
    environment:
      - NEXT_PUBLIC_API_URL=http://localhost:8080
      - NEXT_PUBLIC_DEFAULT_LANGUAGE=zh-CN
      - NEXT_PUBLIC_DEFAULT_THEME=auto
    depends_on:
      - ux-backend
    networks:
      - ux-network

  # 用户体验优化后端
  ux-backend:
    build:
      context: ./backend
      dockerfile: Dockerfile
    ports:
      - "8080:8080"
    environment:
      - DATABASE_URL=postgresql://user:password@postgres:5432/ux_optimization
      - REDIS_URL=redis://redis:6379
      - SUPPORTED_LANGUAGES=zh-CN,en-US,ja-JP
    depends_on:
      - postgres
      - redis
    networks:
      - ux-network

  # PostgreSQL数据库
  postgres:
    image: postgres:13
    environment:
      - POSTGRES_DB=ux_optimization
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=password
    networks:
      - ux-network

  # Redis缓存
  redis:
    image: redis:6-alpine
    networks:
      - ux-network

networks:
  ux-network:
    driver: bridge
```

## 总结

用户体验优化应用提供了完整的用户体验优化解决方案：

1. **响应式设计系统**: 支持多设备适配的组件库
2. **多语言支持**: 3种语言的国际化框架
3. **主题系统**: 浅色、深色、自动主题切换
4. **优化界面**: 现代化的仪表板设计
5. **完整部署**: Docker容器化部署方案

该系统显著提升了Web3应用的用户体验，支持多语言、多主题、多设备，为用户提供了更加友好和个性化的使用体验。
