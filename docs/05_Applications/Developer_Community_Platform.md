# 开发者社区平台应用

## 概述

开发者社区平台是Phase 3第4个月"社区建设"阶段的核心应用，提供技术论坛、开发者文档和代码示例库。

## 核心功能

### 1. 技术论坛系统

#### TypeScript - 论坛前端应用
```typescript
import React, { useState } from 'react';
import { useQuery, useMutation } from '@tanstack/react-query';

interface ForumPost {
  id: string;
  title: string;
  content: string;
  author: {
    name: string;
    avatar: string;
    reputation: number;
  };
  category: string;
  tags: string[];
  createdAt: string;
  viewCount: number;
  replyCount: number;
  likes: number;
}

const ForumApp: React.FC = () => {
  const [selectedCategory, setSelectedCategory] = useState<string>('all');
  const [searchQuery, setSearchQuery] = useState<string>('');

  const { data: posts, isLoading } = useQuery({
    queryKey: ['forum-posts', selectedCategory, searchQuery],
    queryFn: async () => {
      const response = await fetch(`/api/forum/posts?category=${selectedCategory}&search=${searchQuery}`);
      return response.json();
    },
  });

  const categories = [
    { id: 'all', name: '全部', icon: '📚' },
    { id: 'solidity', name: 'Solidity开发', icon: '🔷' },
    { id: 'react', name: 'React前端', icon: '⚛️' },
    { id: 'defi', name: 'DeFi协议', icon: '💰' },
    { id: 'layer2', name: 'Layer2技术', icon: '⚡' },
    { id: 'security', name: '安全审计', icon: '🔒' },
  ];

  return (
    <div className="min-h-screen bg-gray-50">
      <div className="max-w-7xl mx-auto px-4 py-8">
        <header className="bg-white rounded-lg shadow-sm p-6 mb-8">
          <div className="flex items-center justify-between">
            <h1 className="text-3xl font-bold text-gray-900">Web3开发者论坛</h1>
            <input
              type="text"
              placeholder="搜索帖子..."
              value={searchQuery}
              onChange={(e) => setSearchQuery(e.target.value)}
              className="px-4 py-2 border border-gray-300 rounded-lg"
            />
          </div>
        </header>

        <div className="grid grid-cols-1 lg:grid-cols-4 gap-8">
          <div className="lg:col-span-1">
            <div className="bg-white rounded-lg shadow-sm p-6">
              <h2 className="text-lg font-semibold text-gray-900 mb-4">分类</h2>
              <nav className="space-y-2">
                {categories.map((category) => (
                  <button
                    key={category.id}
                    onClick={() => setSelectedCategory(category.id)}
                    className={`w-full flex items-center space-x-3 px-3 py-2 rounded-lg text-left ${
                      selectedCategory === category.id
                        ? 'bg-blue-100 text-blue-700'
                        : 'hover:bg-gray-100 text-gray-700'
                    }`}
                  >
                    <span className="text-lg">{category.icon}</span>
                    <span>{category.name}</span>
                  </button>
                ))}
              </nav>
            </div>
          </div>

          <div className="lg:col-span-3">
            <div className="bg-white rounded-lg shadow-sm">
              {isLoading ? (
                <div className="p-8 text-center">
                  <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-blue-600 mx-auto"></div>
                </div>
              ) : (
                <div className="divide-y divide-gray-200">
                  {posts?.map((post: ForumPost) => (
                    <article key={post.id} className="p-6 hover:bg-gray-50">
                      <div className="flex items-start space-x-4">
                        <img
                          src={post.author.avatar}
                          alt={post.author.name}
                          className="w-12 h-12 rounded-full"
                        />
                        <div className="flex-1">
                          <h3 className="text-lg font-semibold text-gray-900 mb-2">
                            {post.title}
                          </h3>
                          <p className="text-gray-600 text-sm mb-3">{post.content}</p>
                          <div className="flex items-center justify-between text-sm text-gray-500">
                            <span>作者: {post.author.name}</span>
                            <div className="flex items-center space-x-4">
                              <span>👁️ {post.viewCount}</span>
                              <span>💬 {post.replyCount}</span>
                              <span>👍 {post.likes}</span>
                            </div>
                          </div>
                        </div>
                      </div>
                    </article>
                  ))}
                </div>
              )}
            </div>
          </div>
        </div>
      </div>
    </div>
  );
};

export default ForumApp;
```

### 2. 开发者文档系统

#### TypeScript - 文档管理系统
```typescript
import React, { useState } from 'react';
import { useQuery } from '@tanstack/react-query';
import { marked } from 'marked';

interface Documentation {
  id: string;
  title: string;
  content: string;
  category: string;
  author: string;
  version: string;
  viewCount: number;
  rating: number;
}

const DocumentationApp: React.FC = () => {
  const [selectedCategory, setSelectedCategory] = useState<string>('getting-started');
  const [selectedDoc, setSelectedDoc] = useState<string>('');

  const { data: docs } = useQuery({
    queryKey: ['documentation', selectedCategory],
    queryFn: async () => {
      const response = await fetch(`/api/documentation/docs?category=${selectedCategory}`);
      return response.json();
    },
  });

  const { data: currentDoc } = useQuery({
    queryKey: ['documentation-doc', selectedDoc],
    queryFn: async () => {
      const response = await fetch(`/api/documentation/docs/${selectedDoc}`);
      return response.json();
    },
    enabled: !!selectedDoc,
  });

  const categories = [
    { id: 'getting-started', name: '快速开始', icon: '🚀' },
    { id: 'smart-contracts', name: '智能合约', icon: '🔷' },
    { id: 'frontend', name: '前端开发', icon: '⚛️' },
    { id: 'defi-protocols', name: 'DeFi协议', icon: '💰' },
    { id: 'layer2', name: 'Layer2技术', icon: '⚡' },
    { id: 'security', name: '安全指南', icon: '🔒' },
  ];

  return (
    <div className="min-h-screen bg-gray-50">
      <div className="max-w-7xl mx-auto px-4 py-8">
        <header className="bg-white rounded-lg shadow-sm p-6 mb-8">
          <h1 className="text-3xl font-bold text-gray-900">Web3开发者文档</h1>
        </header>

        <div className="grid grid-cols-1 lg:grid-cols-4 gap-8">
          <div className="lg:col-span-1">
            <div className="bg-white rounded-lg shadow-sm p-6">
              <h2 className="text-lg font-semibold text-gray-900 mb-4">文档分类</h2>
              <nav className="space-y-2">
                {categories.map((category) => (
                  <button
                    key={category.id}
                    onClick={() => setSelectedCategory(category.id)}
                    className={`w-full flex items-center space-x-3 px-3 py-2 rounded-lg text-left ${
                      selectedCategory === category.id
                        ? 'bg-blue-100 text-blue-700'
                        : 'hover:bg-gray-100 text-gray-700'
                    }`}
                  >
                    <span className="text-lg">{category.icon}</span>
                    <span>{category.name}</span>
                  </button>
                ))}
              </nav>
            </div>

            {docs && (
              <div className="bg-white rounded-lg shadow-sm p-6 mt-6">
                <h3 className="text-lg font-semibold text-gray-900 mb-4">文档列表</h3>
                <div className="space-y-2">
                  {docs.map((doc: Documentation) => (
                    <button
                      key={doc.id}
                      onClick={() => setSelectedDoc(doc.id)}
                      className={`w-full text-left p-3 rounded-lg ${
                        selectedDoc === doc.id
                          ? 'bg-blue-100 text-blue-700'
                          : 'hover:bg-gray-100 text-gray-700'
                      }`}
                    >
                      <h4 className="font-medium">{doc.title}</h4>
                      <p className="text-sm text-gray-500 mt-1">
                        版本: {doc.version} | 查看: {doc.viewCount}
                      </p>
                    </button>
                  ))}
                </div>
              </div>
            )}
          </div>

          <div className="lg:col-span-3">
            {currentDoc ? (
              <div className="bg-white rounded-lg shadow-sm p-8">
                <h1 className="text-3xl font-bold text-gray-900 mb-4">{currentDoc.title}</h1>
                <div className="prose prose-lg max-w-none">
                  <div
                    dangerouslySetInnerHTML={{
                      __html: marked(currentDoc.content),
                    }}
                  />
                </div>
              </div>
            ) : (
              <div className="bg-white rounded-lg shadow-sm p-8 text-center">
                <div className="text-6xl mb-4">📚</div>
                <h2 className="text-2xl font-semibold text-gray-900 mb-2">选择文档</h2>
                <p className="text-gray-600">请从左侧选择一个文档开始阅读</p>
              </div>
            )}
          </div>
        </div>
      </div>
    </div>
  );
};

export default DocumentationApp;
```

### 3. 代码示例库

#### TypeScript - 代码示例管理系统
```typescript
import React, { useState } from 'react';
import { useQuery } from '@tanstack/react-query';
import { Prism as SyntaxHighlighter } from 'react-syntax-highlighter';
import { tomorrow } from 'react-syntax-highlighter/dist/esm/styles/prism';

interface CodeExample {
  id: string;
  title: string;
  description: string;
  code: string;
  language: string;
  category: string;
  author: string;
  viewCount: number;
  likeCount: number;
  difficulty: 'beginner' | 'intermediate' | 'advanced';
}

const CodeExamplesApp: React.FC = () => {
  const [selectedCategory, setSelectedCategory] = useState<string>('all');
  const [selectedLanguage, setSelectedLanguage] = useState<string>('all');

  const { data: examples, isLoading } = useQuery({
    queryKey: ['code-examples', selectedCategory, selectedLanguage],
    queryFn: async () => {
      const response = await fetch(
        `/api/code-examples?category=${selectedCategory}&language=${selectedLanguage}`
      );
      return response.json();
    },
  });

  const categories = [
    { id: 'all', name: '全部', icon: '📚' },
    { id: 'smart-contracts', name: '智能合约', icon: '🔷' },
    { id: 'frontend', name: '前端开发', icon: '⚛️' },
    { id: 'backend', name: '后端开发', icon: '⚙️' },
    { id: 'defi', name: 'DeFi协议', icon: '💰' },
  ];

  const languages = [
    { id: 'all', name: '全部语言', icon: '🌐' },
    { id: 'javascript', name: 'JavaScript', icon: '🟨' },
    { id: 'typescript', name: 'TypeScript', icon: '🔷' },
    { id: 'solidity', name: 'Solidity', icon: '🔷' },
    { id: 'rust', name: 'Rust', icon: '🦀' },
    { id: 'python', name: 'Python', icon: '🐍' },
  ];

  return (
    <div className="min-h-screen bg-gray-50">
      <div className="max-w-7xl mx-auto px-4 py-8">
        <header className="bg-white rounded-lg shadow-sm p-6 mb-8">
          <h1 className="text-3xl font-bold text-gray-900">代码示例库</h1>
        </header>

        <div className="bg-white rounded-lg shadow-sm p-6 mb-8">
          <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-2">分类</label>
              <select
                value={selectedCategory}
                onChange={(e) => setSelectedCategory(e.target.value)}
                className="w-full px-3 py-2 border border-gray-300 rounded-lg"
              >
                {categories.map((category) => (
                  <option key={category.id} value={category.id}>
                    {category.icon} {category.name}
                  </option>
                ))}
              </select>
            </div>

            <div>
              <label className="block text-sm font-medium text-gray-700 mb-2">编程语言</label>
              <select
                value={selectedLanguage}
                onChange={(e) => setSelectedLanguage(e.target.value)}
                className="w-full px-3 py-2 border border-gray-300 rounded-lg"
              >
                {languages.map((language) => (
                  <option key={language.id} value={language.id}>
                    {language.icon} {language.name}
                  </option>
                ))}
              </select>
            </div>
          </div>
        </div>

        <div className="grid grid-cols-1 lg:grid-cols-2 xl:grid-cols-3 gap-6">
          {isLoading ? (
            <div className="col-span-full text-center py-12">
              <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-blue-600 mx-auto"></div>
            </div>
          ) : (
            examples?.map((example: CodeExample) => (
              <div key={example.id} className="bg-white rounded-lg shadow-sm overflow-hidden">
                <div className="p-6">
                  <div className="flex items-start justify-between mb-4">
                    <h3 className="text-lg font-semibold text-gray-900">{example.title}</h3>
                    <span
                      className={`px-2 py-1 text-xs rounded-full ${
                        example.difficulty === 'beginner'
                          ? 'bg-green-100 text-green-800'
                          : example.difficulty === 'intermediate'
                          ? 'bg-yellow-100 text-yellow-800'
                          : 'bg-red-100 text-red-800'
                      }`}
                    >
                      {example.difficulty}
                    </span>
                  </div>

                  <p className="text-gray-600 text-sm mb-4">{example.description}</p>

                  <div className="bg-gray-900 rounded-lg p-4 mb-4">
                    <SyntaxHighlighter
                      language={example.language}
                      style={tomorrow}
                      customStyle={{ margin: 0, fontSize: '12px' }}
                      showLineNumbers
                    >
                      {example.code.substring(0, 200)}
                      {example.code.length > 200 && '...'}
                    </SyntaxHighlighter>
                  </div>

                  <div className="flex items-center justify-between text-sm text-gray-500">
                    <div className="flex items-center space-x-4">
                      <span>👁️ {example.viewCount}</span>
                      <span>👍 {example.likeCount}</span>
                    </div>
                    <button className="px-3 py-1 bg-blue-600 text-white rounded-lg hover:bg-blue-700">
                      查看详情
                    </button>
                  </div>
                </div>
              </div>
            ))
          )}
        </div>
      </div>
    </div>
  );
};

export default CodeExamplesApp;
```

### 4. 部署配置

#### Docker Compose配置
```yaml
version: '3.8'

services:
  # 开发者社区前端
  community-frontend:
    build:
      context: ./frontend
      dockerfile: Dockerfile
    ports:
      - "3000:3000"
    environment:
      - NEXT_PUBLIC_API_URL=http://localhost:8080
    depends_on:
      - community-backend
    networks:
      - community-network

  # 开发者社区后端
  community-backend:
    build:
      context: ./backend
      dockerfile: Dockerfile
    ports:
      - "8080:8080"
    environment:
      - DATABASE_URL=postgresql://user:password@postgres:5432/community
      - REDIS_URL=redis://redis:6379
    depends_on:
      - postgres
      - redis
    networks:
      - community-network

  # PostgreSQL数据库
  postgres:
    image: postgres:13
    environment:
      - POSTGRES_DB=community
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=password
    networks:
      - community-network

  # Redis缓存
  redis:
    image: redis:6-alpine
    networks:
      - community-network

networks:
  community-network:
    driver: bridge
```

## 总结

开发者社区平台提供了完整的社区建设解决方案：

1. **技术论坛系统**: 支持分类讨论、搜索、用户互动
2. **开发者文档系统**: 完整的文档管理和Markdown渲染
3. **代码示例库**: 多语言代码示例管理和展示
4. **完整部署**: Docker容器化部署方案

该系统为Web3开发者提供了交流、学习和分享的平台，促进了开发者社区的活跃度和技术交流。
