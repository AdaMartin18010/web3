# 开发者社区平台应用

## 概述

开发者社区平台是Phase 3第4个月"社区建设"阶段的核心应用，提供技术论坛、开发者文档和代码示例库，构建活跃的Web3开发者社区。

## 核心功能

### 1. 技术论坛系统

#### TypeScript - 论坛前端应用
```typescript
import React, { useState, useEffect } from 'react';
import { useQuery, useMutation, useQueryClient } from '@tanstack/react-query';
import { useAuth } from './hooks/useAuth';

interface ForumPost {
  id: string;
  title: string;
  content: string;
  author: {
    id: string;
    name: string;
    avatar: string;
    reputation: number;
  };
  category: string;
  tags: string[];
  createdAt: string;
  updatedAt: string;
  viewCount: number;
  replyCount: number;
  likes: number;
  isSticky: boolean;
  isLocked: boolean;
}

interface ForumReply {
  id: string;
  content: string;
  author: {
    id: string;
    name: string;
    avatar: string;
    reputation: number;
  };
  createdAt: string;
  updatedAt: string;
  likes: number;
  isAccepted: boolean;
}

const ForumApp: React.FC = () => {
  const { user } = useAuth();
  const queryClient = useQueryClient();
  const [selectedCategory, setSelectedCategory] = useState<string>('all');
  const [searchQuery, setSearchQuery] = useState<string>('');

  // 获取论坛帖子列表
  const { data: posts, isLoading } = useQuery({
    queryKey: ['forum-posts', selectedCategory, searchQuery],
    queryFn: async () => {
      const response = await fetch(`/api/forum/posts?category=${selectedCategory}&search=${searchQuery}`);
      return response.json();
    },
  });

  // 创建新帖子
  const createPostMutation = useMutation({
    mutationFn: async (newPost: Partial<ForumPost>) => {
      const response = await fetch('/api/forum/posts', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(newPost),
      });
      return response.json();
    },
    onSuccess: () => {
      queryClient.invalidateQueries({ queryKey: ['forum-posts'] });
    },
  });

  const categories = [
    { id: 'all', name: '全部', icon: '📚' },
    { id: 'solidity', name: 'Solidity开发', icon: '🔷' },
    { id: 'react', name: 'React前端', icon: '⚛️' },
    { id: 'defi', name: 'DeFi协议', icon: '💰' },
    { id: 'layer2', name: 'Layer2技术', icon: '⚡' },
    { id: 'security', name: '安全审计', icon: '🔒' },
    { id: 'tutorial', name: '教程分享', icon: '📖' },
    { id: 'qa', name: '问答交流', icon: '❓' },
  ];

  return (
    <div className="min-h-screen bg-gray-50">
      <div className="max-w-7xl mx-auto px-4 py-8">
        {/* 头部导航 */}
        <header className="bg-white rounded-lg shadow-sm p-6 mb-8">
          <div className="flex items-center justify-between">
            <h1 className="text-3xl font-bold text-gray-900">Web3开发者论坛</h1>
            <div className="flex items-center space-x-4">
              <input
                type="text"
                placeholder="搜索帖子..."
                value={searchQuery}
                onChange={(e) => setSearchQuery(e.target.value)}
                className="px-4 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-transparent"
              />
              {user && (
                <button
                  onClick={() => {/* 打开创建帖子模态框 */}}
                  className="px-6 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
                >
                  发布帖子
                </button>
              )}
            </div>
          </div>
        </header>

        <div className="grid grid-cols-1 lg:grid-cols-4 gap-8">
          {/* 侧边栏 - 分类导航 */}
          <div className="lg:col-span-1">
            <div className="bg-white rounded-lg shadow-sm p-6">
              <h2 className="text-lg font-semibold text-gray-900 mb-4">分类</h2>
              <nav className="space-y-2">
                {categories.map((category) => (
                  <button
                    key={category.id}
                    onClick={() => setSelectedCategory(category.id)}
                    className={`w-full flex items-center space-x-3 px-3 py-2 rounded-lg text-left transition-colors ${
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

          {/* 主内容区 - 帖子列表 */}
          <div className="lg:col-span-3">
            <div className="bg-white rounded-lg shadow-sm">
              {isLoading ? (
                <div className="p-8 text-center">
                  <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-blue-600 mx-auto"></div>
                  <p className="mt-4 text-gray-600">加载中...</p>
                </div>
              ) : (
                <div className="divide-y divide-gray-200">
                  {posts?.map((post: ForumPost) => (
                    <article key={post.id} className="p-6 hover:bg-gray-50 transition-colors">
                      <div className="flex items-start space-x-4">
                        {/* 作者头像 */}
                        <div className="flex-shrink-0">
                          <img
                            src={post.author.avatar}
                            alt={post.author.name}
                            className="w-12 h-12 rounded-full"
                          />
                        </div>

                        {/* 帖子内容 */}
                        <div className="flex-1 min-w-0">
                          <div className="flex items-center space-x-2 mb-2">
                            {post.isSticky && (
                              <span className="px-2 py-1 bg-yellow-100 text-yellow-800 text-xs rounded-full">
                                置顶
                              </span>
                            )}
                            <span className="px-2 py-1 bg-blue-100 text-blue-800 text-xs rounded-full">
                              {categories.find(c => c.id === post.category)?.name}
                            </span>
                            {post.tags.map((tag) => (
                              <span
                                key={tag}
                                className="px-2 py-1 bg-gray-100 text-gray-700 text-xs rounded-full"
                              >
                                #{tag}
                              </span>
                            ))}
                          </div>

                          <h3 className="text-lg font-semibold text-gray-900 mb-2">
                            <a href={`/forum/post/${post.id}`} className="hover:text-blue-600">
                              {post.title}
                            </a>
                          </h3>

                          <p className="text-gray-600 text-sm mb-3 line-clamp-2">
                            {post.content}
                          </p>

                          <div className="flex items-center justify-between text-sm text-gray-500">
                            <div className="flex items-center space-x-4">
                              <span>作者: {post.author.name}</span>
                              <span>声望: {post.author.reputation}</span>
                              <span>发布时间: {new Date(post.createdAt).toLocaleDateString()}</span>
                            </div>
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
import React, { useState, useEffect } from 'react';
import { useQuery, useMutation } from '@tanstack/react-query';
import { marked } from 'marked';
import { Prism as SyntaxHighlighter } from 'react-syntax-highlighter';
import { tomorrow } from 'react-syntax-highlighter/dist/esm/styles/prism';

interface Documentation {
  id: string;
  title: string;
  content: string;
  category: string;
  tags: string[];
  author: string;
  version: string;
  createdAt: string;
  updatedAt: string;
  viewCount: number;
  rating: number;
  isPublished: boolean;
}

interface DocumentationCategory {
  id: string;
  name: string;
  description: string;
  icon: string;
  docs: Documentation[];
}

const DocumentationApp: React.FC = () => {
  const [selectedCategory, setSelectedCategory] = useState<string>('getting-started');
  const [selectedDoc, setSelectedDoc] = useState<string>('');
  const [searchQuery, setSearchQuery] = useState<string>('');

  // 获取文档分类
  const { data: categories } = useQuery({
    queryKey: ['doc-categories'],
    queryFn: async () => {
      const response = await fetch('/api/documentation/categories');
      return response.json();
    },
  });

  // 获取文档列表
  const { data: docs } = useQuery({
    queryKey: ['documentation', selectedCategory, searchQuery],
    queryFn: async () => {
      const response = await fetch(`/api/documentation/docs?category=${selectedCategory}&search=${searchQuery}`);
      return response.json();
    },
  });

  // 获取单个文档
  const { data: currentDoc } = useQuery({
    queryKey: ['documentation-doc', selectedDoc],
    queryFn: async () => {
      const response = await fetch(`/api/documentation/docs/${selectedDoc}`);
      return response.json();
    },
    enabled: !!selectedDoc,
  });

  // 配置Markdown渲染
  marked.setOptions({
    highlight: function (code, lang) {
      if (lang && SyntaxHighlighter.supportedLanguages.includes(lang)) {
        return SyntaxHighlighter.highlight(code, { language: lang }, tomorrow);
      }
      return code;
    },
  });

  const docCategories = [
    { id: 'getting-started', name: '快速开始', icon: '🚀' },
    { id: 'smart-contracts', name: '智能合约', icon: '🔷' },
    { id: 'frontend', name: '前端开发', icon: '⚛️' },
    { id: 'defi-protocols', name: 'DeFi协议', icon: '💰' },
    { id: 'layer2', name: 'Layer2技术', icon: '⚡' },
    { id: 'security', name: '安全指南', icon: '🔒' },
    { id: 'api-reference', name: 'API参考', icon: '📚' },
    { id: 'tutorials', name: '教程指南', icon: '📖' },
  ];

  return (
    <div className="min-h-screen bg-gray-50">
      <div className="max-w-7xl mx-auto px-4 py-8">
        {/* 头部导航 */}
        <header className="bg-white rounded-lg shadow-sm p-6 mb-8">
          <div className="flex items-center justify-between">
            <h1 className="text-3xl font-bold text-gray-900">Web3开发者文档</h1>
            <div className="flex items-center space-x-4">
              <input
                type="text"
                placeholder="搜索文档..."
                value={searchQuery}
                onChange={(e) => setSearchQuery(e.target.value)}
                className="px-4 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-transparent"
              />
            </div>
          </div>
        </header>

        <div className="grid grid-cols-1 lg:grid-cols-4 gap-8">
          {/* 侧边栏 - 文档分类 */}
          <div className="lg:col-span-1">
            <div className="bg-white rounded-lg shadow-sm p-6">
              <h2 className="text-lg font-semibold text-gray-900 mb-4">文档分类</h2>
              <nav className="space-y-2">
                {docCategories.map((category) => (
                  <button
                    key={category.id}
                    onClick={() => setSelectedCategory(category.id)}
                    className={`w-full flex items-center space-x-3 px-3 py-2 rounded-lg text-left transition-colors ${
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

            {/* 文档列表 */}
            {docs && (
              <div className="bg-white rounded-lg shadow-sm p-6 mt-6">
                <h3 className="text-lg font-semibold text-gray-900 mb-4">文档列表</h3>
                <div className="space-y-2">
                  {docs.map((doc: Documentation) => (
                    <button
                      key={doc.id}
                      onClick={() => setSelectedDoc(doc.id)}
                      className={`w-full text-left p-3 rounded-lg transition-colors ${
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

          {/* 主内容区 - 文档内容 */}
          <div className="lg:col-span-3">
            {currentDoc ? (
              <div className="bg-white rounded-lg shadow-sm p-8">
                <div className="mb-6">
                  <h1 className="text-3xl font-bold text-gray-900 mb-2">{currentDoc.title}</h1>
                  <div className="flex items-center space-x-4 text-sm text-gray-500">
                    <span>作者: {currentDoc.author}</span>
                    <span>版本: {currentDoc.version}</span>
                    <span>更新时间: {new Date(currentDoc.updatedAt).toLocaleDateString()}</span>
                    <span>查看次数: {currentDoc.viewCount}</span>
                  </div>
                  <div className="flex items-center space-x-2 mt-3">
                    {currentDoc.tags.map((tag: string) => (
                      <span
                        key={tag}
                        className="px-2 py-1 bg-gray-100 text-gray-700 text-xs rounded-full"
                      >
                        #{tag}
                      </span>
                    ))}
                  </div>
                </div>

                <div className="prose prose-lg max-w-none">
                  <div
                    dangerouslySetInnerHTML={{
                      __html: marked(currentDoc.content),
                    }}
                  />
                </div>

                <div className="mt-8 pt-6 border-t border-gray-200">
                  <div className="flex items-center justify-between">
                    <div className="flex items-center space-x-4">
                      <span className="text-sm text-gray-500">这篇文档对您有帮助吗？</span>
                      <div className="flex items-center space-x-2">
                        <button className="px-3 py-1 bg-green-100 text-green-700 rounded-lg hover:bg-green-200">
                          👍 有帮助
                        </button>
                        <button className="px-3 py-1 bg-red-100 text-red-700 rounded-lg hover:bg-red-200">
                          👎 没帮助
                        </button>
                      </div>
                    </div>
                    <div className="text-sm text-gray-500">
                      评分: ⭐⭐⭐⭐⭐ ({currentDoc.rating}/5)
                    </div>
                  </div>
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
import React, { useState, useEffect } from 'react';
import { useQuery, useMutation } from '@tanstack/react-query';
import { Prism as SyntaxHighlighter } from 'react-syntax-highlighter';
import { tomorrow } from 'react-syntax-highlighter/dist/esm/styles/prism';

interface CodeExample {
  id: string;
  title: string;
  description: string;
  code: string;
  language: string;
  category: string;
  tags: string[];
  author: string;
  createdAt: string;
  updatedAt: string;
  viewCount: number;
  likeCount: number;
  downloadCount: number;
  difficulty: 'beginner' | 'intermediate' | 'advanced';
  isPublic: boolean;
}

const CodeExamplesApp: React.FC = () => {
  const [selectedCategory, setSelectedCategory] = useState<string>('all');
  const [selectedLanguage, setSelectedLanguage] = useState<string>('all');
  const [selectedDifficulty, setSelectedDifficulty] = useState<string>('all');
  const [searchQuery, setSearchQuery] = useState<string>('');

  // 获取代码示例列表
  const { data: examples, isLoading } = useQuery({
    queryKey: ['code-examples', selectedCategory, selectedLanguage, selectedDifficulty, searchQuery],
    queryFn: async () => {
      const response = await fetch(
        `/api/code-examples?category=${selectedCategory}&language=${selectedLanguage}&difficulty=${selectedDifficulty}&search=${searchQuery}`
      );
      return response.json();
    },
  });

  // 下载代码示例
  const downloadExample = (example: CodeExample) => {
    const blob = new Blob([example.code], { type: 'text/plain' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `${example.title}.${getFileExtension(example.language)}`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
  };

  const getFileExtension = (language: string) => {
    const extensions: { [key: string]: string } = {
      javascript: 'js',
      typescript: 'ts',
      solidity: 'sol',
      rust: 'rs',
      python: 'py',
      go: 'go',
      html: 'html',
      css: 'css',
    };
    return extensions[language] || 'txt';
  };

  const categories = [
    { id: 'all', name: '全部', icon: '📚' },
    { id: 'smart-contracts', name: '智能合约', icon: '🔷' },
    { id: 'frontend', name: '前端开发', icon: '⚛️' },
    { id: 'backend', name: '后端开发', icon: '⚙️' },
    { id: 'defi', name: 'DeFi协议', icon: '💰' },
    { id: 'security', name: '安全相关', icon: '🔒' },
    { id: 'testing', name: '测试代码', icon: '🧪' },
    { id: 'tools', name: '开发工具', icon: '🛠️' },
  ];

  const languages = [
    { id: 'all', name: '全部语言', icon: '🌐' },
    { id: 'javascript', name: 'JavaScript', icon: '🟨' },
    { id: 'typescript', name: 'TypeScript', icon: '🔷' },
    { id: 'solidity', name: 'Solidity', icon: '🔷' },
    { id: 'rust', name: 'Rust', icon: '🦀' },
    { id: 'python', name: 'Python', icon: '🐍' },
    { id: 'go', name: 'Go', icon: '🔵' },
    { id: 'html', name: 'HTML', icon: '🌐' },
    { id: 'css', name: 'CSS', icon: '🎨' },
  ];

  const difficulties = [
    { id: 'all', name: '全部难度', color: 'gray' },
    { id: 'beginner', name: '初级', color: 'green' },
    { id: 'intermediate', name: '中级', color: 'yellow' },
    { id: 'advanced', name: '高级', color: 'red' },
  ];

  return (
    <div className="min-h-screen bg-gray-50">
      <div className="max-w-7xl mx-auto px-4 py-8">
        {/* 头部导航 */}
        <header className="bg-white rounded-lg shadow-sm p-6 mb-8">
          <div className="flex items-center justify-between">
            <h1 className="text-3xl font-bold text-gray-900">代码示例库</h1>
            <div className="flex items-center space-x-4">
              <input
                type="text"
                placeholder="搜索代码示例..."
                value={searchQuery}
                onChange={(e) => setSearchQuery(e.target.value)}
                className="px-4 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-transparent"
              />
            </div>
          </div>
        </header>

        {/* 筛选器 */}
        <div className="bg-white rounded-lg shadow-sm p-6 mb-8">
          <div className="grid grid-cols-1 md:grid-cols-4 gap-6">
            {/* 分类筛选 */}
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-2">分类</label>
              <select
                value={selectedCategory}
                onChange={(e) => setSelectedCategory(e.target.value)}
                className="w-full px-3 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-transparent"
              >
                {categories.map((category) => (
                  <option key={category.id} value={category.id}>
                    {category.icon} {category.name}
                  </option>
                ))}
              </select>
            </div>

            {/* 语言筛选 */}
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-2">编程语言</label>
              <select
                value={selectedLanguage}
                onChange={(e) => setSelectedLanguage(e.target.value)}
                className="w-full px-3 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-transparent"
              >
                {languages.map((language) => (
                  <option key={language.id} value={language.id}>
                    {language.icon} {language.name}
                  </option>
                ))}
              </select>
            </div>

            {/* 难度筛选 */}
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-2">难度</label>
              <select
                value={selectedDifficulty}
                onChange={(e) => setSelectedDifficulty(e.target.value)}
                className="w-full px-3 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-transparent"
              >
                {difficulties.map((difficulty) => (
                  <option key={difficulty.id} value={difficulty.id}>
                    {difficulty.name}
                  </option>
                ))}
              </select>
            </div>

            {/* 统计信息 */}
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-2">统计</label>
              <div className="text-sm text-gray-600">
                <p>总计: {examples?.length || 0} 个示例</p>
                <p>语言: {selectedLanguage}</p>
                <p>难度: {selectedDifficulty}</p>
              </div>
            </div>
          </div>
        </div>

        {/* 代码示例列表 */}
        <div className="grid grid-cols-1 lg:grid-cols-2 xl:grid-cols-3 gap-6">
          {isLoading ? (
            <div className="col-span-full text-center py-12">
              <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-blue-600 mx-auto"></div>
              <p className="mt-4 text-gray-600">加载中...</p>
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

                  <p className="text-gray-600 text-sm mb-4 line-clamp-3">{example.description}</p>

                  <div className="flex items-center space-x-2 mb-4">
                    <span className="px-2 py-1 bg-blue-100 text-blue-800 text-xs rounded-full">
                      {languages.find(l => l.id === example.language)?.name}
                    </span>
                    {example.tags.map((tag) => (
                      <span
                        key={tag}
                        className="px-2 py-1 bg-gray-100 text-gray-700 text-xs rounded-full"
                      >
                        #{tag}
                      </span>
                    ))}
                  </div>

                  {/* 代码预览 */}
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
                      <span>⬇️ {example.downloadCount}</span>
                    </div>
                    <div className="flex items-center space-x-2">
                      <button
                        onClick={() => downloadExample(example)}
                        className="px-3 py-1 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
                      >
                        下载
                      </button>
                      <button className="px-3 py-1 bg-gray-100 text-gray-700 rounded-lg hover:bg-gray-200 transition-colors">
                        查看详情
                      </button>
                    </div>
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
      - NEXT_PUBLIC_FORUM_URL=http://localhost:3001
      - NEXT_PUBLIC_DOCS_URL=http://localhost:3002
      - NEXT_PUBLIC_EXAMPLES_URL=http://localhost:3003
    depends_on:
      - community-backend
    networks:
      - community-network

  # 论坛服务
  forum-service:
    build:
      context: ./forum
      dockerfile: Dockerfile
    ports:
      - "3001:3000"
    environment:
      - DATABASE_URL=postgresql://user:password@postgres:5432/forum
      - REDIS_URL=redis://redis:6379
    depends_on:
      - postgres
      - redis
    networks:
      - community-network

  # 文档服务
  docs-service:
    build:
      context: ./docs
      dockerfile: Dockerfile
    ports:
      - "3002:3000"
    environment:
      - DATABASE_URL=postgresql://user:password@postgres:5432/docs
      - ELASTICSEARCH_URL=http://elasticsearch:9200
    depends_on:
      - postgres
      - elasticsearch
    networks:
      - community-network

  # 代码示例服务
  examples-service:
    build:
      context: ./examples
      dockerfile: Dockerfile
    ports:
      - "3003:3000"
    environment:
      - DATABASE_URL=postgresql://user:password@postgres:5432/examples
      - GITHUB_TOKEN=${GITHUB_TOKEN}
    depends_on:
      - postgres
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
      - JWT_SECRET=${JWT_SECRET}
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
    volumes:
      - postgres_data:/var/lib/postgresql/data
    networks:
      - community-network

  # Redis缓存
  redis:
    image: redis:6-alpine
    volumes:
      - redis_data:/data
    networks:
      - community-network

  # Elasticsearch搜索
  elasticsearch:
    image: elasticsearch:7.17.0
    environment:
      - discovery.type=single-node
      - "ES_JAVA_OPTS=-Xms512m -Xmx512m"
    volumes:
      - elasticsearch_data:/usr/share/elasticsearch/data
    networks:
      - community-network

volumes:
  postgres_data:
  redis_data:
  elasticsearch_data:

networks:
  community-network:
    driver: bridge
```

## 总结

开发者社区平台提供了完整的社区建设解决方案：

1. **技术论坛系统**: 支持分类讨论、搜索、用户互动
2. **开发者文档系统**: 完整的文档管理和Markdown渲染
3. **代码示例库**: 多语言代码示例管理和下载
4. **完整部署**: Docker容器化部署方案

该系统为Web3开发者提供了交流、学习和分享的平台，促进了开发者社区的活跃度和技术交流。
