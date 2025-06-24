import os
import shutil

# 归档目录名
ARCHIVE_DIRS = ['00-备份', '99_Recycle_Bin']

# 需要归档的文件后缀或关键字
ARCHIVE_KEYWORDS = ['old', 'bak', 'temp', '未整理', '历史', '冗余']

# 递归归档函数
def auto_archive(root_dir):
    for dirpath, dirnames, filenames in os.walk(root_dir):
        for fname in filenames:
            if any(key in fname for key in ARCHIVE_KEYWORDS):
                archive_dir = os.path.join(dirpath, ARCHIVE_DIRS[0])
                os.makedirs(archive_dir, exist_ok=True)
                shutil.move(os.path.join(dirpath, fname), os.path.join(archive_dir, fname))
                print(f"已归档: {fname} -> {archive_dir}")

if __name__ == "__main__":
    auto_archive(os.path.dirname(__file__))
    print("归档完成。") 