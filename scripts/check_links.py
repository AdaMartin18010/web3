import os
import re
from typing import List, Tuple


MARKDOWN_LINK_PATTERN = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")


def find_markdown_files(root: str) -> List[str]:
    files: List[str] = []
    for dirpath, dirnames, filenames in os.walk(root):
        # skip common large or generated dirs if any
        for name in filenames:
            if name.lower().endswith(".md"):
                files.append(os.path.join(dirpath, name))
    return files


def is_external_link(target: str) -> bool:
    return target.startswith("http://") or target.startswith("https://") or target.startswith("mailto:")


def normalize_path(base_file: str, link_target: str) -> str:
    if os.path.isabs(link_target):
        return link_target
    return os.path.normpath(os.path.join(os.path.dirname(base_file), link_target))


def check_links(root: str) -> List[Tuple[str, int, str, str]]:
    problems: List[Tuple[str, int, str, str]] = []
    md_files = find_markdown_files(root)
    for md_file in md_files:
        try:
            with open(md_file, "r", encoding="utf-8") as f:
                for idx, line in enumerate(f, start=1):
                    for match in MARKDOWN_LINK_PATTERN.finditer(line):
                        target = match.group(2).strip()
                        if not target or is_external_link(target):
                            continue
                        # drop fragment part
                        path_only = target.split('#', 1)[0]
                        if not path_only:
                            # intra-doc fragment only, skip
                            continue
                        resolved = normalize_path(md_file, path_only)
                        if not os.path.exists(resolved):
                            problems.append((md_file, idx, target, resolved))
        except Exception as e:
            problems.append((md_file, 0, "<read_error>", str(e)))
    return problems


def main() -> int:
    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), os.pardir))
    problems = check_links(repo_root)
    if problems:
        print("Broken links found (file:line -> target | resolved):")
        for file_path, line_no, target, resolved in problems:
            print(f"{os.path.relpath(file_path, repo_root)}:{line_no} -> {target} | {os.path.relpath(resolved, repo_root)}")
        return 1
    print("No broken links detected.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())


