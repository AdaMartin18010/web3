$ErrorActionPreference = 'Stop'

function Get-MarkdownFiles {
  param([string]$Root)
  Get-ChildItem -Path $Root -Recurse -File -Include *.md
}

function Test-ExternalLink {
  param([string]$Target)
  return ($Target -match '^(https?://|mailto:)')
}

function Resolve-LinkPath {
  param([string]$BaseFile, [string]$Target)
  if ([System.IO.Path]::IsPathRooted($Target)) { return $Target }
  $baseDir = Split-Path -Parent $BaseFile
  $combined = Join-Path $baseDir $Target
  try {
    return [System.IO.Path]::GetFullPath($combined)
  } catch {
    return $combined
  }
}

function Test-DirLinkValid {
  param([string]$Path)
  if (Test-Path -LiteralPath $Path -PathType Container) {
    $readme = Join-Path $Path 'README.md'
    if (Test-Path -LiteralPath $readme) { return $true }
  }
  return $false
}

function Test-Links {
  param([string]$Root)
  $pattern = '\[([^\]]+)\]\(([^)]+)\)'
  $problems = @()
  $files = Get-MarkdownFiles -Root $Root
  $ignoreFragments = @(
    "\docs\Matter\00-备份\"
  )
  foreach ($file in $files) {
    $filePath = $file.FullName
    $skip = $false
    foreach ($frag in $ignoreFragments) { if ($filePath -like "*${frag}*") { $skip = $true; break } }
    if ($skip) { continue }

    $lines = Get-Content -Path $filePath -Encoding UTF8
    $inCode = $false
    for ($i = 0; $i -lt $lines.Count; $i++) {
      $line = $lines[$i]
      if ($line -match '^\s*```') { $inCode = -not $inCode; continue }
      if ($inCode) { continue }

      $linkMatches = [System.Text.RegularExpressions.Regex]::Matches($line, $pattern)
      foreach ($m in $linkMatches) {
        $target = $m.Groups[2].Value.Trim()
        if (-not $target -or (Test-ExternalLink -Target $target)) { continue }
        $pathOnly = $target.Split('#')[0]
        if (-not $pathOnly) { continue } # fragment-only
        $resolved = Resolve-LinkPath -BaseFile $filePath -Target $pathOnly
        if (-not (Test-Path -LiteralPath $resolved)) {
          if (-not (Test-DirLinkValid -Path $resolved)) {
            $problems += [pscustomobject]@{
              File = $filePath
              Line = $i + 1
              Target = $target
              Resolved = $resolved
            }
          }
        }
      }
    }
  }
  return $problems
}

try {
  $repoRoot = (Split-Path -Parent $PSScriptRoot)
  $problems = Test-Links -Root $repoRoot
  if ($problems.Count -gt 0) {
    Write-Host "Broken links found (file:line -> target | resolved):" -ForegroundColor Red
    foreach ($p in $problems) {
      $fileRel = (Resolve-Path -LiteralPath $p.File).Path.Replace($repoRoot + '\', '')
      $resolvedRel = $p.Resolved.Replace($repoRoot + '\', '')
      Write-Host ("{0}:{1} -> {2} | {3}" -f $fileRel, $p.Line, $p.Target, $resolvedRel)
    }
    exit 1
  }
  Write-Host "No broken links detected." -ForegroundColor Green
  exit 0
} catch {
  Write-Host "Link check failed: $($_.Exception.Message)" -ForegroundColor Red
  exit 2
}


