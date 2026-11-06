$ErrorActionPreference = 'Stop'
$ProgressPreference = 'SilentlyContinue'
$p = $PSScriptRoot
foreach ($d in @('build','build\tmp','build\texmf-var','build\texmf-config')) {
    New-Item -ItemType Directory -Path (Join-Path $p $d) -Force | Out-Null
}
$env:TEMP = Join-Path $p 'build\tmp'
$env:TMP = $env:TEMP
$env:TEXMFOUTPUT = Join-Path $p 'build'
$env:TEXMFVAR = Join-Path $p 'build\texmf-var'
$env:TEXMFCONFIG = Join-Path $p 'build\texmf-config'
$compiler = 'C:\texlive\2025\bin\windows\latexmk.exe'
if (-not (Test-Path -LiteralPath $compiler)) { $compiler = 'latexmk' }
Push-Location $p
try {
    & $compiler -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=build paper_main.tex
    if ($LASTEXITCODE -ne 0) { throw "latexmk failed with exit code $LASTEXITCODE" }
} finally { Pop-Location }
