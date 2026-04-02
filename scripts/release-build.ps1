# release-build.ps1
# Minimal “verifier-friendly” build script for the EulerBasel project.
# Run from repo root:
#   powershell -ExecutionPolicy Bypass -File .\scripts\release-build.ps1
#
# Optional:
#   powershell -ExecutionPolicy Bypass -File .\scripts\release-build.ps1 -Clean

param(
  [switch]$Clean
)

$ErrorActionPreference = "Stop"

function Say([string]$msg) {
  Write-Host $msg
}

Say ""
Say "=== EulerBasel release build ==="
Say ("Repo root: " + (Get-Location).Path)
Say ("Time: " + (Get-Date).ToString("yyyy-MM-dd HH:mm:ss"))

if ($Clean) {
  Say ""
  Say "-> Cleaning (lake clean)..."
  & lake clean
}

Say ""
Say "-> Toolchain info:"
try {
  & lake env lean --version
} catch {
  Say "WARNING: failed to run 'lake env lean --version'. Continuing."
}

Say ""
Say "-> Building (lake build)..."
& lake build

Say ""
Say "✅ SUCCESS: lake build completed."
Say "=== Done ==="