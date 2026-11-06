#!/bin/sh
# Build the jsd image for amd64 and arm64 and push it to ghcr.io, tagged latest and with the package version.
# Logs in with the gh CLI's token (needs write:packages). Run from the repo root.
set -e
image=ghcr.io/ciarands/jsd
version=$(node -p "require('./package.json').version")
gh auth token | docker login ghcr.io -u "$(gh api user --jq .login)" --password-stdin
# The index annotation is what links the package to the repo on GitHub (the Dockerfile LABEL lands on each platform image).
docker buildx build --platform linux/amd64,linux/arm64 -t "$image:latest" -t "$image:$version" \
  --annotation "index:org.opencontainers.image.source=https://github.com/Ciarands/jscrambler-deobfuscator" \
  --annotation "index:org.opencontainers.image.description=jsd: deobfuscator for Jscrambler-protected JavaScript" \
  --push .
echo "pushed $image:latest and $image:$version"
