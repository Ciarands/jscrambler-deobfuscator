FROM node:24-alpine AS build
WORKDIR /app
COPY package*.json ./
RUN npm ci --ignore-scripts
COPY tsconfig*.json ./
COPY src ./src
RUN npm run build

FROM node:24-alpine
LABEL org.opencontainers.image.source="https://github.com/Ciarands/jscrambler-deobfuscator" \
      org.opencontainers.image.description="jsd: deobfuscator for Jscrambler-protected JavaScript"
WORKDIR /app
COPY package*.json ./
RUN npm ci --omit=dev --ignore-scripts && npm cache clean --force
COPY --from=build /app/dist ./dist
# Run with `-v "$PWD:/work"`: paths are relative to the folder you run it from.
WORKDIR /work
USER node
ENV NODE_ENV=production NODE_OPTIONS=--max-old-space-size=2048
ENTRYPOINT ["node", "/app/dist/cli.js"]
