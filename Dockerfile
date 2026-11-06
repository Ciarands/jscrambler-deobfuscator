FROM node:22-alpine AS builder

WORKDIR /app

COPY package*.json ./

RUN npm ci --ignore-scripts

COPY tsconfig*.json ./
COPY src ./src

RUN npm run build

FROM node:22-alpine AS runtime

WORKDIR /app

COPY package*.json ./

RUN npm ci --omit=dev --ignore-scripts && npm cache clean --force

COPY --from=builder /app/dist ./dist

RUN mkdir -p /app/input /app/output && chown node:node /app/output

# The input is hostile: run unprivileged (docker-compose.yml adds no network, a read-only root and limits).
USER node

ENV NODE_ENV=production NODE_OPTIONS=--max-old-space-size=2048

ENTRYPOINT ["node", "dist/cli.js"]

CMD ["--help"]
