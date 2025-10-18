FROM node:22-alpine AS builder

WORKDIR /app

COPY package*.json ./

RUN npm ci

COPY . .

RUN npm run build

FROM node:22-alpine AS runtime

WORKDIR /app

COPY package*.json ./

RUN npm ci --only=production && npm cache clean --force

COPY --from=builder /app/dist ./dist

RUN mkdir -p /app/input /app/output

ENTRYPOINT ["node", "dist/cli.js"]

CMD ["--help"]