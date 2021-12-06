FROM node:14-alpine

WORKDIR /app

RUN apk add git

COPY package.json .

RUN yarn install

COPY . .

CMD ./node_modules/.bin/ts-node index.ts && \
    ./node_modules/.bin/ts-node utils/deploy.ts Greeter
