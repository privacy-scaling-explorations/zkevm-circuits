FROM node:14-alpine

WORKDIR /app

COPY package.json .

RUN apk add git &&\
    yarn

# ENTRYPOINT yarn deploy
