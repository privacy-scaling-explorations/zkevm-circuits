# MPT witness generator

## Generate witnesses

To generate witnesses for the MPT circuit, execute

```
go test -v ./...
```

To generate the tests that use a local blockchain you need a local `geth`. You would
need to run something like:
```
geth --dev --http --ipcpath ~/Library/Ethereum/geth.ipc

```
The local `geth` is used to generate some tests that have a small number of accounts so that
these accounts appear in the first or second level of the trie. You might need to remove the
database if you already have some accounts:

```
geth removedb
```

The witness files will appear in generated_witnesses folder.

## Format the code

To format the code use:

```
gofmt -w ./*
```