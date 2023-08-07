module main

go 1.16

require (
	github.com/ethereum/go-ethereum v1.11.5
	github.com/holiman/uint256 v1.2.0
)

replace github.com/ethereum/go-ethereum => github.com/taikoxyz/taiko-geth v0.0.0-20230807083144-d9cd977d304b

// Uncomment for debugging
// replace github.com/ethereum/go-ethereum => ../../go-ethereum
