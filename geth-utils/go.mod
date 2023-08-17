module main

go 1.16

require (
	github.com/ethereum/go-ethereum v1.12.2
	github.com/holiman/uint256 v1.2.3
)

// Uncomment for debugging
// replace github.com/ethereum/go-ethereum => ../../go-ethereum
replace github.com/ethereum/go-ethereum v1.12.2 => github.com/taikoxyz/taiko-geth v0.0.0-20230814083522-76b7e96ec36f
