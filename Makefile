help: ## Display this help screen
	@grep -h \
		-E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | \
		awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-30s\033[0m %s\n", $$1, $$2}'

clippy: ## Run clippy checks over all workspace members
	@cargo clippy --all-features --all-targets -- -D clippy::all

doc: ## Generate and tests docs including private items
	@cargo doc --all --document-private-items

fmt: ## Check whether the code is formated correctly
	@cargo fmt --all -- --check

test: ## Run tests for all the workspace members
	@cargo test --release --all --all-features

test-all: fmt doc clippy test ## Run all the CI checks locally (in your actual toolchain) 


.PHONY: clippy doc fmt test test-all help
