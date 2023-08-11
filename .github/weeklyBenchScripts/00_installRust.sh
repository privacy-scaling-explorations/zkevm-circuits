#!/bin/bash

# Check if rustup is already installed
if ! command -v rustup &>/dev/null; then
    echo "Installing rustup..."
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
    source $HOME/.cargo/env
else
    echo "rustup is already installed. Checking for updates..."
    rustup update
fi

# Install the latest version of Rust
echo "Installing the latest version of Rust..."
rustup install stable

# Set the latest version as the default
rustup default stable

# Print the installed Rust version
echo "Rust has been installed successfully. Current version:"
rustc --version
cargo --version

