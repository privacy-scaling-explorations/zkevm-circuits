#!/bin/bash

# Check if Go is already installed
if command -v go &>/dev/null; then
    echo "Go is already installed."
else
    # Set the Go version to be installed (latest as of current date)
    GO_VERSION="1.19.1"

    # Determine the architecture
    ARCH="amd64"

    # Download and extract the Go archive
    wget -q "https://golang.org/dl/go$GO_VERSION.linux-$ARCH.tar.gz"
    sudo tar -C /usr/local -xzf "go$GO_VERSION.linux-$ARCH.tar.gz"

    # Set Go environment variables
    export GOROOT="/usr/local/go"
    export GOPATH="$HOME/go"
    export PATH="$GOROOT/bin:$GOPATH/bin:$PATH"

    # Append Go environment variables to the shell profile
    echo 'export GOROOT="/usr/local/go"' >> "$HOME/.bashrc"
    echo 'export GOPATH="$HOME/go"' >> "$HOME/.bashrc"
    echo 'export PATH="$GOROOT/bin:$GOPATH/bin:$PATH"' >> "$HOME/.bashrc"

    # Refresh the shell session to make Go available
    source "$HOME/.bashrc"

    # Cleanup the downloaded archive
    rm "go$GO_VERSION.linux-$ARCH.tar.gz"

    echo "Go $GO_VERSION has been installed successfully."
fi

# Display the installed Go version
go version

