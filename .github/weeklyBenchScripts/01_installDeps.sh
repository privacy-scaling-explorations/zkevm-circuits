#!/bin/bash
sudo apt update

# Check if Git is already installed
if command -v git &>/dev/null; then
    echo "Git is already installed."
else
    # Detect the Linux distribution and install Git
    if [[ -f /etc/os-release ]]; then
        source /etc/os-release
        if [[ $ID == "ubuntu" || $ID == "debian" ]]; then
            sudo apt install -y git
        elif [[ $ID == "centos" || $ID == "rhel" ]]; then
            sudo yum install -y git
        elif [[ $ID == "fedora" ]]; then
            sudo dnf install -y git
        else
            echo "Unsupported Linux distribution. Please install Git manually."
            exit 1
        fi
    else
        echo "Cannot determine the Linux distribution. Please install Git manually."
        exit 1
    fi

    # Verify Git installation
    if command -v git &>/dev/null; then
        echo "Git has been installed successfully."
    else
        echo "Failed to install Git. Please install it manually."
    fi
fi

# Check if the C compiler is installed
if ! command -v cc &>/dev/null; then
    # Detect the Linux distribution and install the C compiler
    if [[ -f /etc/os-release ]]; then
        source /etc/os-release
        if [[ $ID == "ubuntu" || $ID == "debian" ]]; then
            sudo apt install -y build-essential
        elif [[ $ID == "centos" || $ID == "rhel" ]]; then
            sudo yum groupinstall -y "Development Tools"
        elif [[ $ID == "fedora" ]]; then
            sudo dnf groupinstall -y "Development Tools"
        else
            echo "Unsupported Linux distribution. Please install the C compiler manually."
            exit 1
        fi
    else
        echo "Cannot determine the Linux distribution. Please install the C compiler manually."
        exit 1
    fi

    # Verify C compiler installation
    if command -v cc &>/dev/null; then
        echo "The C compiler has been installed successfully."
    else
        echo "Failed to install the C compiler. Please install it manually."
    fi
fi

sudo apt install -y pkg-config fontconfig libfontconfig-dev
