#!/bin/bash

GITHUB_RUN_ID=$1

# Set up the directory name with the timestamp
directory_name="CI_Prover_Benches/$GITHUB_RUN_ID"

# Set up the full path for the directory in the home directory
directory_path="$HOME/$directory_name"

# Create the directory
if [ ! -d "$directory_path" ]; then
  mkdir -p "$directory_path"
  echo "Directory '$directory_name' with GITHUB_RUN_ID '$GITHUB_RUN_ID' has been created in the home directory."
fi

