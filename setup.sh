#!/bin/bash

# Script to setup UDBM and UTAP libraries for TimedAutomata examples
# This script will clone both libraries if not present and build them

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
UDBM_DIR="$SCRIPT_DIR/UDBM"
echo "Setting up UDBM and UTAP libraries..."




#install omp
sudo apt-get update && sudo apt-get install -y libomp-dev


# Setup UDBM
echo "=== Setting up UDBM ==="
# Check if UDBM directory exists
if [ ! -d "$UDBM_DIR" ]; then
    echo "UDBM directory not found. Cloning from GitHub..."
    git clone https://github.com/UPPAALModelChecker/UDBM "$UDBM_DIR"
fi

cd "$UDBM_DIR"

# Check if library is already built
if [ ! -f "build-x86_64-linux-release/src/libUDBM.a" ]; then
    echo "UDBM library not built. Building now..."
    
    # Get dependencies
    echo "Getting UDBM dependencies..."
    ./getlibs.sh x86_64-linux
    
    # Compile the library
    echo "Compiling UDBM..."
    ./compile.sh x86_64-linux-libs-release
    
    echo "UDBM library built successfully!"
else
    echo "UDBM library already built."
fi




echo "=== Setup Complete ==="
echo "Ready to build"
