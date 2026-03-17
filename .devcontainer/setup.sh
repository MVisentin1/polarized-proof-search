#!/bin/bash
set -e 

echo "--- 1. Fixing Git Permissions & Ownership ---"
# Necessary to avoid "dubious ownership" errors in Dev Containers
git config --global --add safe.directory /workspaces/polarized-proof-search
git config --global --add safe.directory /workspaces/polarized-proof-search/rocq-carve

#echo "--- 2. Setting Fallback Git Identity ---"
#if [ -z "$(git config --global user.email)" ]; then
#    git config --global user.email "research-team@mcgill.ca"
#    git config --global user.name "Research Team"
#fi

echo "--- 3. Initializing Submodules ---"
git submodule update --init --recursive

echo "--- 4. Syncing OPAM & Installing Research Tools ---"
# We force the switch and load the environment explicitly
eval $(opam env --switch 5.3.0 --set-switch)

# Add Repositories
opam repo add coq-released https://coq.inria.fr/opam/released || true
opam update -y

# Pin Rocq 9.1.0
opam pin add -y coq 9.1.0

# Install the actual "brains" of the IDE and your search algorithm
# We install vscoq-language-server as it provides the vscoqtop binary for Rocq 9.1
opam install -y \
    num \
    coq-simple-io \
    vscoq-language-server \
    ocaml-lsp-server \
    utop \
    coq-hammer

echo "--- 5. Building the Project ---"
# Reload env one last time to ensure binaries like 'rocq' are in PATH
eval $(opam env)

# Generate the Makefile
rocq makefile -f _CoqProject -o Makefile

# Build dependency submodule
if [ -d "rocq-carve" ]; then
    echo "Building rocq-carve..."
    cd rocq-carve
    if [ -f "./configure" ]; then ./configure; fi
    make -j$(nproc)
    cd ..
fi

# Build your polarized proof search logic
echo "Building main project..."
make -j$(nproc)

echo "--- SETUP COMPLETE ---" 