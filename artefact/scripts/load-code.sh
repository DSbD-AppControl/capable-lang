#!/bin/bash -eux

cat >>$HOME/.bashrc <<'EOF'
export PATH=$HOME/.nix-profile/bin:$PATH
EOF
source $HOME/.bashrc


echo "## Checking installation"

which idris2
idris2 --prefix
idris2 --paths
idris2 --libdir

echo "## Installing Artifact"

cd /tmp/
tar -zxvf /tmp/capable.tar.gz

cd "$HOME"
mv /tmp/capable "$HOME/capable"

echo "## Testing Artifact"

cd "capable"

make capable
make capable-test-run

cd "$HOME"

echo "## Finished"
