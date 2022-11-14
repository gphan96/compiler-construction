# Installation

We will use the following software:

  - GHC (included, e.g., in Haskell-Platform or stack)
  - cabal (included, e.g., in Haskell-Platform or stack)
  - stack (includes necessary Haskell Modules)
  - BNFC
  - llvm
  - make
  - alex (optional, for Haskell; included in Haskell-Platform)
  - happy (optional, for Haskell; included in Haskell-Platform)
  - llvm-general (optional, for Haskell)
  - clang (optional, for C++)
  - bison (optional, for C++)
  - flex (optional, for C++)
    
We will use the BNFC tool to generate a parser and code snippets for the language of your choice, and the make tool to control the compilation process. Please make sure you have the make tool installed before proceeding. The BNFC tool is written in the Haskell programming language and, therefore, you will need a working Haskell installation to compile BNFC.

We recommend that you setup Ubuntu 18.04 or a similar Linux system in order to work on your compiler construction project. You may install Ubuntu within a virtual machine, e.g. using VirtualBox16. On such Linux distributions, the above-mentioned software can be installed using the following sequence of commands:
```console
sudo apt-get update
sudo apt-get -y install build-essential llvm-9 clang-9 libedit-dev libgmp-dev bison flex libz-dev ghc curl
curl -sSL https://get.haskellstack.org/ | sh
echo "export PATH=${HOME}/.local/bin:${PATH}" >> ${HOME}/.bashrc
export PATH=${HOME}/.local/bin:${PATH}
stack --resolver lts-14.0 --install-ghc install BNFC alex happy
```

# Run & test

Use the following command to let bnfc generate its code in a subfolder called bnfc:
```console
bnfc -o bnfc -m CPP.cf
```

And for testing:
```console
./run_tests -all
```
to run all tests in the test directory. **For additional tests** the expected output **has to be defined.**
