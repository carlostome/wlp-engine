# WLP-engine

Weakest liberal precondition for GCL programs.

# Installation

1.  Download and install the Haskell platform for your operating system.
    The Haskell platform can be found in https://www.haskell.org/platform/. 
    The three main platforms, Window, Mac OS X and Linux are supported.

2. Install the Stack tool from the hackage repository with the next steps.
   This need to be done from a terminal with the Haskell platform available in
   the path.

```bash
cabal update
cabal install stack
```

3. Clone this repository or extract the source code.

```bash
git clone https://github.com/carlostome/wlp-engine.git
```

4. cd into the project and build the project with `stack build`.

# Usage

The easiest way to play with this library is to use it in a live ghci session.
In order to do so, just type `stack ghci` in the project folder.

