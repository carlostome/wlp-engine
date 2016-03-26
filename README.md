# WLP-engine

Weakest liberal precondition for GCL programs.

# Installation

1.  Download and install the Haskell platform for your operating system.
    The Haskell platform can be found in \url{https://www.haskell.org/platform/}. 
    The three main platforms, Window, Mac OS X and Linux are supported.

2. Install the Stack\footnote{For more information please visit
   \url{http://docs.haskellstack.org/en/stable/index.html}.} tool from the hackage
   repository with the next steps.  This need to be done from a terminal with the
   Haskell platform available in the path.

```bash
          cabal update
          install stack
```

3. Clone this repository or extract the source code and cd into
   the directory.

4. Build the project with `stack build`

# Usage

The easiest way to play with this library is to use it in a live ghci session.
In order to do so, just type `stack ghci` in the project folder.

