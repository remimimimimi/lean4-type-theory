## lambda-calculus-typecheckers
Implementation of typecheckers (not only) for different lambda calculus type systems with proof of correctness.

### Project structure

- stlc (Simple typed lambda calculus)

## Build and run

The only prerequisite is `opam`:

``` sh
cd NAME_OF_TYPE_SYSTEM_PROJECT 
opam init # for first usage
opam install . --deps-only
dune build
```

