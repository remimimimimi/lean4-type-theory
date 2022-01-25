## lambda-calculus-typecheckers
Implementation of typecheckers (not only) for different lambda calculus type systems with proof of correctness.

### Project structure

- Simple typed lambda calculus (stlc)
- Polymorphic lambda calculus (systemf) 

## Build and run

The only prerequisite is `opam`:

``` sh
opam init # for first usage
cd NAME_OF_TYPE_SYSTEM_PROJECT 
opam install . --deps-only
dune build
```

