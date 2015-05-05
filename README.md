The `hoopl` Package  [![Hackage](https://img.shields.io/hackage/v/hoopl.svg)](https://hackage.haskell.org/package/hoopl) [![Build Status](https://travis-ci.org/haskell/hoopl.svg)](https://travis-ci.org/haskell/hoopl)
===================

## Hoopl: A Higher-Order OPtimization Library

API documentation can be found on [Hackage](https://hackage.haskell.org/package/hoopl).

| Directory      | Contents
| -------------- | ---------
| `paper/`       | A paper about Hoopl
| `prototypes/`  | A sampling of prototypes and early designs
| `src/`         | The current official sources to the Cabal package
| `testing/`     | Tests, including a sample client.  See [`testing/README`](testing/README)

### Development Notes

To build the library, change to the src directory and run

    cabal configure --prefix=$HOME --user   # we have no idea what this means
    cabal build
    cabal install --enable-documentation

To run the tests in the folder testing/, change to the src directory and run 

    cabal configure --enable-tests
    cabal test

To run the tests with the test coverage report, change to the src directory and run 

    cabal configure --enable-tests -f testcoverage
    cabal test

You'll need a Haskell Platform, which should include appropriate
versions of Cabal and GHC.

### Checklist for Making Releases

In order to facilitate GHC development's workflow, the version in [`hoopl.cabal`](hoopl.cabal) is to be bumped as soon as a change requires a respective version bump (according to the PVP) relative to the last released `hoopl` version.

1. Make sure `hoopl` passes Travis for all GHC versions in the build-matrix
2. Update Changelog (& `git commit`)
3. Generate source tarball via `cabal sdist` and upload a candidate to Hackage (see note below), and inspect the result. 
4. If everything checks out, make an annotated and GPG-signed Git release tag: `git tag -a -s v${VER} -m "hoopl ${VER}"`
5. Publish (there's a button for that on Hackage) the package candidate
6. Work on next release

Note: To upload to Hackage,

    cabal sdist
    cabal upload dist/hoopl-*.tar.gz

However, it's recommended use the Hackage feature for
[uploading a candidate](http://hackage.haskell.org/packages/candidates/upload).
