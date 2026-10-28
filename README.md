<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Plouffe

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/plouffe/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/plouffe/actions/workflows/docker-action.yml




Computing Pi decimal using Plouffe Formula in Rocq

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Rocq/Coq versions: 9.2 or later
- Additional dependencies:
  - [Bignums](https://github.com/coq/bignums) same version as Rocq
  - [MathComp ssreflect 2.6 or later](https://math-comp.github.io)
  - [Coquelicot 3.4.5 or later](https://gitlab.inria.fr/coquelicot/coquelicot)
- Rocq/Coq namespace: `plouffe`
- Related publication(s): none

## Building and installation instructions

To build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/thery/plouffe.git
cd plouffe
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



