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
- Compatible Coq versions: 9.0 or later
- Additional dependencies:
  - [Bignums](https://github.com/coq/bignums) same version as Rocq
  - [MathComp ssreflect 2.4 or later](https://math-comp.github.io)
  - [Coquelicot 3.4.3 or later](https://gitlab.inria.fr/coquelicot/coquelicot)
- Coq namespace: `plouffe`
- Related publication(s): none

## Building and installation instructions

To build and install manually, do:

``` shell
git clone https://github.com/thery/plouffe.git
cd plouffe
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



