<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# tutorial_material

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/math-comp/tutorial_material/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/tutorial_material/actions?query=workflow:"Docker%20CI"





## Tutorial materials

Scripts associated to tutorials for mathcomp.

It contains
- [AnIntroductionToSmallScaleReflectionInCoq](https://github.com/math-comp/tutorial_material/blob/master/AnIntroductionToSmallScaleReflectionInCoq) associated to [An Introduction To Small Scale Reflection In Coq](https://hal.inria.fr/inria-00515548v4/document)
- [AnSsreflectTutorial](https://github.com/math-comp/tutorial_material/blob/master/AnSsreflectTutorial) associated to [An Ssreflect Tutorial](https://hal.inria.fr/inria-00407778)
- [SummerSchoolSophia](https://github.com/math-comp/tutorial_material/tree/master/SummerSchoolSophia) associated to a [5-day School](https://team.inria.fr/marelle/en/coq-winter-school-2018/) on Mathematical Components at Sophia-Antipolis

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.18 or later
- Additional dependencies:
  - [MathComp ssreflect 2.1 or later](https://math-comp.github.io)
- Coq namespace: `tutorial_material`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of tutorial_material
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-tutorial_material
```

To instead build and install manually, do:

``` shell
git clone https://github.com/math-comp/tutorial_material.git
cd tutorial_material
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



