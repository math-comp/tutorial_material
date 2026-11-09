<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# tutorial_material

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/math-comp/tutorial_material/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/tutorial_material/actions/workflows/docker-action.yml





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
- Additional dependencies:
  - [MathComp ssreflect 2.6 or later](https://math-comp.github.io)
- Rocq/Coq namespace: `tutorial_material`
- Related publication(s): none

## Building and installation instructions

To build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/math-comp/tutorial_material.git
cd tutorial_material
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



