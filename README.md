
## Synopsis

This projects contains the development of DEC, an imperative
functional language with bounded recursion and generic side-effects
embedded in Coq.

DEC has been designed as an intermediate language to support the
translation to C of the Pip protokernel
(https://github.com/2xs/pipcore).

## Version

DEC 1.0 language specification, implemented in Coq 8.6.

## Coq modules (src/langspec)

* EnvLib.v: auxiliary library

* ModTyp.v: module type

* BaseMod.v: base module

* LangSpec.v: language specification including

  + syntax definition

  + static semantics

  + small-step dynamic semantics

## Building the project

* run './make2file' to create the Makefile, then 'make' to build the project

* run './makedoc' to generate the pdf documentation (in doc, requires
  pdflatex) and the coqdoc html documentation (in coqdoc)

## Contributors

The DEC development team is

* Paolo Torrini <paolo.torrini@univ-lille1.fr>

* David Nowak <david.nowak@univ-lille1.fr>

## Licence

The source code is covered by a CeCILL-A licence.
