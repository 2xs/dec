
## Synopsis

This projects contains the definition and the development of DEC, a
functional imperative language with bounded recursion and generic
side-effects embedded in Coq.

DEC has been designed as an intermediate language to support the
translation to C of the Pip protokernel
(https://github.com/2xs/pipcore).

## Version

DEC 1.0 language specification, implemented in Coq 8.6.

## Content

* src/langspec: language definition 

* src/DEC1: full language development with proofs 
            and case study on the verification of Pip invariants
  
  (ITP 2018 submission: see src/DEC1/README.md)

## Coq modules in src/langspec

* EnvLib.v: auxiliary library

* ModTyp.v: module type

* BaseMod.v: base module

* LangSpec.v: language specification including

  + syntax definition

  + static semantics

  + small-step dynamic semantics

## Information on modules in src/DEC1

   see src/DEC1/README.md

## Building the language specification

* run './make2file' to create the Makefile, then 'make' to build the project

* run './makedoc' to generate the pdf documentation (in doc, requires
  pdflatex) and the coqdoc html documentation (in coqdoc)

## Building the full language inclusive of case study and tests

  go to src/DEC1/ and run 'make'

## Contributors

The developers of DEC are

* Paolo Torrini <paolo.torrini@univ-lille1.fr>

* David Nowak <david.nowak@univ-lille1.fr>

Case study contributors:

* Mohamed Sami Cherif <mohamedsami.cherif@yahoo.com>

* Narjes Jomaa <Narjes.Jomaa@univ-lille1.fr>

## Licence

  The source code is covered by a CeCILL-A licence.
