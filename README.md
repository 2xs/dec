
## Synopsis

This project contains the development of the two distinct languages,
DEC1 and DEC2, both functional imperative languages with bounded
recursion and generic side-effects, deeply embedded in Coq. Both
languages are specified in terms of small-step semantics (SOS).

The DEC languages have been designed as intermediate languages to
support the translation to C of the Pip protokernel (Pip is available
at https://github.com/2xs/pipcore).

The development of DEC1 includes a Hoare logic and a verification case
study discussed in a VSTTE 2018 paper (see the documentation folder
for a version of the paper and the slides).

DEC2 includes a proof of the adequacy of its reflection in Gallina
with respect to its operational semantics.


## Coq version

Coq 8.6.

## Content

* src/langspec: language definition of DEC1

* src/DEC1: full language development of DEC1 with 
            case study on the verification of Pip invariants

* src/DEC2: full language development of DEC2 


## VSTTE 2018 artifact (DEC1)

see src/DEC1/README.md

## Coq modules in src/langspec (DEC1)

* EnvLib.v: auxiliary library

* ModTyp.v: module type

* BaseMod.v: base module

* LangSpec.v: DEC1 language specification including

  + syntax definition

  + static semantics

  + small-step dynamic semantics

## Information on modules in src/DEC1

   see src/DEC1/README.md

## Building DEC1 documentation and language specification

* run './make2file' to create the Makefile, then 'make' to build the project

* run './makedoc' to generate the pdf documentation (in doc, requires
  pdflatex) and the coqdoc html documentation (in coqdoc)

## Building DEC1

  go to src/DEC1/ and run 'make'

## Building DEC2

  go to src/DEC2/ and run 'make'

## Contributors

The developers of DEC1 are

* Paolo Torrini <paolo.torrini@univ-lille1.fr> 

* David Nowak <david.nowak@univ-lille1.fr>

Case study contributors:

* Mohamed Sami Cherif <mohamedsami.cherif@yahoo.com> 

* Narjes Jomaa <Narjes.Jomaa@univ-lille1.fr>


DEC2 is developed by Paolo Torrini.


## Licence

  The source code is covered by a CeCILL-A licence.
