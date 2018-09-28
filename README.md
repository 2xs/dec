
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
with respect to its operational semantics, and its translation to
CompCert C (using CompCert-3.0.1).


## Coq version

Coq 8.6.

## Content

* src/langspec: language definition of DEC1

* src/DEC1: full language development of DEC1 with 
            case study on the verification of Pip invariants

* src/DEC2: full language development of DEC2 with
            translation to CompCert C

## Documentation

* documentation on DEC1 in doc: 
          DEC1_spec.tex (language specification),
	  vstte2018.pdf (VSTTE 2018 paper),
	  vstte2018_slides.pdf (VSTTE 2018 slides),
	  MSCherif_project_report.pdf (BSc student project report)

* documentation on DEC2 in doc: 
          ENTROPY18_DEC2_slides.pdf (ENTROPY 2018 slides on DEC2),
          DEC2_notes.pdf (introduction and reflection in Gallina),
	  DEC2_to_CompCertC_info_txt (translation to CompCert C),
	  Gallina_to_DEC2_spec.txt (on translating from Gallina to DEC2)

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

## Information on modules in src/DEC2

   see src/DEC2/README.md

## Building DEC1 documentation and language specification

* run './make2file' to create the Makefile, then 'make' to build the project

* run './makedoc' to generate the pdf documentation (in doc, requires
  pdflatex) and the coqdoc html documentation (in coqdoc)

## Building DEC1 (see DEC1/README.md)

  go to src/DEC1/ and run 'make'

## Building DEC2 (see DEC2/README.md) 

  go to src/DEC2/ and run 'make'

## Contributors


The developers of DEC1 are

* Paolo Torrini <paolo.torrini@univ-lille.fr> 

* David Nowak <david.nowak@univ-lille.fr>

Case study contributors:

* Mohamed Sami Cherif <mohamedsami.cherif@yahoo.com> 

* Narjes Jomaa <Narjes.Jomaa@univ-lille.fr>


The developer of DEC2 is Paolo Torrini <ptorrx@gmail.com>


## Licence

  The source code is covered by a CeCILL-A licence.
