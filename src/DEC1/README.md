
## Synopsis

This projects contains the full development of DEC1, and a case study
on the verification of Pip invariants (artifact for the VSTTE18 paper). 

## Version

DEC1 language development, implemented in Coq 8.6.

## Building the project 

  run 'make'

## Language development

Contributors: Torrini (main), Nowak

* auxiliary libraries: EnvLibA.v, RelLibA, PRelLibA.v

* module type: IdModTypeA.v

* syntax and static semantics: StaticSemA.v, TRinduct.v

* dynamic semantics: DynamicSemA.v

* main proofs and interpreter: WeakenA.v, SReducA.v, TSoundnessA.V, DetermA.v, STypingA.v, SOS2GallinaB.v

* DEC1 libraries: AbbrevA.v, InvertA,v, DECauxB.v

## Code extraction

Contributors: Nowak (main), Torrini

* extraction to Haskell (read comments): Extraction.v

* Haskell extraction test: main.hs

* extraction to OCaml (read comments, not included in the general build): ExtractionOCaml.v 

## Hoare logic: 

Contributors: Torrini (main), Cherif

* preliminary: HoareA.v

* typed: THoareA.v

## Case study

Contributors: Cherif (main), Torrini, Jomaa

* module: IdModPip.v

* case study proofs:
     Hoare_getFstShadow.v, Hoare_writeVirtualInv.v, Hoare_initVAddrTable.v, Hoare_initVAddrTable_SynDir.v

## Case study: modules imported from Pip

refactored code from https://github.com/2xs/pipcore

Contributors for the original code: Jomaa (main), Nowak; refactored by Cherif

* Lib.v, Pip_DependentTypeLemmas.v, Pip_InternalLemmas.v, Pip_Prop.v,
  Pip_stateLib.v, Pip_writeVirtualInv_Lemmas.v

## Testing

Contributors: Torrini, Cherif, Nowak

* modules: ModNat1A.v, ModLEnvA.v, ModNEnvA.v

* test functions: Test_Nat1A.v, TestLEnvA.v, Test_Convert.v

## Contributors

for the development of DEC1:

* Paolo Torrini <paolo.torrini@univ-lille1.fr>

* David Nowak <david.nowak@univ-lille1.fr>

for the case study on Pip:

* Mohamed Sami Cherif <mohamedsami.cherif@yahoo.com>

* Narjes Jomaa <Narjes.Jomaa@univ-lille1.fr>

## Licence

  The source code is covered by a CeCILL-A licence.
