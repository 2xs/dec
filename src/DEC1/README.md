
## Synopsis

This projects contains the full development of DEC, and a case study
on the verification of Pip invariants.

## Version

DEC 1.0 language development, implemented in Coq 8.6.

## Building the project

  run 'make'

## Language development

Contributors: Torrini (main), Nowak

* auxiliary libraries: EnvLibA.v, RelLibA, PRelLibA.v

* module type: IdModTypeA.v

* syntax and static semantics: StaticSemA.v, TRinduct.v

* dynamic semantics: DynamicSemA.v

* main proofs: WeakenA.v, SReducA.v, TSoundnessA.V, DetermA.v, STypingA.v

* DEC libraries: AbbrevA.v, InvertA,v, DECauxB.v

## Code extraction

Contributors: Nowak (main), Torrini

* Extraction.v

## Hoare logic: 

Contributors: Torrini (main), Cherif

* preliminary: HoareA.v

* typed: THoareA.v

## Case study

Contributors: Cherif (main), Jomaa, Torrini

* module: IdModPip.v

* case study proofs:
     Hoare_getFstShadow.v, Hoare_writeVirtualInv.v, Hoare_initVAddrTable.v

## Case study: modules imported from Pip

refactoring of code from https://github.com/2xs/pipcore

Contributors: Jomaa (main), Nowak, refactored by Cherif

* Lib.v, Pip_DependentTypeLemmas.v, Pip_InternalLemmas.v, Pip_Prop.v,
  Pip_stateLib.v, Pip_writeVirtualInv_Lemmas.v

## Testing

Contributors: Torrini, Cherif, Nowak

* modules: ModNat1A.v, ModLEnvA.v, ModNEnvA.v

* test functions: Test_Nat1A.v, TestLEnvA.v, Test_Convert.v

## Contributors

for the development of DEC:

* Paolo Torrini <paolo.torrini@univ-lille1.fr>

* David Nowak <david.nowak@univ-lille1.fr>

for the case study on Pip:

* Mohamed Sami Cherif <mohamedsami.cherif@yahoo.com>

* Narjes Jomaa <Narjes.Jomaa@univ-lille1.fr>

## Licence

  The source code is covered by a CeCILL-A licence.
