
## Synopsis

This projects contains the development of DEC, and a case study on the
verification of Pip invariants.

## Version

DEC 1.0 language development, implemented in Coq 8.6.

## Language development modules

* auxiliary libraries: EnvLibA.v, RelLibA, PRelLibA.v, DECaux.v 

* module type: IdModTypeA.v

* static semantics: StaticSemA.v, TRinduct.v

* dynamic semantics: DynamicSemA.v

* proofs: WeakenA.v, SReducA.v, TSoundnessA.V, DetermA.v, STypingA.v

* definitions: AbbrevA.v

* extraction: Extraction.v

* Hoare logic: InvertA.v HoareA.v, THoareA.v

## Case study modules

* module: IdModPip.v

* case study proofs:
     Hoare_getFstShadow.v, Hoare_writeVirtualInv.v, Hoare_initVAddrTable.v

* modules imported from Pip:
     Lib.v, Pip_DependentTypeLemmas.v, Pip_InternalLemmas.v, Pip_Prop.v,
     Pip_stateLib.v, Pip_writeVirtualInv_Lemmas.v

## Testing modules

* modules: ModNat1A.v, ModLEnvA.v, ModNEnvA.v

* tests: Test_Nat1A.v, TestLEnvA.v, Test_Convert.v

## Building the full project

  simply run 'make'

## Contributors

The developers of DEC are

* Paolo Torrini <paolo.torrini@univ-lille1.fr>

* David Nowak <david.nowak@univ-lille1.fr>

Case study contributors:

* Mohamed Sami Cherif <mohamedsami.cherif@yahoo.com>

* Narjes Jomaa <Narjes.Jomaa@univ-lille1.fr>

## Licence

  The source code is covered by a CeCILL-A licence.
