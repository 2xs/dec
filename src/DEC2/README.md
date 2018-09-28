
## Synopsis

This projects contains the full development of DEC2, inclusive of its
reflection in Gallina and of its translation to CompCert C.

An informal outline of the translation to CompCert C, that can be used
to generate CompCert C programs from DEC2 ones, can be found in the
documentation (DEC2_to_CompCertC_info.txt).


## Version

DEC2 language development, implemented in Coq 8.6.

## To build the project without the translation to CompCert C

  run 'make'

To build the translation, CompCert needs to be installed.  Assuming
you have installed CompCert-3.0.1 in ~/lib, you can compile the
translation by

  coqc CTransI1.v

If your CompCert has a different version or a different location you
need to edit the Add LoadPath line of CTransI1.v. 

You can run a set of test cases of the translation to CompCert C,
first loading a testing module

  coqc ModNat1I1.v

and then running the tests

  coqc CTestI1.v


## Language development

* general auxiliary libraries: AuxLibI1.v, CHeadAuxI1.v

* module type: ModTypI1.v

* syntax: TypSpecI1.v, LangSpecI1.v

* static semantics: StaticSemI1.v

* dynamic semantics and SOS interpreter: DynamicSemI1.v, DerivDynI1.v,
  UniqueTypI1.v, WeakenA.v, TransPrelimI1.v, TSoundnessI1.v,
  SReducI1.v, DetermI1.v

* reflection in Gallina: PreReflI1.v, ReflectI1.v

* adequacy of SOS with respect to reflection: PreInterI1.v,
  InterpBaseI1.v, InterpretI1.v

* translation to CompCert C: CTransI1.v

* testing: ModNat1I1.v. CTestI1.v


## Contributor

* Paolo Torrini <ptorrx@gmail.com>

## Licence

  The source code is covered by a CeCILL-A licence.
