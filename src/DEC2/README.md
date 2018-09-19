
## Synopsis

This projects contains the full development of DEC2, inclusive of its
translation to CompCert C.

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


## Contributor

* Paolo Torrini <ptorrx@gmail.com>

## Licence

  The source code is covered by a CeCILL-A licence.
