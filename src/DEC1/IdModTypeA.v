Require Import EnvLibA.


Module Type IdModType.

Parameter Id : Type.

Parameter IdEqDec : forall (x y : Id), {x = y} + {x <> y}.

Instance IdEq : DEq Id :=
{
  dEq := IdEqDec
}.

Parameter W : Type.

Parameter Loc_PI : forall (T: Type) (p1 p2: ValTyp T), p1 = p2.

Parameter BInit : W.

Instance WP : PState W :=
{
  loc_pi := Loc_PI;
  
  b_init := BInit
}.              
  
End IdModType.

