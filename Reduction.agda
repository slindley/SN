module Reduction where

open import Stuff
open import TypedLambda
open import ParallelSubstitutionTyped
open import Subst

open import Relation.Binary.PropositionalEquality renaming (subst to coerce; [_] to <_>)
open ≡-Reasoning


{-** The reduction relation **-}
infixr 2 _==>_
data _==>_ : {Gam : Cx Ty} {tau : Ty} (m : Gam !- tau) -> (m' : Gam !- tau) -> Set where

  beta :      forall {Gam sg tau} -> {m : Gam :: sg !- tau} -> {n : Gam !- sg}
          
          --  -----------------------------------------------
          ->  app (lam m) n ==> subst (sub1 n) m

  lam :       forall {Gam sg tau} {m n : Gam :: sg !- tau}
          ->  m ==> n
          --  ---------------
          ->  lam m ==> lam n

  app-fun :  forall {Gam sg tau} {m m' : Gam !- sg ->> tau} {n : Gam !- sg}
          ->  m ==> m'
          --  --------------------
          ->  app m n ==> app m' n

  app-arg :  forall {Gam sg tau} {m : Gam !- sg ->> tau} {n n' : Gam !- sg}
          ->  n ==> n'
          --  --------------------
          ->  app m n ==> app m n'

-- substitution preserves ==>
sub-red : forall {Gam Del tau i} -> {vt : VarTrm i} -> (theta : RenSub Gam Del vt) -> (m m' : Gam !- tau) -> (r : m ==> m') ->
            subst theta m ==> subst theta m'
sub-red theta (var x) m' ()
sub-red theta (lam m) (lam m') (lam r) = lam (sub-red (lift theta) m m' r)
sub-red {Gam}{Del}{tau}{vt = Var}theta (app (lam{sg = sg} m) n) .(subst (sub1 n) m) beta = r where
  p : subst (sub1 (subst theta n)) (subst (lift theta) m) ≡ subst theta (subst (sub1 n) m)
  p = begin 
          subst (sub1 (subst theta n)) (subst (lift theta) m)
        ≡⟨ comp_subst (sub1 (subst theta n)) (lift theta) m ⟩
          subst (comp (sub1 (subst theta n)) (lift theta)) m
        ≡⟨ sub1-comp theta m n ⟩
          subst (comp theta (sub1 n)) m
        ≡⟨ sym (comp_subst theta (sub1 n) m) ⟩
          subst theta (subst (sub1 n) m)
        ∎

  r : subst theta (app (lam m) n) ==> subst theta (subst (sub1 n) m)
  r = coerce (\m' -> (app (lam (subst (lift theta) m)) (subst theta n)) ==> m') p beta
sub-red {Gam}{Del}{tau}{vt = Trm}theta (app (lam{sg = sg} m) n) .(subst (sub1 n) m) beta = r where
  p : subst (sub1 (subst theta n)) (subst (lift theta) m) ≡ subst theta (subst (sub1 n) m)
  p = begin 
          subst (sub1 (subst theta n)) (subst (lift theta) m)
        ≡⟨ comp_subst (sub1 (subst theta n)) (lift theta) m ⟩
          subst (comp (sub1 (subst theta n)) (lift theta)) m
        ≡⟨ sub1-comp theta m n ⟩
          subst (comp theta (sub1 n)) m
        ≡⟨ sym (comp_subst theta (sub1 n) m) ⟩
          subst theta (subst (sub1 n) m)
        ∎

  r : subst theta (app (lam m) n) ==> subst theta (subst (sub1 n) m)
  r = coerce (\m' -> (app (lam (subst (lift theta) m)) (subst theta n)) ==> m') p beta
sub-red theta (app m n) (app m' .n) (app-fun r) = app-fun (sub-red theta m m' r)
sub-red theta (app m n) (app .m n') (app-arg r) = app-arg (sub-red theta n n' r)
