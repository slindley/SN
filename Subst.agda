module Subst where

open import Stuff
open import TypedLambda
open import ParallelSubstitutionTyped

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality renaming (subst to coerce; [_] to <_>)
open ≡-Reasoning

{-** substitution stuff **-}

-- strengthen a renaming
str : forall {Gam Del sg} -> Ren (Gam :: sg) Del -> Ren Gam Del
str pi x = pi (suc x)

rename : forall {Gam Del} (pi : Ren Gam Del) {tau} -> Gam !- tau -> Del !- tau
rename pi = subst pi

sub : forall {Gam Del i} -> {vt : VarTrm i} -> RenSub Gam Del vt -> Sub Gam Del
sub {vt = Var} theta x = var (theta x)
sub {vt = Trm} theta x = theta x

sub1 : forall {Gam sg} -> Gam !- sg -> Sub (Gam :: sg) Gam
sub1 n zero    = n
sub1 n (suc x) = var x

-- id-sub : forall {Gam i} -> {vt : VarTrm i} -> RenSub Gam Gam vt
-- id-sub {vt = Var} = id
-- id-sub {vt = Trm} = var

-- perhaps we can rationalise the following definitions

lift-id' : forall {Gam sg tau} -> (x : tau <: Gam :: sg) -> lift id x ≡ x
lift-id' zero    = refl
lift-id' (suc x) = refl

lift-id : (Gam : Cx Ty) (sg : Ty) ->
    (\ {tau : Ty} (x : tau <: Gam :: sg) -> lift id x)
  ≡
    (\ {tau : Ty} (x : tau <: Gam :: sg) -> x)
lift-id Gam sg = impl-fun-ext (\tau -> fun-ext (lift-id'{tau = tau}))

sub-lift-id : forall {Gam sg tau} -> (m : Gam :: sg !- tau) -> subst (lift id) m ≡ subst id m
sub-lift-id {Gam}{sg}{tau} m = cong (\theta -> subst (\{tau} -> theta{tau}) m) (lift-id Gam sg)

rename-id :
  forall {Gam tau} ->
    (m : Gam !- tau) ->
       subst id m ≡ m
rename-id (var x) = refl
rename-id (lam m) = cong lam (coerce (\n -> subst (lift id) m ≡ n) (rename-id m) (sub-lift-id m))
rename-id (app m n) rewrite rename-id m | rename-id n = refl

lift-var' : forall {Gam sg tau} -> (x : tau <: Gam :: sg) -> lift var x ≡ var x
lift-var' zero    = refl
lift-var' (suc x) = refl

lift-var : (Gam : Cx Ty) (sg : Ty) ->
    (\ {tau : Ty} (x : tau <: Gam :: sg) -> lift var x)
  ≡
    (\ {tau : Ty} (x : tau <: Gam :: sg) -> var x)
lift-var Gam sg = impl-fun-ext (\tau -> fun-ext (lift-var'{tau = tau}))

sub-lift-var : forall {Gam sg tau} -> (m : Gam :: sg !- tau) -> subst (lift var) m ≡ subst var m
sub-lift-var {Gam}{sg}{tau} m = cong (\theta -> subst (\{tau} -> theta{tau}) m) (lift-var Gam sg)

sub-var : forall {Gam tau} -> (m : Gam !- tau) -> subst var m ≡ m
sub-var (var x) = refl
sub-var (lam m) = cong lam (coerce (\n -> subst (lift var) m ≡ n) (sub-var m) (sub-lift-var m))
sub-var (app m n) rewrite sub-var m | sub-var n = refl

str-suc :
  forall {Gam Del sg tau} ->
    (pi : Ren (Gam :: sg) Del)
      (m : Gam !- tau) ->
        subst (str pi) m ≡ subst pi (subst suc m)
str-suc pi (var zero) = refl
str-suc pi (var (suc x)) = refl
str-suc pi (lam m) = begin
    lam (subst (lift (str pi)) m)
  ≡⟨ refl ⟩
    lam (subst (lift (comp pi suc)) m)
  ≡⟨ sym (cong (\theta' -> lam (subst (\{tau} -> theta'{tau}) m)) (comp_lift pi suc)) ⟩
    lam (subst (comp (lift pi) (lift suc)) m)
  ≡⟨ sym (cong lam (comp_subst (lift pi) (lift suc) m)) ⟩
    lam (subst (lift pi) (subst (lift suc) m))
  ∎
str-suc pi (app m n) rewrite str-suc pi m | str-suc pi n = refl

{-** more substitution lemmas **-}
sub1-suc :
  forall {Gam sg} -> (n : Gam !- sg) ->
    (\{tau} -> comp (sub1 n) suc {tau}) ≡ var
sub1-suc n = impl-fun-ext (\tau -> fun-ext (λ x → refl) )

sub1-lift-var :
  forall {Gam Del sg tau i} -> {vt : VarTrm i} -> (theta : RenSub Gam Del vt) -> (x : tau <: Gam :: sg) -> (n : Gam !- sg) ->
    comp (sub1 (subst theta n)) (sub (lift theta)) x ≡ comp theta (sub1 n) x
sub1-lift-var {vt = Var} theta zero n = refl
sub1-lift-var {vt = Trm} theta zero n = refl
sub1-lift-var {vt = Var} theta (suc x) n = begin
    subst (sub1 (subst theta n)) (subst (\{tau} -> suc) (var (theta x)))
  ≡⟨ comp_subst (sub1 (subst theta n)) suc (var (theta x)) ⟩
    var (theta x)
  ≡⟨ refl ⟩
    subst theta (sub1 n (suc x))
  ≡⟨ refl ⟩
    comp theta (sub1 n) (suc x)
  ∎
sub1-lift-var {vt = Trm} theta (suc x) n = begin
    subst (sub1 (subst theta n)) (subst suc (theta x))
  ≡⟨ comp_subst (sub1 (subst theta n)) suc (theta x) ⟩
    subst (comp (sub1 (subst theta n)) (\{tau} -> suc)) (theta x)
  ≡⟨ cong (\theta' -> subst (\{tau} -> theta'{tau}) (theta x)) (sub1-suc (subst theta n)) ⟩
    subst var (theta x)
  ≡⟨ sub-var (theta x) ⟩
    theta x
  ≡⟨ refl ⟩
    subst theta (sub1 n (suc x))
  ≡⟨ refl ⟩
    comp theta (sub1 n) (suc x)
  ∎

sub1-lift :
  forall {Gam Del sg i} -> {vt : VarTrm i} -> (theta : RenSub Gam Del vt) -> (n : Gam !- sg) ->
    (\{tau} -> (comp (sub1 (subst theta n)) (sub (lift theta))){tau}) ≡ comp theta (sub1 n)
sub1-lift theta n = impl-fun-ext (\tau -> fun-ext (\x -> sub1-lift-var theta x n))

sub1-comp :
  forall {Gam Del sg tau i} -> {vt : VarTrm i} -> (theta : RenSub Gam Del vt) -> (m : Gam :: sg !- tau) -> (n : Gam !- sg) ->
    subst (comp (sub1 (subst theta n)) (sub (lift theta))) m ≡ subst (comp theta (sub1 n)) m
sub1-comp theta m n = cong (\theta' -> subst (\{tau} -> theta'{tau}) m) (sub1-lift theta n)
