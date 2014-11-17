module ReductionMany where

open import Stuff
open import TypedLambda
open import ParallelSubstitutionTyped
open import Subst
open import Reduction

open import Relation.Binary.PropositionalEquality renaming (subst to coerce; [_] to <_>)
open ≡-Reasoning

{-** Transitive reflexive closure of the reduction relation **-}
infixr 2 _==>*_
data _==>*_ : {Gam : Cx Ty} {tau : Ty} (m : Gam !- tau) -> (m' : Gam !- tau) -> Set where

  none : forall {Gam tau} -> {m : Gam !- tau} -> m ==>* m

  one : forall {Gam tau} -> {m m' : Gam !- tau} -> m ==> m' -> m ==>* m'

  many : forall {Gam tau} -> {m m' m'' : Gam !- tau} -> m ==>* m' -> m' ==>* m'' -> m ==>* m'' 

-- substitution preserves ==>*
sub-red* : forall {Gam Del tau i} -> {vt : VarTrm i} -> (theta : RenSub Gam Del vt) -> (m m' : Gam !- tau) -> (r : m ==>* m') ->
            subst theta m ==>* subst theta m'
sub-red* theta m .m none = none
sub-red* theta m m' (one r) = one (sub-red theta m m' r)
sub-red* theta m m' (many rs rs') = many (sub-red* theta m _ rs) (sub-red* theta _ m' rs')


app-fun* :
  forall {Gam sg tau} ->
    {m m' : Gam !- sg ->> tau} ->
    {n : Gam !- sg} ->
      m ==>* m' ->
       app m n ==>* app m' n
app-fun* none          = none
app-fun* (one r)       = one (app-fun r)
app-fun* (many rs rs') = many (app-fun* rs) (app-fun* rs')

app-arg* :
  forall {Gam sg tau} ->
    {m : Gam !- sg ->> tau} ->
    {n n' : Gam !- sg} ->
      n ==>* n' ->
       app m n ==>* app m n'
app-arg* none          = none
app-arg* (one r)       = one (app-arg r)
app-arg* (many rs rs') = many (app-arg* rs) (app-arg* rs')

lam* : 
  forall {Gam sg tau} ->
    {m m' : Gam :: sg !- tau} ->
      m ==>* m' ->
       lam m ==>* lam m'
lam* none          = none
lam* (one r)       = one (lam r)
lam* (many rs rs') = many (lam* rs) (lam* rs')

_++_ : Cx Ty -> Cx Ty -> Cx Ty
Gam ++ Em = Gam
Gam ++ (Del :: x) = (Gam ++ Del) :: x

-- generalised weakening
lift* : forall {Gam Del i} -> {vt : VarTrm i} -> (Phi : Cx Ty) -> RenSub Gam Del vt -> RenSub (Gam ++ Phi) (Del ++ Phi) vt
lift* Em         theta = theta
lift* (Phi :: _) theta = lift (lift* Phi theta)

-- this seems to be the one place we require genuine weakening as
-- opposed to more general renaming

-- substitutions simulate reduction of the substituted term
sub-arg-red :
  forall {Gam sg tau} -> (Del : Cx Ty) ->
    (m : (Gam :: sg) ++ Del !- tau) ->
      (n n' : Gam !- sg) ->
        (r : n ==> n') ->
          subst (lift* Del (sub1 n)) m ==>* subst (lift* Del (sub1 n')) m
sub-arg-red Em (var zero) n n' r = one r
sub-arg-red Em (var (suc x)) n n' r = none
sub-arg-red (Del :: tau) (var zero) n n' r = none
sub-arg-red (Del :: tau) (var (suc x)) n n' r =
  sub-red* suc (lift* Del (sub1 n) x) (lift* Del (sub1 n') x) (sub-arg-red Del (var x) n n' r)
sub-arg-red {Gam}{sg}{sg' ->> tau} Del (lam m) n n' r = lam* (sub-arg-red (Del :: sg') m n n' r)
sub-arg-red Del (app m m') n n' r =
  many (app-fun* (sub-arg-red Del m n n' r)) (app-arg* (sub-arg-red Del m' n n' r))
