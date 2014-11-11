module SN where

open import TypedLambda
open import ParallelSubstitutionTyped
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality renaming (subst to coerce; [_] to <_>)
open ≡-Reasoning

-- standard stuff
postulate
  fun-ext : forall {i j}{X : Set i}{Y : X -> Set j}
              {f g : (x : X) -> Y x} ->
              ((x : X) -> f x ≡ g x) ->
              f ≡ g
  impl-fun-ext :
      forall {i j}{X : Set i}{Y : X -> Set j} ->
        {f g : {x : X} -> Y x} ->
        ((x : X) -> f {x} ≡ g {x}) ->
        (\{x} -> f {x}) ≡ g

Not : forall {X : Set} -> (P : X -> Set) -> Set
Not P = forall {x} -> P x -> ⊥

data List {l}(X : Set l) : Set l where
  <>    :                 List X
  _,_   : X -> List X ->  List X

_o_ : forall {i j k}
        {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k} ->
        (f : {a : A}(b : B a) -> C a b) ->
        (g : (a : A) -> B a) ->
        (a : A) -> C a (g a)
f o g = \ a -> f (g a)

id : forall {k}{X : Set k} -> X -> X
id x = x

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

{-** Transitive reflexive closure of the reduction relation **-}
infixr 2 _==>*_
data _==>*_ : {Gam : Cx Ty} {tau : Ty} (m : Gam !- tau) -> (m' : Gam !- tau) -> Set where

  none : forall {Gam tau} -> {m : Gam !- tau} -> m ==>* m

  one : forall {Gam tau} -> {m m' : Gam !- tau} -> m ==> m' -> m ==>* m'

  many : forall {Gam tau} -> {m m' m'' : Gam !- tau} -> m ==>* m' -> m' ==>* m'' -> m ==>* m'' 


-- inductive characerisation of weak normalisation
data WN : {Gam : Cx Ty} {tau : Ty} (m : Gam !- tau) -> Set where
  stop : forall {Gam tau m}   -> Not (\n -> m ==> n) -> WN{Gam}{tau} m
  step : forall {Gam tau m n} -> m ==> n -> WN{Gam}{tau} n -> WN m

-- inductive characterisation of strong normalisation
mutual
  data SN : {Gam : Cx Ty} {tau : Ty} (m : Gam !- tau) -> Set where
    step : forall {Gam tau m} -> SN'{Gam}{tau} m -> SN m

  SN' : {Gam : Cx Ty} {tau : Ty} (m : Gam !- tau) -> Set
  SN' m = forall {n} -> m ==> n -> SN n

unstep : forall {Gam tau} -> {m : Gam !- tau} -> SN m -> SN' m
unstep (step g) = g

sn-lam : forall {Gam sg tau m} -> SN{Gam :: sg}{tau} m -> SN{Gam}{sg ->> tau} (lam m)
sn-lam m-nf = step (sn-lam' m-nf) where
  sn-lam' : forall {Gam sg tau m} -> SN{Gam :: sg}{tau} m -> SN'{Gam}{sg ->> tau} (lam m)
  sn-lam' (step g) (lam r) = step (sn-lam' (g r))

-- sn-unlam : forall {Gam sg tau m} -> SN{Gam}{sg ->> tau} (lam m) -> SN{Gam :: sg}{tau} m
-- sn-unlam lam-nf = step (sn-unlam' lam-nf) where
--   sn-unlam' : forall {Gam sg tau m} -> SN{Gam}{sg ->> tau} (lam m) -> SN'{Gam :: sg}{tau} m
--   sn-unlam' (step g) r = step (sn-unlam' (g (lam r)))

-- sn-app-var : forall {Gam sg tau m} -> (x : sg ->> tau <: Gam) -> SN m -> SN (app (var x) m)
-- sn-app-var {m = m} x (step g) = step g' where
--   g' : forall {n} -> app (var x) m ==> n -> SN n
--   g' (app-fun ())
--   g' (app-arg r) = sn-app-var x (g r)

-- given a strongly normalising (or weakly normalising) term, we can
-- normalise it by picking a reduction order (this is not part of the
-- strong normalisation proof)

-- perform at most one normal-order reduction
reduce : forall {Gam tau} -> (m : Gam !- tau) -> Maybe (Σ[ n ∈ Gam !- tau ] m ==> n)
reduce (var x)   = nothing
reduce (lam m) with reduce m
reduce (lam m) | just (m' , f) = just (lam m' , lam f)
reduce (lam m) | nothing = nothing
reduce (app m n) with reduce m
reduce (app m n) | just (m' , f) = just (app m' n , app-fun f)
reduce (app m n) | nothing with reduce n 
reduce (app m n) | nothing | just (n' , f) = just (app m n' , app-arg f)
reduce (app m n) | nothing | nothing = nothing

-- weak normalisation
norm-wn : forall {Gam tau} -> (m : Gam !- tau) -> WN m -> Gam !- tau
norm-wn m (stop _)       = m
norm-wn m (step r m'-wn) = norm-wn _ m'-wn

-- normal-order normalisation
norm-sn : forall {Gam tau} -> (m : Gam !- tau) -> SN m -> Gam !- tau
norm-sn m (step g) with reduce m
norm-sn m (step g) | just (m' , r) = norm-sn m' (g r)
norm-sn m (step g) | nothing = m

{-** frame stacks **-}
infix 3 _!-s_-o_
data _!-s_-o_ (Gam : Cx Ty) : Ty -> Ty -> Set where

  [-] : forall {tau}

         -> ----------------------
             Gam !-s tau -o tau

  app :  forall {sg tau rho} ->
             Gam !-s tau -o rho ->  Gam !- sg
         ->  --------------------------------
             Gam !-s sg ->> tau -o rho

{-** plugging terms in frame stacks **-}
_[_] : forall {Gam tau rho} -> Gam !-s tau -o rho -> Gam !- tau -> Gam !- rho
[-]     [ m ] = m
app s m [ l ] = s [ app l m ]

-- it turns out that we don't need to plug frame stacks in frame
-- stacks

-- _[_]s :  forall {Gam sg tau rho} -> Gam !-s tau -o rho -> Gam !-s sg -o tau -> Gam !-s sg -o rho
-- s' [ [-] ]s      = s'
-- s' [ app s n ]s  = app (s' [ s ]s) n

record Plugged (Gam : Cx Ty) (rho tau : Ty) : Set where
  constructor Plug
  field
    s : Gam !-s tau -o rho 
    m : Gam !- tau

-- it turns out that we don't need to decompose terms

-- record Decompose (Gam : Cx Ty) (rho : Ty) : Set where
--   constructor Decomp
--   field
--     l : Gam !- rho
--     tau : Ty
--     s : Gam !-s tau -o rho 
--     m : Gam !- tau
--     p : s [ m ] ≡ l

-- decompose : forall {Gam tau rho} -> (s : Gam !-s tau -o rho) -> (m : Gam !- tau) -> Decompose Gam rho
-- decompose [-] (var x) = Decomp (var x) _ [-] (var x) refl
-- decompose (app s n) (var x) = Decomp (s [ app (var x) n ]) _ s (app (var x) n) refl
-- decompose s (lam n) = Decomp (s [ lam n ]) _ s (lam n) refl
-- decompose s (app m n) = decompose (app s n) m

{-** frame stack reduction **-}
infixr 2 _==>s_
data _==>s_ : {Gam : Cx Ty} {tau rho : Ty} (s : Gam !-s tau -o rho) -> (s' : Gam !-s tau -o rho) -> Set where

  app-stack : forall {Gam sg tau rho} {s s' : Gam !-s tau -o rho} {m : Gam !- sg} ->
           s ==>s s'
        -> ---------------------
           app s m ==>s app s' m

  app-term : forall {Gam sg tau rho} {s : Gam !-s tau -o rho} {m m' : Gam !- sg} -> 
           m ==> m'
        -> ---------------------
           app s m ==>s app s m'

{-** strongly normalising frame stacks **-}
mutual
  data SNs : {Gam : Cx Ty} {tau rho : Ty} (s : Gam !-s tau -o rho) -> Set where
    step : forall {Gam tau rho s} -> SNs'{Gam}{tau}{rho} s -> SNs s

  SNs' : {Gam : Cx Ty} {tau rho : Ty} (s : Gam !-s tau -o rho) -> Set
  SNs' s = forall {s'} -> s ==>s s' -> SNs s'

-- unsteps : forall {Gam tau rho} -> {s : Gam !-s tau -o rho} -> SNs s -> SNs' s
-- unsteps (step g) = g

sns-app : forall {Gam sg tau rho s n} -> SNs{Gam}{tau}{rho} s -> SN{Gam}{sg} n -> SNs{Gam}{sg ->> tau} (app s n)
sns-app s-sn n-sn = step (sns-app' s-sn n-sn) where
  sns-app' : forall {Gam sg tau rho s n} -> SNs{Gam}{tau}{rho} s -> SN{Gam}{sg} n -> SNs'{Gam}{sg ->> tau} (app s n)
  sns-app' (step sf) (step nf) (app-term r)  = step (sns-app' (step sf) (nf r))
  sns-app' (step sf) (step nf) (app-stack r) = step (sns-app' (sf r) (step nf))

{-** reduction relation on plugs **-}
infixr 2 _==>p_
data _==>p_ : {Gam : Cx Ty} {sg tau rho : Ty} ->
                 Plugged Gam rho tau ->
                 Plugged Gam rho sg -> Set where
 
  stack : forall {Gam tau rho} {s s' : Gam !-s tau -o rho} {m : Gam !- tau} ->

           s ==>s s'
        -> -----------------------
           Plug s m ==>p Plug s' m

  term : forall {Gam tau rho} {s : Gam !-s tau -o rho} {m m' : Gam !- tau} ->

           m ==> m'
        -> -----------------------
           Plug s m ==>p Plug s m'

  beta : forall {Gam sg tau rho} {s : Gam !-s tau -o rho} {m : Gam :: sg !- tau} {n : Gam !- sg}

        -> ------------------------------------------------------
           Plug (app s n) (lam m) ==>p Plug s (subst (sub1 n) m)


-- shift is admissible!

  -- shift :  forall {Gam xi sg tau rho}
  --             {s : Gam !-s tau -o rho} -> {m : Gam !- sg ->> tau} -> {n : Gam !- sg} ->
  --             {s' : Gam !-s xi -o rho} -> {m' : Gam !- xi} ->
  --
  --          Plug s (app m n) ==>p Plug s' m'
  --       -> ------------------------------------------------------
  --          Plug (app s n) m ==>p Plug s' m'


{-** strong normalisation for plugs **-}
mutual
  data SNp : {Gam : Cx Ty} {rho tau : Ty} (p : Plugged Gam rho tau) -> Set where
    step : forall {Gam rho tau p} -> SNp'{Gam}{rho}{tau} p -> SNp{Gam}{rho}{tau} p

  SNp' : {Gam : Cx Ty} {rho tau : Ty} (p : Plugged Gam rho tau) -> Set
  SNp' {Gam}{rho}p = forall {sg} -> {p' : Plugged Gam rho sg} -> p ==>p p' -> SNp p'

-- shift allows us to simulate peeling off the frame stack to reveal a raw term
-- and thus simulate any term reduction on a plug
shift :  forall {Gam} ->
           {tau1 sg tau rho : Ty} ->
           (s : Gam !-s tau -o rho) -> (m : Gam !- sg ->> tau) -> (n : Gam !- sg) ->
           (s1 : Gam !-s tau1 -o rho) -> (m1 : Gam !- tau1) ->
             Plug s (app m n) ==>p Plug s1 m1 ->
               Σ[ tau2 ∈ Ty ]
                 Σ[ s2 ∈ Gam !-s tau2 -o rho ]
                   Σ[ m2 ∈ Gam !- tau2 ]
                     (Plug (app s n) m ==>p Plug s2 m2) × (s1 [ m1 ] ≡ s2 [ m2 ])
shift {tau1 = tau1} s (lam m) n .s .(subst (sub1 n) m) (term beta) =
  tau1 , s , subst (sub1 n) m , beta , refl
shift [-] m n s1 .(app m n) (stack ())
shift (app s n') m n [-] .(app m n) (stack ())
shift {tau1 = tau1}{sg = sg} s m n s1 .(app m n) (stack r) =
  sg ->> tau1 , app s1 n , m , stack (app-stack r) , refl
shift {tau1 = tau1}{sg = sg} s m n .s (app m' .n) (term (app-fun r)) =
  sg ->> tau1 , app s n , m' , term r , refl
shift {tau1 = tau1}{sg = sg} s m n .s (app .m n') (term (app-arg r)) =
  sg ->> tau1 , app s n' , m , stack (app-term r) , refl
 
-- the plugging operation preserves term reduction
red-term : forall {Gam tau rho} -> (s : Gam !-s tau -o rho) -> (m m' : Gam !- tau) ->
             m ==> m' -> s [ m ] ==> s [ m' ]
red-term [-]       m m' r = r
red-term (app s n) m m' r = red-term s (app m n) (app m' n) (app-fun r)

-- the plugging operation preserves the transitive closure of term reduction
red-term* : forall {Gam tau rho} -> (s : Gam !-s tau -o rho) -> {m m' : Gam !- tau} ->
             m ==>* m' -> s [ m ] ==>* s [ m' ]
red-term* s {m} {.m} none = none
red-term* s {m} {n} (one r) = one (red-term s m n r)
red-term* s {m} {n} (many rs rs') = many (red-term* s rs) (red-term* s rs')

-- the plugging operation preserves frame stack reduction
red-stack : forall {Gam tau rho} -> (s s' : Gam !-s tau -o rho) -> (m : Gam !- tau) ->
            s ==>s s' -> s [ m ] ==> s' [ m ]
red-stack (app s n) (app s' .n) m (app-stack r) = red-stack s s' (app m n) r
red-stack (app s n) (app .s n') m (app-term r) = red-term s (app m n) (app m n') (app-arg r)

-- the plugging operation simulates reduction on plugs
red-plug : forall {Gam sg tau rho} ->
              (s : Gam !-s sg -o rho) -> (m : Gam !- sg) ->
                (s' : Gam !-s tau -o rho) -> (m' : Gam !- tau) ->
                   Plug s m ==>p Plug s' m' -> s [ m ] ==> s' [ m' ]
red-plug s m s' .m (stack r) = red-stack s s' m r
red-plug s m .s m' (term r) = red-term s m m' r
red-plug (app s n) (lam m) .s .(subst (sub1 n) m) beta =
  red-plug s (app (lam m) n) s (subst (sub1 n) m) (term beta)

-- plugs simulate reduction on the plugging of a term in a frame stack
plug-red : forall {Gam rho} ->
                (tau : Ty) ->
                (s : Gam !-s tau -o rho) -> (m : Gam !- tau) -> (l l' : Gam !- rho) ->
                  (p : s [ m ] ≡ l) ->
                    l ==> l' ->
                      Σ[ sg ∈ Ty ]
                        Σ[ s' ∈ Gam !-s sg -o rho ]
                          Σ[ m' ∈ Gam !- sg ]
                            (Plug s m ==>p Plug s' m') × (s' [ m' ] ≡ l')
plug-red tau [-] m .m l' refl r = tau , [-] , l' , term r , refl
plug-red (sg ->> tau) (app s n) m l l' p r with plug-red tau s (app m n) l l' p r
... | sg' , s' , m' , r' , p' with shift s m n s' m' r'
... | sg'' , s2 , m2 , r'' , p'' rewrite p'' = sg'' , s2 , m2 , r'' , p'

stack-var-sn : {Gam : Cx Ty} -> {tau rho : Ty} -> (x : tau <: Gam) -> (s : Gam !-s tau -o rho) -> SNs s -> SNp' (Plug s (var x))
stack-var-sn x s (step s-f) {p' = Plug s' .(var x)} (stack r) = step (stack-var-sn x s' (s-f r))
stack-var-sn x s (step s-f) {p' = Plug .s m} (term ())

-- decomposition preserves strong normalisation
sn-snp : forall {Gam tau rho} -> (s : Gam !-s tau -o rho) -> (m : Gam !- tau) -> SN (s [ m ]) -> SNp' (Plug s m)
sn-snp {tau = tau} s m (step f) {p' = Plug s' m'} r with red-plug s m s' m' r
... | r' = step (sn-snp s' m' (f r'))

-- recomposition preserves strong normalisation
snp-sn : forall {Gam tau rho} -> (s : Gam !-s tau -o rho) -> (m : Gam !- tau) -> SNp (Plug s m) -> SN' (s [ m ])
snp-sn {tau = tau} s m (step f) {l'} r with plug-red tau s m (s [ m ]) l' refl r
... | sg , s' , m' , r' , p' rewrite sym p' = step (snp-sn s' m' (f r'))

mutual
  {-** reducibility for frame stacks **-}
  RedT : (tau : Ty) -> {Gam : Cx Ty} -> {rho : Ty} -> (s : Gam !-s tau -o rho) -> Set
  RedT iota [-]               = ⊤
  RedT (sg ->> tau) [-]       = ⊤
  RedT (sg ->> tau) (app s m) = RedT tau s × Red sg m

  {-** reducibility for terms **-}
  Red : (tau : Ty) -> {Gam : Cx Ty} -> (m : Gam !- tau) -> Set
  Red tau {Gam} m = forall {Del rho} -> {pi : Ren Gam Del} -> {s : Del !-s tau -o rho} ->
                      RedT tau {Del}{rho} s -> SN (s [ rename pi m ])
  -- it is crucial to allow the term to be renamed in order to allow
  -- it to be placed in any frame stack of the correct type


-- reducibility implies strong normalisation
red-sn : (tau : Ty) -> {Gam : Cx Ty}-> (m : Gam !- tau) -> Red tau m -> SN m
red-sn iota         m red = coerce SN (rename-id m) (red {pi = id}{s = [-]} tt)
red-sn (sg ->> tau) m red = coerce SN (rename-id m) (red {pi = id}{s = [-]} tt)


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

-- any descendant of a strongly normalising term in strongly
-- normalising
sn* :
  forall {Gam tau} ->
    (m n : Gam !- tau) -> m ==>* n -> SN m -> SN n
sn* m .m none (step g) = step g
sn* m n (one r) (step g) = g r
sn* m n (many{m' = m'} rs rs') (step g) = sn* m' n rs' (sn* m m' rs (step g))

sub1-sn :
  forall {Gam sg tau rho} -> (s : Gam !-s tau -o rho) -> (m : Gam :: sg !- tau) -> (n n' : Gam !- sg) ->
    n ==> n' -> SNp (Plug s (subst (sub1 n) m)) -> SNp (Plug s (subst (sub1 n') m))
sub1-sn s m n n' r snp = step (sn-snp s (subst (sub1 n') m) sn) where
  sn : SN (s [ subst (sub1 n') m ])
  sn = sn* (s [ subst (sub1 n) m ]) (s [ subst (sub1 n') m ])
            (red-term* s (sub-arg-red Em m n n' r)) (step (snp-sn s (subst (sub1 n) m) snp))


{-** strong normalisagion is closed under beta expansion **-}

-- plugs
snp-closure : forall {Gam sg tau rho} -> (m : Gam :: sg !- tau) -> (n : Gam !- sg) -> (s : Gam !-s tau -o rho) ->
  SNp (Plug s (subst (sub1 n) m)) -> SN n -> SNp' (Plug s (app (lam m) n))
snp-closure m n s (step snm-f) (step n-f) {p' = Plug s' .(app (lam m) n)} (stack r) =
  step (snp-closure m n s' (snm-f (stack r)) (step n-f))
snp-closure m n s (step snm-f) (step n-f) {p' = Plug .s .(subst (sub1 n) m)} (term beta) =
  step snm-f
snp-closure m n s (step snm-f) (step n-f) {p' = Plug .s (app (lam m') .n)} (term (app-fun (lam r))) =
  step (snp-closure m' n s (snm-f (term (sub-red (sub1 n) m m' r))) (step n-f))
snp-closure m n s (step snm-f) (step n-f) {p' = Plug .s (app (lam .m) n')} (term (app-arg r)) =
  step (snp-closure m n' s (sub1-sn s m n n' r (step snm-f)) (n-f r))

-- pluggings
sn-closure : forall {Gam sg tau rho} -> (m : Gam :: sg !- tau) -> (n : Gam !- sg) -> (s : Gam !-s tau -o rho) ->
  SN{Gam}{rho} (s [ subst (sub1 n) m ]) -> SN n -> SN (s [ app (lam m) n ])
sn-closure m n s smn-nf n-nf =
  step (snp-sn s (app (lam m) n)
    (step (snp-closure m n s (step (sn-snp s (subst (sub1 n) m) smn-nf)) n-nf)))

-- reducibility is closed under reduction

-- terms
red-closed : {Gam : Cx Ty} -> {tau : Ty} -> (m : Gam !- tau) -> Red tau m -> {m' : Gam !- tau} -> m ==> m' -> Red tau m'
red-closed m red {m' = m'} r {pi = pi} {s = s} redT =
  unstep (red {s = s} redT) {s [ rename pi m' ] } (red-term s (rename pi m) (rename pi m') (sub-red pi m m' r))

-- frame stacks
redT-closed : {Gam : Cx Ty} -> {tau rho : Ty} -> (s : Gam !-s tau -o rho) ->
                RedT tau s -> {s' : Gam !-s tau -o rho} -> s ==>s s' -> RedT tau s'
redT-closed {tau = iota} [-] tt ()
redT-closed {tau = sg ->> tau} [-] tt ()
redT-closed {tau = sg ->> tau} (app s n) (redT , red) (app-stack r) = redT-closed s redT r , red
redT-closed {tau = sg ->> tau} (app s n) (redT , red) (app-term r) = redT , red-closed n red r

-- reducable frame stacks are strongly normalising
redT-sn : {tau : Ty} -> {Gam : Cx Ty} -> {rho : Ty} -> (s : Gam !-s tau -o rho)
                           -> RedT tau s -> SNs s
redT-sn {iota} [-] tt = step (\())
redT-sn {sg ->> tau} [-] tt = step (\())
redT-sn {sg ->> tau} (app s n) (redT , red) = step g where
  g : SNs' (app s n)
  g {app .s n'}(app-term r)  = sns-app (redT-sn {tau} s redT) (red-sn sg n' (red-closed n red r))
  g {app s' .n}(app-stack r) = sns-app (redT-sn {tau} s' (redT-closed s redT r)) (red-sn sg n red)

-- variables are reducible
var-red : (tau : Ty) -> {Gam : Cx Ty} -> (x : tau <: Gam) -> Red tau (var x)
var-red tau          x {s = [-]}     redT = step (\())
var-red (sg ->> tau) x {pi = pi} {s = app s m} redT =
  step (snp-sn (app s m) (var (pi x)) (step (stack-var-sn (pi x) (app s m) (redT-sn (app s m) redT))))

-- reducibility is closed under renaming
rename-red :
  forall {Gam Del tau} ->
    (pi : Ren Gam Del) ->
      (m : Gam !- tau) ->
        Red tau m -> Red tau (subst pi m)
rename-red pi m red {pi = pi'} {s = s} redT =
  coerce (\m -> SN (s [ m ])) (sym (comp_subst pi' pi m)) (red {pi = comp pi' pi} {s = s} redT)

{-** reducibility is closed under beta expansion **-}
red-closure : forall {Gam sg tau} -> (m : Gam :: sg !- tau) ->
  Red tau m ->
    (forall {Del} -> {pi : Ren Gam Del} -> {n : Del !- sg} ->
      Red sg n -> Red tau (subst (sub1 n) (rename (lift pi) m))) ->
        Red (sg ->> tau) (lam m)
red-closure {Gam}{sg}{tau} m redm h {pi = pi}{s = [-]} redT =
  sn-lam (red-sn tau (rename (lift pi) m) (rename-red (lift pi) m redm))
red-closure {Gam}{sg}{tau} m redm h {pi = pi}{s = app s n} (redT , red) =
  sn-closure (rename (lift pi) m) n s nm-sn (red-sn sg n red) where
    nm-sn : SN (s [ subst (sub1 n) (subst (lift pi) m) ])
    nm-sn = coerce (\m -> SN (s [ m ])) (rename-id _) (h {pi = pi} {n} red {pi = id} {s = s} redT)


-- rename-lem :
--   forall {Gam Del tau} ->
--     (pi : Ren Gam Del) ->
--       (m : Gam !- tau) ->
--         (m' : Del !- tau) ->
--           subst pi m ==> m' ->
--             Σ[ m'' ∈ Gam !- tau ] (m ==> m'') * (m' ≡ subst pi m'')
-- rename-lem pi (var x) m' ()
-- rename-lem pi (lam m) (lam m') (lam r) with rename-lem (lift pi) m m' r
-- ... | m'' , r' , p = lam m'' , lam r' , cong lam p
-- rename-lem pi (app (lam m) n) .(subst (sub1 (subst pi n)) (subst (lift pi) m)) beta =
--    subst (sub1 n) m , beta , begin
--                                  subst (sub1 (subst pi n)) (subst (lift pi) m)
--                                ≡⟨ comp_subst (sub1 (subst pi n)) (lift pi) m ⟩
--                                  subst (comp (sub1 (subst pi n)) (lift pi)) m
--                                ≡⟨ sub1-comp pi m n  ⟩
--                                  subst (comp pi (sub1 n)) m
--                                ≡⟨ sym (comp_subst pi (sub1 n) m) ⟩
--                                  subst pi (subst (sub1 n) m)
--                                ∎
-- rename-lem pi (app m n) (app m' .(subst pi n)) (app-fun r) with rename-lem pi m m' r
-- ... | m'' , r' , p = app m'' n , app-fun r' , cong (\l -> app l (subst pi n)) p
-- rename-lem pi (app m n) (app .(subst pi m) n') (app-arg r) with rename-lem pi n n' r
-- ... | n'' , r' , p = app m n'' , app-arg r' , cong (app (subst pi m)) p

-- sn-weak :
--   forall {Gam sg tau} ->
--     (m : Gam !- tau) ->
--       SN m -> SN' (subst{Gam}{Gam :: sg} suc m)
-- sn-weak m (step g) {m'} r with rename-lem suc m m' r
-- sn-weak m (step g) r | m'' , r' , refl = step (sn-weak m'' (g {m''} r'))

{-** reducibility of substitutions **-}
RedSub : (Gam Del : Cx Ty) -> (theta : Sub Gam Del) -> Set
RedSub Gam Del theta = (sg : Ty) -> (x : sg <: Gam) -> Red sg (theta x)

-- simple substitution lemmas

-- reducible substitutions are closed under weakening
wk-red-sub :
  forall {Gam Del sg} ->
    (theta : Sub Gam Del) ->
      RedSub Gam Del theta ->
        RedSub (Gam :: sg) (Del :: sg) (lift theta)
wk-red-sub theta f sg zero {pi = pi} redT = var-red sg (pi zero) {pi = id} redT
wk-red-sub theta f tau (suc x) {pi = pi} {s = s} redT =
  coerce (\m -> SN (s [ m ])) (str-suc pi (theta x)) (f tau x {pi = str pi} {s = s} redT)

-- reducible substitutions are closed under renaming
rename-red-sub : 
  forall {Gam Del Phi}
    (theta : Sub Gam Del) ->
      (pi : Ren Del Phi) ->
        RedSub Gam Del theta ->
          RedSub Gam Phi (comp pi theta)
rename-red-sub theta pi f tau x {Del = Del'}{pi = pi'}{s = s} redT =
  coerce (\m -> SN (s [ m ])) (sym (comp_subst pi' pi (theta x))) (f tau x {pi = comp pi' pi} {s = s} redT)

-- reducible substitutions are extensible
extend-red-sub' :
  forall {Gam Del sg}
    (theta : Sub Gam Del) ->
      RedSub Gam Del theta ->
        (n : Del !- sg) ->
          Red sg n ->
            RedSub (Gam :: sg) Del (comp (sub1 n) (lift theta))
extend-red-sub' theta f n red sg zero = red
extend-red-sub' theta f n red tau (suc x) {Del = Del'}{pi = pi}{s = s} redT =
  coerce (\m -> SN (s [ subst pi m ])) (sym p) (f tau x {pi = pi}{s = s} redT) where
    p : subst (sub1 n) (subst suc (theta x)) ≡ theta x
    p = begin 
            subst (sub1 n) (subst suc (theta x))
          ≡⟨ comp_subst (sub1 n) suc (theta x) ⟩
            subst (comp (sub1 n) suc) (theta x)
          ≡⟨ cong (\theta' -> subst (\{tau} -> theta'{tau}) (theta x)) (sub1-suc n) ⟩
            subst var (theta x)
          ≡⟨ sub-var (theta x) ⟩
            theta x
          ∎

-- reducible substitutions can be simulateously renamed and extended
extend-red-sub :
  forall {Gam Del Phi sg} {theta : Sub Gam Del} {pi : Ren Del Phi} ->
    RedSub Gam Del theta ->
      (n : Phi !- sg) ->
        Red sg n ->
          RedSub (Gam :: sg) Phi (comp (sub1 n) (comp (lift pi) (lift theta)))
extend-red-sub {Gam}{Del}{Phi}{sg}{theta}{pi = pi} f n red = h where
  g : RedSub (Gam :: sg) Phi (comp (sub1 n) (lift (comp pi theta)))
  g = extend-red-sub' (comp pi theta) (rename-red-sub theta pi f) n red

  h : RedSub (Gam :: sg) Phi (comp (sub1 n) (comp (lift pi) (lift theta)))
  h = coerce (\theta' -> RedSub (Gam :: sg) Phi (comp (sub1 n) (\{tau} -> theta'{tau}))) (sym (comp_lift pi theta)) g

{-** every term is reducible **-}
fundamental-theorem :
  forall {Gam Del tau} ->
    (m : Gam !- tau) ->
      (theta : Sub Gam Del) ->
        RedSub Gam Del theta -> Red tau (subst theta m)
fundamental-theorem {tau = tau} (var x) theta f = f tau x
fundamental-theorem {Gam}{Del}{sg ->> tau}(lam m) theta f {pi = pi}{s = s} redT =
  red-closure{Del}{sg}{tau} (subst (lift{Gam}{Del}{sg} theta) m) red-m red-mn {s = s} redT where
    red-mn' : forall {Phi} -> {pi : Ren Del Phi} -> {n : Phi !- sg} ->
                Red sg n -> Red tau (subst (comp (sub1 n) (comp (lift pi) (lift theta))) m)
    red-mn' {Phi}{pi}{n} redn =
      fundamental-theorem m (comp (sub1 n) (comp (lift pi) (lift theta))) (extend-red-sub f n redn)

    red-mn : forall {Phi} -> {pi : Ren Del Phi} -> {n : Phi !- sg} ->
               Red sg n -> Red tau (subst (sub1 n) (subst (lift pi) (subst (lift theta) m)))
    red-mn {Phi}{pi}{n} redn = coerce (Red tau) p (red-mn' redn) where
      p : subst (comp (sub1 n) (comp (lift pi) (lift theta))) m ≡
            subst (sub1 n) (subst (lift pi) (subst (lift theta) m))
      p = begin
              subst (comp (sub1 n) (comp (lift pi) (lift theta))) m
            ≡⟨ sym (comp_subst (sub1 n) (comp (lift pi) (lift theta)) m) ⟩
              subst (sub1 n) (subst (comp (lift pi) (lift theta)) m)
            ≡⟨ cong (subst (sub1 n)) (sym (comp_subst (lift pi) (lift theta) m)) ⟩
              subst (sub1 n) (subst (lift pi) (subst (lift theta) m))
            ∎

    red-m : Red tau (subst (lift theta) m)
    red-m = fundamental-theorem m (lift theta) (wk-red-sub theta f) 
fundamental-theorem {Gam}{tau = tau} (app{sg} m n) theta f {Del = Del}{pi = pi} {s = s} redT =
  fundamental-theorem
    {tau = sg ->> tau} m theta f {pi = pi} {s = app s (rename pi (subst theta n))} (redT , red') where

    f' : RedSub Gam Del (comp pi theta)
    f' tau x {pi = pi'} {s = s} redT =
      coerce (\m -> SN (s [ m ]))
        (sym (comp_subst pi' pi (theta x)))
        (f tau x {pi = comp pi' pi} {s = s} redT)

    red : Red sg (subst (comp pi theta) n)
    red = fundamental-theorem {tau = sg} n (comp pi theta) f'

    red' : Red sg (rename pi (subst theta n))
    red' {pi = pi'} {s = s} redT =
      coerce (\m -> SN (s [ rename pi' m ]))
        (sym (comp_subst pi theta n))
        (red {pi = pi'} {s = s} redT)

{-** every term is strongly normalising **-}
sn-theorem : 
  forall {Gam tau} -> (m : Gam !- tau) -> SN m
sn-theorem {tau = tau} m =
  red-sn tau m (coerce (Red tau) (sub-var m) (fundamental-theorem m var (\sg -> var-red sg)))
