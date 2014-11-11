-- Parallel substitution for simply-typed lambda terms.
--
-- This is directly adapted from Andreas Abel's code for parallel
-- substitution for untyped de Bruijn terms:
--
-- "Instead of distinguishing renamings and substitutions as in
--
--   Chung-Kil Hur et al., 
--   Strongly Typed Term Representations in Coq
--
-- which leads to 4 different composition operations,
-- we define a generic substitution/renaming operation.
-- This is inspired by 
-- 
--   Conor McBride
--   Type Preserving Renaming and Substitution
--
-- but, being not restricted to structural recursion, we can utilize
-- the lexicographically terminating definition of
--
--   Thorsten Altenkirch and Bernhard Reus
--   Monadic Presentations of Lambda Terms Using Generalized Inductive Types
--
-- This way, we have a single composition operation and lemma, which is mutual
-- with a lemma for composition of liftings."
--
module ParallelSubstitutionTyped where

open import Data.Nat
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)
open ≡-Reasoning

open import TypedLambda renaming (suc to succ)

-- since we model substitutions as functions over natural numbers
-- (instead of lists), functional extensionality is very convenient to have!

postulate
  funExt : forall {i j}{X : Set i}{Y : X -> Set j}
              {f g : (x : X) -> Y x} ->
              ((x : X) -> f x ≡ g x) ->
              f ≡ g
  implFunExt :
      forall {i j}{X : Set i}{Y : X -> Set j} ->
        {f g : {x : X} -> Y x} ->
        ((x : X) -> f {x} ≡ g {x}) ->
        (\{x} -> f {x}) ≡ g

-- A structurally ordered two-element set
data VarTrm : ℕ → Set where
  Var : VarTrm 0  -- we are dealing with variables (natural numbers)
  Trm : VarTrm 1  -- we are dealing with terms

max01 : ℕ → ℕ → ℕ
max01 0 m = m
max01 n m = n

compVT : ∀ {n m} (vt : VarTrm n) (vt' : VarTrm m) → VarTrm (max01 n m)
compVT Var vt' = vt'
compVT Trm vt  = Trm

-- A set of variables or terms
VT : (Γ : Cx Ty) (τ : Ty) -> ∀ {n} → (vt : VarTrm n) → Set
VT Γ τ Var = τ <: Γ
VT Γ τ Trm = Γ !- τ

-- A mapping which is either a renaming (Var) or substitution (Trm)
RenSub : (Γ Δ : Cx Ty) → ∀ {n} → (vt : VarTrm n) → Set
RenSub Γ Δ vt = {τ : Ty} -> τ <: Γ → VT Δ τ vt

Ren : (Γ Δ : Cx Ty) → Set
Ren Γ Δ   = {τ : Ty} → τ <: Γ → τ <: Δ  -- Renamings 
Sub : (Γ Δ : Cx Ty) → Set
Sub Γ Δ = {τ : Ty} → τ <: Γ → Δ !- τ -- Substitutions


mutual

  lift : ∀ {Γ Δ σ m} {vt : VarTrm m} (θ : RenSub Γ Δ vt) → RenSub (Γ :: σ) (Δ :: σ) vt
  -- lifting a renaming
  lift {vt = Var} θ zero     = zero
  lift {vt = Var} θ (succ x) = succ (θ x) 
  -- lifting a substituion  
  lift {vt = Trm} θ zero     = var zero
  lift {vt = Trm} θ (succ x) = subst succ (θ x) -- shift
  
  subst : ∀ {Γ Δ τ m} {vt : VarTrm m} (θ : RenSub Γ Δ vt) → Γ !- τ → Δ !- τ
  subst {vt = vt} θ (lam{σ}{τ} t)   = lam (subst (lift θ) t)
  subst {vt = vt} θ (app t u) = app (subst θ t) (subst θ u)
  -- PUT THESE LAST BECAUSE OF AGDA SPLIT HEURISTICS:
  subst {vt = Var} θ (var x)   = var (θ x) -- lookup in renaming
  subst {vt = Trm} θ (var x)   = θ x       -- lookup in substitution

-- substitution composition

comp : ∀ {Γ Δ Φ}{n}{vt2 : VarTrm n}(θ : RenSub Δ Φ vt2)
         {m}{vt1 : VarTrm m}(π : RenSub Γ Δ vt1) → RenSub Γ Φ (compVT vt1 vt2)
comp θ {vt1 = Var} π x = θ (π x)
comp θ {vt1 = Trm} π x = subst θ (π x) 



-- Composition lemma

mutual

  comp_lift : 
    ∀ {Γ Δ Φ σ}
      {n}{vt2 : VarTrm n}(θ : RenSub Δ Φ vt2)
      {m}{vt1 : VarTrm m}(π : RenSub Γ Δ vt1) → 
        (λ {τ} → comp{Γ :: σ}{Δ :: σ}{Φ :: σ} (lift θ) (lift π) {τ}) ≡ (λ {τ} → lift (comp θ π))

  comp_lift θ π = implFunExt (λ τ → funExt (λ x -> comp_lift' θ π x))

  comp_lift' : 
    ∀ {Γ Δ Φ σ}
      {n}{vt2 : VarTrm n}(θ : RenSub Δ Φ vt2)
      {m}{vt1 : VarTrm m}(π : RenSub Γ Δ vt1){τ : Ty}(x : τ <: Γ :: σ) → 
        comp (lift θ) (lift π) x ≡ lift (comp θ π) x
  comp_lift' {vt2 = Var} θ {vt1 = Var} π zero = refl
  comp_lift' {vt2 = Trm} θ {vt1 = Var} π zero = refl
  comp_lift' {vt2 = Var} θ {vt1 = Trm} π zero = refl
  comp_lift' {vt2 = Trm} θ {vt1 = Trm} π zero = refl
  comp_lift' {vt2 = Var} θ {vt1 = Var} π (succ x') = refl
  comp_lift' {vt2 = Trm} θ {vt1 = Var} π (succ x') = refl
  comp_lift' {vt2 = Var} θ {vt1 = Trm} π (succ x') = begin
      subst (lift θ) (subst succ (π x'))
    ≡⟨ comp_subst (lift θ) succ (π x') ⟩
      subst (comp (lift θ) succ) (π x')
    ≡⟨ refl ⟩
      subst (λ x → comp (lift θ) succ x) (π x')
    ≡⟨ refl ⟩
      subst (λ x → succ (θ x)) (π x')  
    ≡⟨ refl ⟩
      subst (λ x → comp succ θ x) (π x')
    ≡⟨ refl ⟩
      subst (comp succ θ) (π x')
    ≡⟨ sym (comp_subst succ θ (π x')) ⟩
      subst succ (subst θ (π x'))
    ∎
  comp_lift' {vt2 = Trm} θ {vt1 = Trm} π (succ x') = begin
      subst (lift θ) (subst succ (π x'))
    ≡⟨ comp_subst (lift θ) succ (π x') ⟩
      subst (comp (lift θ) succ) (π x')
    ≡⟨ refl ⟩
      subst (λ x → comp (lift θ) succ x) (π x')
    ≡⟨ refl ⟩
      subst (λ x → subst succ (θ x)) (π x')  -- distinct line!
    ≡⟨ refl ⟩
      subst (λ x → comp succ θ x) (π x')
    ≡⟨ refl ⟩
      subst (comp succ θ) (π x')
    ≡⟨ sym (comp_subst succ θ (π x')) ⟩
      subst succ (subst θ (π x'))
    ∎

  comp_subst :
    ∀ {Γ Δ Φ τ}
      {n}{vt2 : VarTrm n}(θ : RenSub Δ Φ vt2)
      {m}{vt1 : VarTrm m}(π : RenSub Γ Δ vt1)(t : Γ !- τ) → 
         subst θ (subst π t) ≡ subst (comp θ π) t
  comp_subst {vt2 = Var} θ {vt1 = Var} π (var x) = refl
  comp_subst {vt2 = Var} θ {vt1 = Trm} π (var x) = refl
  comp_subst {vt2 = Trm} θ {vt1 = Var} π (var x) = refl
  comp_subst {vt2 = Trm} θ {vt1 = Trm} π (var x) = refl

  comp_subst {vt2 = vt2} θ {vt1 = vt1} π (lam t) = begin

      subst θ (subst π (lam t)) 

    ≡⟨ refl ⟩ 

      subst θ (lam (subst (lift π) t))

    ≡⟨ refl ⟩ 

      lam (subst (lift θ) (subst (lift π) t))

    ≡⟨ cong lam (comp_subst (lift θ) (lift π) t) ⟩ 

      lam (subst (comp (lift θ) (lift π)) t)

    ≡⟨ cong (λ π' → lam (subst (λ{τ} → π'{τ}) t)) (comp_lift θ π) ⟩ 

      lam (subst (lift (comp θ π)) t)

    ≡⟨ refl ⟩ 

      subst (comp θ π) (lam t)
    ∎

  comp_subst {vt2 = vt2} θ {vt1 = vt1} π (app t u) = begin

      subst θ (subst π (app t u)) 

    ≡⟨ refl ⟩

      app (subst θ (subst π t)) (subst θ (subst π u)) 

    ≡⟨ cong (λ t' → app t' (subst θ (subst π u))) 
            (comp_subst θ π t) ⟩

      app (subst (comp θ π) t) (subst θ (subst π u)) 

    ≡⟨ cong (λ u' → app (subst (comp θ π) t) u') 
            (comp_subst θ π u) ⟩

      app (subst (comp θ π) t) (subst (comp θ π) u)

    ≡⟨ refl ⟩

      subst (comp θ π) (app t u)
    ∎



