module Stuff where

open import Data.Empty
open import Relation.Binary.PropositionalEquality

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

_o_ : forall {i j k}
        {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k} ->
        (f : {a : A}(b : B a) -> C a b) ->
        (g : (a : A) -> B a) ->
        (a : A) -> C a (g a)
f o g = \ a -> f (g a)

id : forall {k}{X : Set k} -> X -> X
id x = x
