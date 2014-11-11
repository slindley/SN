module TypedLambda where

data Ty : Set where
  iota   :              Ty
  _->>_  : Ty -> Ty ->  Ty
infixr 5 _->>_

data Cx (X : Set) : Set where
  Em    : Cx X
  _::_  : Cx X -> X -> Cx X
infixl 4 _::_

data _<:_ (tau : Ty) : Cx Ty -> Set where
  zero  : forall {Gam}                    -> tau <: Gam :: tau
  suc   : forall {Gam sg}  -> tau <: Gam  -> tau <: Gam :: sg
infix 3 _<:_

data _!-_ (Gam : Cx Ty) : Ty -> Set where

  var :  forall {tau}
         ->  tau <: Gam
         --  -------------
         ->  Gam !- tau

  lam :  forall {sg tau}
         ->  Gam :: sg !- tau
         --  ------------------
         ->  Gam !- sg ->> tau

  app :  forall {sg tau}
         ->  Gam !- sg ->> tau  ->  Gam !- sg
         --  --------------------------------
         ->  Gam !- tau

infix 3 _!-_
