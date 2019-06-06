module Category where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ) renaming (zero to z; suc to s)
open import Data.Nat.Properties using (+-comm)
import Level as L
open L using (Level; _⊔_; zero; suc)
open import Relation.Binary using (Rel; IsEquivalence)
open import Data.Unit using (⊤)


record Category {objL morL eqL : Level} : Set (L.suc (objL ⊔ morL ⊔ eqL))  where
  field
    Obj : Set objL
    Hom⟨_,_⟩  : (src : Obj) -> (tgt : Obj) -> Set morL
    id  : {a : Obj} -> Hom⟨ a , a ⟩
    _~_ : {a b : Obj} -> Rel (Hom⟨ a , b ⟩) eqL 
    ~-equiv : {a b : Obj} -> IsEquivalence (_~_ {a} {b})

    _∘_ : {a b c : Obj} -> Hom⟨ b , c ⟩ -> Hom⟨ a , b ⟩ -> Hom⟨ a , c ⟩

    assoc-law
      : {a b c d : Obj}
      -> (f : Hom⟨ a , b ⟩)
      -> (g : Hom⟨ b , c ⟩)
      -> (h : Hom⟨ c , d ⟩)
      -> (h ∘ (g ∘ f)) ~ ((h ∘ g) ∘ f)  
    left-id-law 
     : {a b : Obj}
     -> (f : Hom⟨ a , b ⟩)
     -> (id ∘ f) ~ f
    right-id-law 
     : {a b : Obj}
     -> (f : Hom⟨ a , b ⟩)
     -> (f ∘ id) ~ f


--hom :  {A : Set l} -> (A -> A -> Set
--hom x y = 





--example : Category {zero} {zero} {zero}
--example = record {Obj = ℕ; Hom = hom; }

