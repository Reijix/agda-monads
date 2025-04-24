module Monads where

open import Level
open import Categories.Category
open import Categories.Monad hiding (id)
open import Categories.Object.Terminal
open import Categories.Object.Exponential
open import Categories.Functor renaming (id to idF)
open import Categories.Category.Cocartesian.Bundle
open import Categories.Category.CartesianClosed
open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts
open import Categories.Category.CartesianClosed.Bundle
open import Categories.NaturalTransformation renaming (id to idN)
open import Function using (_$_)

module _ (o ℓ e : Level) where


    --*
    -- Exception monad TX = X + E
    --*


    ExceptionMonad : (C : CocartesianCategory o ℓ e) → CocartesianCategory.Obj C → Monad (CocartesianCategory.U C)
    ExceptionMonad CC E = record
        { F = F
        ; η = η'
        ; μ = μ'
        ; assoc = assoc'
        ; sym-assoc = λ {X} → sym assoc'
        ; identityˡ = begin
            [ id , i₂ ] ∘ (i₁ +₁ id) ≈⟨ []∘+₁ ⟩ 
            [ id ∘ i₁  , i₂ ∘ id ] ≈⟨ []-cong₂ identityˡ identityʳ ⟩
            [ i₁ , i₂ ] ≈⟨ +-η ⟩
            id ∎
        ; identityʳ = inject₁
        }
        where
            open CocartesianCategory CC renaming (U to C)
            open HomReasoning
            open Equiv
            F : Endofunctor C
            F = record
                { F₀ = λ X → X + E
                ; F₁ = λ f → f +₁ id
                ; identity = λ {A} → begin 
                    id +₁ id ≈⟨ sym identityˡ ⟩
                    (id ∘ (id +₁ id)) ≈⟨ ∘-resp-≈ˡ (sym +-η) ⟩
                    ([ i₁ , i₂ ] ∘ (id +₁ id)) ≈⟨ []∘+₁ ⟩
                    [ i₁ ∘ id , i₂ ∘ id ] ≈⟨ []-cong₂ identityʳ identityʳ ⟩
                    [ i₁ , i₂ ] ≈⟨ +-η ⟩
                    id ∎
                ; homomorphism = λ {X} {Y} {Z} {f} {g} → begin 
                    g ∘ f +₁ id ≈⟨ sym (+₁-cong₂ refl identity²) ⟩ 
                    (g ∘ f +₁ id ∘ id) ≈⟨ sym +₁∘+₁ ⟩ 
                    ((g +₁ id) ∘ (f +₁ id)) ∎
                ; F-resp-≈ = λ {A B f g} fg → +₁-cong₂ fg refl
                }
            open Functor F
            η' : NaturalTransformation idF F
            η' = ntHelper record
                { η = λ X → i₁
                ; commute = λ {X Y} f → sym +₁∘i₁
                }
            open NaturalTransformation η'
            μ' : NaturalTransformation (F ∘F F) F
            μ' = ntHelper record
                { η = λ X → [ id , i₂ ]
                ; commute = λ {X Y} f → begin 
                    ([ id , i₂ ] ∘ ((f +₁ id) +₁ id)) ≈⟨ []∘+₁ ⟩ 
                    [ id ∘ (f +₁ id) , i₂ ∘ id ] ≈⟨ []-cong₂ identityˡ identityʳ ⟩
                    [ f +₁ id , i₂ ] ≈⟨ []-congˡ (sym identityʳ) ⟩
                    [ f +₁ id , i₂ ∘ id ] ≈⟨ sym ([]-cong₂ identityʳ +₁∘i₂) ⟩
                    [ (f +₁ id) ∘ id , (f +₁ id) ∘ i₂ ] ≈⟨ sym ∘[] ⟩
                    ((f +₁ id) ∘ [ id , i₂ ]) ∎
                }
            open NaturalTransformation μ' renaming (η to μ)
            assoc' : ∀ {X : Obj} → μ X ∘ F₁ (μ X) ≈ μ X ∘ μ (F₀ X)
            assoc' {X} = begin 
                [ id , i₂ ] ∘ ([ id , i₂ ] +₁ id) ≈⟨ []∘+₁ ⟩ 
                [ id ∘ [ id , i₂ ] , i₂ ∘ id ] ≈⟨ []-cong₂ identityˡ identityʳ ⟩
                [ [ id , i₂ ] , i₂ ] ≈⟨ sym ([]-cong₂ identityʳ inject₂) ⟩
                [ [ id , i₂ ] ∘ id , [ id , i₂ ] ∘ i₂ ] ≈⟨ sym (∘[]) ⟩
                [ id , i₂ ] ∘ [ id , i₂ ] ∎

    -- Maybe monad as special case of exception monad
    MaybeMonad : (C : CocartesianCategory o ℓ e) → Terminal (CocartesianCategory.U C) → Monad (CocartesianCategory.U C)
    MaybeMonad C T = ExceptionMonad C (Terminal.⊤ T)


    --*
    -- Reader monad TX = X^S
    --*


    ReaderMonad : (CCC : CartesianClosedCategory o ℓ e) → CartesianClosedCategory.Obj CCC → Monad (CartesianClosedCategory.U CCC)
    ReaderMonad CCC S = record
        { F = F
        ; η = η'
        ; μ = μ'
        ; assoc = assoc'
        ; sym-assoc = λ {X} → sym assoc'
        ; identityˡ = λ {X} → begin
            (λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ∘ (λg ((λg π₁) ∘ eval′)) ≈⟨ exp.subst product product ⟩ 
            λg ((eval′ ∘ ⟨ eval′ , π₂ ⟩) ∘ ((λg ((λg π₁) ∘ eval′)) ⁂ id)) ≈⟨ λ-cong assoc ⟩ 
            λg (eval′ ∘ (⟨ eval′ , π₂ ⟩ ∘ ((λg ((λg π₁) ∘ eval′)) ⁂ id))) ≈⟨ λ-cong (∘-resp-≈ʳ ⟨⟩∘) ⟩ 
            λg (eval′ ∘ (⟨ eval′ ∘ ((λg ((λg π₁) ∘ eval′)) ⁂ id) , π₂ ∘ ((λg ((λg π₁) ∘ eval′)) ⁂ id) ⟩)) ≈⟨ λ-cong (∘-resp-≈ʳ (⟨⟩-cong₂ β′ π₂∘⁂)) ⟩ 
            λg (eval′ ∘ ⟨ (λg π₁) ∘ eval′ , id ∘ π₂ ⟩) ≈⟨ λ-cong (∘-resp-≈ʳ (sym ⁂∘⟨⟩)) ⟩ 
            λg (eval′ ∘ (((λg π₁) ⁂ id) ) ∘ ⟨ eval′ , π₂ ⟩) ≈⟨ λ-cong sym-assoc ⟩ 
            λg ((eval′ ∘ (((λg π₁) ⁂ id) )) ∘ ⟨ eval′ , π₂ ⟩) ≈⟨ λ-cong (∘-resp-≈ˡ β′) ⟩ 
            λg (π₁ ∘ ⟨ eval′ , π₂ ⟩) ≈⟨ λ-cong project₁ ⟩ 
            λg eval′ ≈⟨ η-id′ ⟩ 
            id ∎
        ; identityʳ = λ {X} → begin
            (λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ∘ λg π₁ ≈⟨ exp.subst product product ⟩ 
            λg ((eval′ ∘ ⟨ eval′ , π₂ ⟩) ∘ ((λg π₁) ⁂ id)) ≈⟨ λ-cong assoc ⟩
            λg (eval′ ∘ (⟨ eval′ , π₂ ⟩ ∘ ((λg π₁) ⁂ id))) ≈⟨ λ-cong (∘-resp-≈ʳ ⟨⟩∘) ⟩ 
            λg (eval′ ∘ ⟨ eval′ ∘ ((λg π₁) ⁂ id) , π₂ ∘ ((λg π₁) ⁂ id) ⟩) ≈⟨ λ-cong (∘-resp-≈ʳ (⟨⟩-cong₂ β′ π₂∘⁂)) ⟩ 
            λg (eval′ ∘ ⟨ π₁ , id ∘ π₂ ⟩) ≈⟨ λ-cong (∘-resp-≈ʳ (⟨⟩-congˡ identityˡ)) ⟩ 
            λg (eval′ ∘ ⟨ π₁ , π₂ ⟩) ≈⟨ λ-cong (∘-resp-≈ʳ p-η) ⟩ 
            λg (eval′ ∘ id) ≈⟨ λ-cong identityʳ ⟩ 
            λg eval′ ≈⟨ η-id′ ⟩ 
            id ∎
        }
        where
            open CartesianClosedCategory CCC renaming (U to C)
            open CartesianClosed cartesianClosed
            open Cartesian cartesian
            open BinaryProducts products renaming (η to p-η)
            open HomReasoning
            open Equiv
            F = record
                { F₀ = λ X → X ^ S
                ; F₁ = λ {A B} f → λg (f ∘ eval′)
                ; identity = λ {A} → begin 
                    λg (id ∘ eval′) ≈⟨ λ-cong identityˡ ⟩ 
                    λg eval′ ≈⟨ η-id′ ⟩ 
                    id ∎
                ; homomorphism = λ {X Y Z f g } → begin 
                    λg ((g ∘ f) ∘ eval′) ≈⟨ λ-cong assoc ⟩ 
                    λg (g ∘ (f ∘ eval′)) ≈⟨ sym (λ-cong (∘-resp-≈ʳ β′)) ⟩
                    λg (g ∘ (eval′ ∘ ((λg (f ∘ eval′)) ⁂ id))) ≈⟨ sym (λ-cong assoc) ⟩
                    λg ((g ∘ eval′) ∘ ((λg (f ∘ eval′)) ⁂ id)) ≈⟨ sym (exp.subst product product) ⟩
                    (λg (g ∘ eval′)) ∘ (λg (f ∘ eval′)) ∎
                ; F-resp-≈ = λ {A B f g} fg → λ-cong (∘-resp-≈ˡ fg)
                }
            open Functor F
            η' = ntHelper record
                { η = λ X → λg π₁
                ; commute = λ {X Y} f → sym $ begin 
                    (λg (f ∘ eval′)) ∘ λg π₁ ≈⟨ exp.subst product product ⟩ 
                    λg ((f ∘ eval′) ∘ (λg π₁ ⁂ id)) ≈⟨ λ-cong assoc ⟩ 
                    λg (f ∘ (eval′ ∘ (λg π₁ ⁂ id))) ≈⟨ λ-cong (∘-resp-≈ʳ β′) ⟩ 
                    λg (f ∘ π₁) ≈⟨ sym (λ-cong π₁∘⁂) ⟩ 
                    λg (π₁ ∘ (f ⁂ id)) ≈⟨ sym (exp.subst product product) ⟩ 
                    λg π₁ ∘ f ∎
                }
            open NaturalTransformation η'
            μ' = ntHelper record
                { η = λ X → λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)
                ; commute = λ {X Y} f → begin 
                    (λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ∘ (λg ((λg (f ∘ eval′)) ∘ eval′)) ≈⟨ ∘-resp-≈ʳ (λ-cong (exp.subst product product)) ⟩ 
                    ((λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ∘ (λg (λg ((f ∘ eval′) ∘ (eval′ ⁂ id))))) ≈⟨ exp.subst product product ⟩ 
                    λg ((eval′ ∘ ⟨ eval′ , π₂ ⟩) ∘ ((λg (λg ((f ∘ eval′) ∘ (eval′ ⁂ id)))) ⁂ id )) ≈⟨ λ-cong assoc ⟩ 
                    λg (eval′ ∘ (⟨ eval′ , π₂ ⟩ ∘ ((λg (λg ((f ∘ eval′) ∘ (eval′ ⁂ id)))) ⁂ id ))) ≈⟨ λ-cong (∘-resp-≈ʳ ⟨⟩∘) ⟩ 
                    λg (eval′ ∘ (⟨ eval′ ∘ ((λg (λg ((f ∘ eval′) ∘ (eval′ ⁂ id)))) ⁂ id ) , π₂ ∘ ((λg (λg ((f ∘ eval′) ∘ (eval′ ⁂ id)))) ⁂ id ) ⟩)) ≈⟨ λ-cong (∘-resp-≈ʳ (⟨⟩-cong₂ β′ π₂∘⁂)) ⟩ 
                    λg (eval′ ∘ (⟨ λg ((f ∘ eval′) ∘ (eval′ ⁂ id)) , id ∘ π₂ ⟩)) ≈⟨ λ-cong (∘-resp-≈ʳ (⟨⟩-congˡ identityˡ)) ⟩ 
                    λg (eval′ ∘ ⟨ λg ((f ∘ eval′) ∘ (eval′ ⁂ id)) , π₂ ⟩) ≈⟨ λ-cong (∘-resp-≈ʳ (⟨⟩-congʳ (sym (exp.subst product product)))) ⟩ 
                    λg (eval′ ∘ ⟨ λg (f ∘ eval′) ∘ eval′ , π₂ ⟩) ≈⟨ λ-unique′ ((
                        begin 
                            eval′ ∘ ((λg (eval′ ∘ ⟨ λg (f ∘ eval′) ∘ eval′ , π₂ ⟩)) ⁂ id) ≈⟨ β′ ⟩
                            eval′ ∘ ⟨ λg (f ∘ eval′) ∘ eval′ , π₂ ⟩ ≈⟨ ∘-resp-≈ʳ (⟨⟩-congˡ (sym identityˡ)) ⟩
                            (eval′ ∘ ⟨ λg (f ∘ eval′) ∘ eval′ , id ∘ π₂ ⟩) ≈⟨ ∘-resp-≈ʳ (sym ⁂∘⟨⟩) ⟩
                            eval′ ∘ ( (λg (f ∘ eval′)) ⁂ id ) ∘ ⟨ eval′ , π₂ ⟩ ≈⟨ sym-assoc ⟩
                            (eval′ ∘ ( (λg (f ∘ eval′)) ⁂ id )) ∘ ⟨ eval′ , π₂ ⟩ ≈⟨ ∘-resp-≈ˡ β′ ⟩
                            (((f ∘ eval′)) ∘ ⟨ eval′ , π₂ ⟩) ≈⟨ assoc ⟩
                            f ∘ (eval′ ∘ ⟨ eval′ , π₂ ⟩) ∎
                    )) ⟩ 
                    λg (f ∘ (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ≈⟨ sym (λ-cong (∘-resp-≈ʳ β′)) ⟩ 
                    λg (f ∘ (eval′ ∘ ((λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ⁂ id))) ≈⟨ (λ-cong sym-assoc) ⟩ 
                    λg ((f ∘ eval′) ∘ ((λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ⁂ id)) ≈⟨ sym (exp.subst product product) ⟩ 
                    (λg (f ∘ eval′)) ∘ λg (eval′ ∘ ⟨ eval′ , π₂ ⟩) ∎ 
                }
            open NaturalTransformation μ' renaming (η to μ)
            assoc' : ∀ {X : Obj} → μ X ∘ F₁ (μ X) ≈ μ X ∘ μ (F₀ X)
            assoc' {X} = begin 
                (λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ∘ (λg ((λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ∘ eval′)) ≈⟨ exp.subst product product ⟩ 
                λg ((eval′ ∘ ⟨ eval′ , π₂ ⟩) ∘ ((λg ((λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ∘ eval′)) ⁂ id)) ≈⟨ λ-cong assoc ⟩
                λg (eval′ ∘ (⟨ eval′ , π₂ ⟩ ∘ ((λg ((λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ∘ eval′)) ⁂ id))) ≈⟨ λ-cong (∘-resp-≈ʳ ⟨⟩∘) ⟩
                λg (eval′ ∘ (⟨ eval′ ∘ ((λg ((λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ∘ eval′)) ⁂ id) , π₂ ∘ ((λg ((λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ∘ eval′)) ⁂ id) ⟩)) ≈⟨ λ-cong (∘-resp-≈ʳ (⟨⟩-cong₂ β′ π₂∘⁂)) ⟩
                λg (eval′ ∘ (⟨ (λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ∘ eval′ , id ∘ π₂ ⟩)) ≈⟨ λ-cong (∘-resp-≈ʳ (sym ⁂∘⟨⟩)) ⟩
                λg (eval′ ∘ (((λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ⁂ id) ∘ ⟨ eval′ , π₂ ⟩)) ≈⟨ λ-cong sym-assoc ⟩
                λg ((eval′ ∘ ((λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ⁂ id)) ∘ ⟨ eval′ , π₂ ⟩) ≈⟨ λ-cong (∘-resp-≈ˡ β′) ⟩
                λg (((eval′ ∘ ⟨ eval′ , π₂ ⟩)) ∘ ⟨ eval′ , π₂ ⟩) ≈⟨ λ-cong assoc ⟩
                λg (eval′ ∘ ⟨ eval′ , π₂ ⟩ ∘ ⟨ eval′ , π₂ ⟩) ≈⟨ λ-cong (∘-resp-≈ʳ ⟨⟩∘) ⟩
                λg (eval′ ∘ ⟨ eval′ ∘ ⟨ eval′ , π₂ ⟩ , π₂ ∘ ⟨ eval′ , π₂ ⟩ ⟩) ≈⟨ λ-cong (∘-resp-≈ʳ (⟨⟩-congˡ project₂)) ⟩
                λg (eval′ ∘ ⟨ eval′ ∘ ⟨ eval′ , π₂ ⟩ , π₂ ⟩) ≈⟨ λ-cong (∘-resp-≈ʳ (⟨⟩-congˡ (sym identityˡ))) ⟩
                λg (eval′ ∘ ⟨ eval′ ∘ ⟨ eval′ , π₂ ⟩ , id ∘ π₂ ⟩) ≈⟨ sym (λ-cong (∘-resp-≈ʳ (⟨⟩-cong₂ β′ π₂∘⁂))) ⟩
                λg (eval′ ∘ ⟨ eval′ ∘ ((λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ⁂ id) , π₂ ∘ ((λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ⁂ id) ⟩) ≈⟨ λ-cong (∘-resp-≈ʳ (sym ⟨⟩∘)) ⟩
                λg (eval′ ∘ ⟨ eval′ , π₂ ⟩ ∘ ((λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ⁂ id)) ≈⟨ λ-cong sym-assoc ⟩
                λg ((eval′ ∘ ⟨ eval′ , π₂ ⟩) ∘ ((λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ⁂ id)) ≈⟨ sym (exp.subst product product) ⟩
                (λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ∘ (λg (eval′ ∘ ⟨ eval′ , π₂ ⟩)) ∎