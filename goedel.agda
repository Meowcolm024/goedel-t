module goedel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as RT
open RT using (Star; ε; _◅_; _◅◅_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; _≡_)

postulate
  extensionality : {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → ((x : A) → f x ≡ g x) → f ≡ g

infixr 7 _⇒_

data Ty : Set where
  `ℕ  : Ty
  _⇒_ : Ty → Ty → Ty

infixl 5 _▷_

data Ctx : Set where
  ∅   : Ctx
  _▷_ : Ctx → Ty → Ctx

infix  4 _∋_

data _∋_ : Ctx → Ty → Set where
  Z : ∀ {Γ A}           → Γ ▷ A ∋ A
  S : ∀ {Γ A B} → Γ ∋ A → Γ ▷ B ∋ A

infix  4 _⊢_

infix  9 `_
infixr 5 ƛ_
infixl 7 _·_

data _⊢_ (Γ : Ctx) : Ty → Set where
  `_  : ∀ {A}   → Γ ∋ A                           → Γ ⊢ A
  ƛ_  : ∀ {A B} → Γ ▷ A ⊢ B                       → Γ ⊢ A ⇒ B
  _·_ : ∀ {A B} → Γ ⊢ A ⇒ B      → Γ ⊢ A          → Γ ⊢ B
  `Z  :                                             Γ ⊢ `ℕ
  `S  :           Γ ⊢ `ℕ                          → Γ ⊢ `ℕ 
  rec : ∀ {A}   → Γ ⊢ `ℕ → Γ ⊢ A → Γ ▷ `ℕ ▷ A ⊢ A → Γ ⊢ A

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

lift : ∀ {Γ Δ A} → Ren Γ Δ → Ren (Γ ▷ A) (Δ ▷ A)
lift ρ Z     = Z
lift ρ (S x) = S (ρ x)

ren : ∀ {Γ Δ} → Ren Γ Δ → ∀ {A} → Γ ⊢ A → Δ ⊢ A
ren ρ (` x)       = ` ρ x
ren ρ (ƛ M)       = ƛ ren (lift ρ) M
ren ρ (M · N)     = (ren ρ M) · (ren ρ N)
ren ρ `Z          = `Z
ren ρ (`S M)      = `S (ren ρ M)
ren ρ (rec L M N) = rec (ren ρ L) (ren ρ M) (ren (lift (lift ρ)) N)

weaken : ∀ {Γ A B} → Γ ⊢ A → Γ ▷ B ⊢ A
weaken = ren S

Sub : Ctx → Ctx → Set
Sub Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

lifts : ∀ {Γ Δ A} → Sub Γ Δ → Sub (Γ ▷ A) (Δ ▷ A)
lifts σ Z     = ` Z
lifts σ (S x) = weaken (σ x)

sub : ∀ {Γ Δ} → Sub Γ Δ → ∀ {A} → Γ ⊢ A → Δ ⊢ A
sub σ (` x)       = σ x
sub σ (ƛ M)       = ƛ sub (lifts σ) M
sub σ (M · N)     = (sub σ M) · (sub σ N)
sub σ `Z          = `Z
sub σ (`S M)      = `S (sub σ M)
sub σ (rec L M N) = rec (sub σ L) (sub σ M) (sub (lifts (lifts σ)) N)

infixr 6 _•_

_•_ : ∀ {Γ Δ A} → (M : Δ ⊢ A) → (σ : Sub Γ Δ) → Sub (Γ ▷ A) Δ
(M • σ) Z     = M
(M • σ) (S x) = σ x

ids : ∀ {Γ} → Sub Γ Γ
ids x = ` x

sub-zero : ∀ {Γ A} → Γ ⊢ A → Sub (Γ ▷ A) Γ
sub-zero M = M • ids 

_[_] : ∀ {Γ A B} → Γ ▷ B ⊢ A → Γ ⊢ B → Γ ⊢ A
_[_] M N = sub (sub-zero N) M

data Val {Γ} : ∀ {A} → (Γ ⊢ A) → Set where
  V-ƛ  : ∀ {A B} → (M : Γ ▷ A ⊢ B) → Val (ƛ M)
  V-`Z :                             Val `Z
  V-`S : ∀ {M}   → Val M           → Val (`S M)

infix  2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·ₗ : ∀ {Γ A B} {M M' : Γ ⊢ A ⇒ B} {N}
    → M —→ M'
      ----------------
    → M · N —→ M' · N

  ξ-·ᵣ : ∀ {Γ A B} {M : Γ ▷ A ⊢ B} {N N'}
    → N —→ N'
      ------------------------
    → (ƛ M) · N —→ (ƛ M) · N'

  β-· : ∀ {Γ A B} {M : Γ ▷ A ⊢ B} {N}
    → Val N
      ---------------------
    → (ƛ M) · N —→ M [ N ]

  ξ-`S : ∀ {Γ} {M M' : Γ ⊢ `ℕ}
    → M —→ M'
      --------------
    → `S M —→ `S M'

  ξ-rec : ∀ {Γ A} {L L'} {M : Γ ⊢ A} {N}
    → L —→ L'
      ------------------------
    → rec L M N —→ rec L' M N

  β-rec₀ : ∀ {Γ A} {M : Γ ⊢ A} {N}
      ----------------
    → rec `Z M N —→ M

  β-recₛ : ∀ {Γ A} {L} {M : Γ ⊢ A} {N}
    → Val L
      ------------------------------------------------
    → rec (`S L) M N —→ sub ((rec L M N) • L • ids) N

ℕ-elim : ∀ {A : Set} → ℕ → A → (ℕ → A → A) → A
ℕ-elim zero    z k = z
ℕ-elim (suc n) z k = k n (ℕ-elim n z k)

⟦_⟧ᵀ : Ty → Set
⟦ `ℕ    ⟧ᵀ = ℕ
⟦ A ⇒ B ⟧ᵀ = ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ

⟦_⟧ᴳ : Ctx → Set
⟦ ∅     ⟧ᴳ = ⊤
⟦ Γ ▷ A ⟧ᴳ = ⟦ Γ ⟧ᴳ × ⟦ A ⟧ᵀ

⟦_⟧ᴸ : ∀ {Γ A} → Γ ∋ A → ⟦ Γ ⟧ᴳ → ⟦ A ⟧ᵀ
⟦ Z   ⟧ᴸ (η , A) = A
⟦ S x ⟧ᴸ (η , A) = ⟦ x ⟧ᴸ η

⟦_⟧ᴱ : ∀ {Γ A} → (M : Γ ⊢ A) → (η : ⟦ Γ ⟧ᴳ) → ⟦ A ⟧ᵀ
⟦ ` x       ⟧ᴱ η = ⟦ x ⟧ᴸ η
⟦ ƛ M       ⟧ᴱ η = λ x → ⟦ M ⟧ᴱ (η , x)
⟦ M · N     ⟧ᴱ η = (⟦ M ⟧ᴱ η) (⟦ N ⟧ᴱ η)
⟦ `Z        ⟧ᴱ η = zero
⟦ `S M      ⟧ᴱ η = suc (⟦ M ⟧ᴱ η)
⟦ rec L M N ⟧ᴱ η = ℕ-elim (⟦ L ⟧ᴱ η) (⟦ M ⟧ᴱ η) λ n z → ⟦ N ⟧ᴱ ((η , n) , z)

⟦_⟧ : ∀ {A} → (M : ∅ ⊢ A) → ⟦ A ⟧ᵀ
⟦ M ⟧ = ⟦ M ⟧ᴱ tt

Ren† : ∀ {Γ Δ : Ctx} (η : ⟦ Γ ⟧ᴳ) (γ : ⟦ Δ ⟧ᴳ) (ρ : Ren Γ Δ) → Set
Ren† {Γ} {Δ} η γ ρ = ∀ {A} (x : Γ ∋ A) → ⟦ x ⟧ᴸ η ≡ ⟦ ρ x ⟧ᴸ γ

lift-Ren† : ∀ {Γ Δ} (η : ⟦ Γ ⟧ᴳ) (γ : ⟦ Δ ⟧ᴳ) (ρ : Ren Γ Δ) → Ren† η γ ρ → ∀ {A} (v : ⟦ A ⟧ᵀ) → Ren† (η , v) (γ , v) (lift ρ)
lift-Ren† η γ ρ ρ† v Z     = refl
lift-Ren† η γ ρ ρ† v (S x) = ρ† x

ren-Ren† : ∀ {Γ Δ A} (η : ⟦ Γ ⟧ᴳ) (γ : ⟦ Δ ⟧ᴳ) (ρ : Ren Γ Δ) (ρ† : Ren† η γ ρ) → ∀ (M : Γ ⊢ A) → ⟦ M ⟧ᴱ η ≡ ⟦ ren ρ M ⟧ᴱ γ
ren-Ren† η γ ρ ρ† (` x) = ρ† x
ren-Ren† η γ ρ ρ† (ƛ M) = extensionality λ x → ren-Ren† (η , x) (γ , x) (lift ρ) (lift-Ren† η γ ρ ρ† x) M
ren-Ren† η γ ρ ρ† (M · N) = Eq.cong₂ (λ x y → x y) (ren-Ren† η γ ρ ρ† M) (ren-Ren† η γ ρ ρ† N)
ren-Ren† η γ ρ ρ† `Z = refl
ren-Ren† η γ ρ ρ† (`S M) = Eq.cong suc (ren-Ren† η γ ρ ρ† M)
ren-Ren† η γ ρ ρ† (rec L M N) = Eq.trans
  (Eq.cong₂ (λ x y → ℕ-elim x y λ v k → ⟦ N ⟧ᴱ ((η , v) , k) ) (ren-Ren† η γ ρ ρ† L) (ren-Ren† η γ ρ ρ† M))
  (Eq.cong (ℕ-elim (⟦ ren ρ L ⟧ᴱ γ) (⟦ ren ρ M ⟧ᴱ γ)) (extensionality λ v → extensionality λ k →
    ren-Ren† ((η , v) , k) ((γ , v) , k) (lift (lift ρ)) (lift-Ren† (η , v) (γ , v) (lift ρ) (lift-Ren† η γ ρ ρ† v) k) N))

Sub† : ∀ {Γ Δ : Ctx} (η : ⟦ Γ ⟧ᴳ) (γ : ⟦ Δ ⟧ᴳ) (σ : Sub Γ Δ) → Set  
Sub† {Γ} {Δ} η γ σ = ∀ {A} (x : Γ ∋ A) → ⟦ x ⟧ᴸ η ≡ ⟦ σ x ⟧ᴱ γ

lifts-Sub† : ∀ {Γ Δ} (η : ⟦ Γ ⟧ᴳ) (γ : ⟦ Δ ⟧ᴳ) (σ : Sub Γ Δ) → Sub† η γ σ → ∀ {A} (v : ⟦ A ⟧ᵀ) → Sub† (η , v) (γ , v) (lifts σ)
lifts-Sub† η γ σ σ† v Z     = refl
lifts-Sub† η γ σ σ† v (S x) = Eq.trans (σ† x) (ren-Ren† γ (γ , v) S (λ _ → refl) (σ x))

sub-Sub† : ∀ {Γ Δ} (η : ⟦ Γ ⟧ᴳ) (γ : ⟦ Δ ⟧ᴳ) (σ : Sub Γ Δ) → Sub† η γ σ → ∀ {A} (M : Γ ⊢ A) → ⟦ M ⟧ᴱ η ≡ ⟦ sub σ M ⟧ᴱ γ
sub-Sub† η γ σ σ† (` x)       = σ† x
sub-Sub† η γ σ σ† (ƛ M)       = extensionality λ x → sub-Sub† (η , x) (γ , x) (lifts σ) (lifts-Sub† η γ σ σ† x) M
sub-Sub† η γ σ σ† (M · N)     = Eq.cong₂ (λ x y → x y) (sub-Sub† η γ σ σ† M) (sub-Sub† η γ σ σ† N)
sub-Sub† η γ σ σ† `Z          = refl
sub-Sub† η γ σ σ† (`S M)      = Eq.cong suc (sub-Sub† η γ σ σ† M)
sub-Sub† η γ σ σ† (rec L M N) = Eq.trans
  (Eq.cong₂ (λ x y → ℕ-elim x y λ v k → ⟦ N ⟧ᴱ ((η , v), k) ) (sub-Sub† η γ σ σ† L) (sub-Sub† η γ σ σ† M))
  (Eq.cong (ℕ-elim (⟦ sub σ L ⟧ᴱ γ) (⟦ sub σ M ⟧ᴱ γ)) (extensionality λ v → extensionality λ k →
    sub-Sub† ((η , v) , k) ((γ , v) , k) (lifts (lifts σ)) (lifts-Sub† (η , v) (γ , v) (lifts σ) (lifts-Sub† η γ σ σ† v) k) N))

ids-Sub† : ∀ {Γ} (η : ⟦ Γ ⟧ᴳ) → Sub† η η ids
ids-Sub† η x = refl

cons-Sub† : ∀ {Γ Δ} (η : ⟦ Γ ⟧ᴳ) (γ : ⟦ Δ ⟧ᴳ) (σ : Sub Γ Δ) → Sub† η γ σ → ∀ {A} (M : Δ ⊢ A) → Sub† (η , ⟦ M ⟧ᴱ γ) γ (M • σ)
cons-Sub† η γ σ σ† M Z     = refl
cons-Sub† η γ σ σ† M (S x) = σ† x

sub-zero-Sub† : ∀ {Γ A B} (η : ⟦ Γ ⟧ᴳ) (M : Γ ▷ A ⊢ B) (N : Γ ⊢ A) → ⟦ M ⟧ᴱ (η , ⟦ N ⟧ᴱ η) ≡ ⟦ M [ N ] ⟧ᴱ η
sub-zero-Sub† η M N = sub-Sub† (η , ⟦ N ⟧ᴱ η) η (sub-zero N) (cons-Sub† η η ids (ids-Sub† η) N) M 

—→-⟦⟧ᴱ : ∀ {Γ A} {M N : Γ ⊢ A} → (η : ⟦ Γ ⟧ᴳ) → M —→ N → ⟦ M ⟧ᴱ η ≡ ⟦ N ⟧ᴱ η
—→-⟦⟧ᴱ {M = M · N}          η (ξ-·ₗ M—→N)  = Eq.cong (λ x → x (⟦ N ⟧ᴱ η)) (—→-⟦⟧ᴱ η M—→N)
—→-⟦⟧ᴱ {M = (ƛ M) · N}      η (ξ-·ᵣ M—→N)  = Eq.cong (λ x → ⟦ M ⟧ᴱ (η , x)) (—→-⟦⟧ᴱ η M—→N)
—→-⟦⟧ᴱ {M = (ƛ M) · N}      η (β-· V)      = sub-zero-Sub† η M N
—→-⟦⟧ᴱ                      η (ξ-`S M—→N)  = Eq.cong suc (—→-⟦⟧ᴱ η M—→N)
—→-⟦⟧ᴱ {M = rec L M N}      η (ξ-rec M—→N) = Eq.cong (λ x → ℕ-elim x (⟦ M ⟧ᴱ η) λ v k → ⟦ N ⟧ᴱ ((η , v) , k)) (—→-⟦⟧ᴱ η M—→N)
—→-⟦⟧ᴱ                      η β-rec₀       = refl
—→-⟦⟧ᴱ {M = rec (`S L) M N} η (β-recₛ V)   = sub-Sub† ((η , ⟦ L ⟧ᴱ η) , ⟦ rec L M N ⟧ᴱ η) η (rec L M N • sub-zero L)
  (cons-Sub† (η , ⟦ L ⟧ᴱ η) η (sub-zero L) (cons-Sub† η η ids (ids-Sub† η) L) (rec L M N)) N

-- soundness
—→-⟦⟧ : ∀ {A} {M N : ∅ ⊢ A} → M —→ N → ⟦ M ⟧ ≡ ⟦ N ⟧
—→-⟦⟧ M—→N = —→-⟦⟧ᴱ tt M—→N

progress : ∀ {A} (M : ∅ ⊢ A) → ∃[ N ] (M —→ N) ⊎ Val M
progress (ƛ M)            = inj₂ (V-ƛ M)
progress (M · N) with progress  M
... | inj₁ (M' , M—→M')   = inj₁ (M' · N , ξ-·ₗ M—→M')
... | inj₂ (V-ƛ M') with progress N
...   | inj₁ (N' , N—→N') = inj₁ ((ƛ M') · N' , ξ-·ᵣ N—→N')
...   | inj₂ V            = inj₁ (M' [ N ] , β-· V) 
progress `Z               = inj₂  V-`Z
progress (`S M) with progress M
... | inj₁ (M' , M—→M')   = inj₁ (`S M' , ξ-`S M—→M')
... | inj₂ V              = inj₂ (V-`S V)
progress (rec L M N) with progress L
... | inj₁ (L' , L—→L')   = inj₁ (rec L' M N , ξ-rec L—→L')
... | inj₂ V-`Z           = inj₁ (M , β-rec₀)
... | inj₂ (V-`S V)       = inj₁ (_ , β-recₛ V)

_—↠_ : ∀ {Γ A} → (M N : Γ ⊢ A) → Set
_—↠_ M N = Star _—→_ M N

—↠-⟦⟧ : ∀ {A} {M N : ∅ ⊢ A} → M —↠ N → ⟦ M ⟧ ≡ ⟦ N ⟧
—↠-⟦⟧ ε               = refl
—↠-⟦⟧ (M—→M' ◅ M'—↠N) = Eq.trans (—→-⟦⟧ M—→M') (—↠-⟦⟧ M'—↠N)

-- unfortunately we still need a normalization proof
Halts : ∀ {A} → (M : ∅ ⊢ A) → Set
Halts M = ∃[ N ] (M —↠ N) × Val N

ℋ : ∀ {A} (M : ∅ ⊢ A) → Set
ℋ {A = `ℕ}    M = Halts M
ℋ {A = A ⇒ B} M = Halts M × (∀ {N} → ℋ N → ℋ (M · N))

ℋ-Halts : ∀ {A} {M : ∅ ⊢ A} → ℋ M → Halts M
ℋ-Halts {A = `ℕ}    H       = H
ℋ-Halts {A = A ⇒ B} (H , k) = H

⊨_ : ∀ {Γ} (σ : Sub Γ ∅) → Set
⊨_ {Γ} σ = ∀ {A} (x : Γ ∋ A) → ℋ (σ x)

postulate
  sub-id : ∀ {Γ A} {M : Γ ⊢ A} → M ≡ sub ids M
  -- TODO
  halts : ∀ {Γ A} {σ : Sub Γ ∅} → ⊨ σ → (M : Γ ⊢ A) → ℋ (sub σ M)

eval : ∀ {A} → (M : ∅ ⊢ A) → Halts M
eval M = ℋ-Halts (Eq.subst ℋ (Eq.sym sub-id) (halts {σ = ids} (λ ()) M))

eval≈denote : ∀ {A} → (M : ∅ ⊢ A) → ∃[ N ] (M —↠ N) × Val N × ⟦ M ⟧ ≡ ⟦ N ⟧
eval≈denote M with eval M
... | N , M—↠N , V = N , M—↠N , V , —↠-⟦⟧ M—↠N
