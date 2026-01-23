import HoTTLean.Frontend.Commands

noncomputable section

declare_theory hott0

namespace HoTT0

hott0 def isSection₀₀ {A B : Type} (f : A → B) (g : B → A) : Type :=
  ∀ (a : A), Identity (g (f a)) a

hott0 def isEquiv₀₀ {A B : Type} (f : A → B) : Type :=
  Σ (g : B → A),
    Σ (h : B → A),
      Σ (_ : isSection₀₀ f g),
        isSection₀₀ h f

hott0 def happly {A : Type} {B : A → Type} {f g : (a : A) → B a} :
    Identity f g → (a : A) → Identity (f a) (g a) :=
  fun h _ => h.rec .rfl₀

hott0
  /-- HoTT book, Axiom 2.9.3. -/
  axiom funext₀₀ {A : Type} {B : A → Type} (f g : (a : A) → B a) :
    isEquiv₀₀ (@happly _ _ f g)

hott0 def isSection₁₀ {A : Type 1} {B : Type} (f : A → B) (g : B → A) : Type 1 :=
  ∀ (a : A), Identity (g (f a)) a

hott0 def isSection₀₁ {A : Type} {B : Type 1} (f : A → B) (g : B → A) : Type :=
  ∀ (a : A), Identity (g (f a)) a

hott0 def isEquiv₁₀ {A : Type 1} {B : Type} (f : A → B) : Type 1 :=
  Σ (g : B → A),
    Σ (h : B → A),
      Σ (_ : isSection₁₀ f g),
        isSection₀₁ h f

hott0 def isEquiv₁₀_grpd {A : Type 1} {B : Type} (f : A → B) : Type 1 :=
  Σ (g : B → A),
    Σ (_ : isSection₁₀ f g),
      isSection₀₁ g f

hott0 def transport₀ {A B : Type} (h : Identity A B) (a : A) : B :=
  h.rec a

hott0 def isEquiv₀₀_transport₀ {A B : Type} (h : Identity A B) : isEquiv₀₀ (transport₀ h) :=
  h.rec ⟨fun a => a, fun a => a, fun _ => .rfl₀, fun _ => .rfl₀⟩

hott0 def Identity.toEquiv₀₀ {A B : Type} : Identity A B → Σ (f : A → B), isEquiv₀₀ f :=
  fun h => ⟨transport₀ h, isEquiv₀₀_transport₀ h⟩

hott0 def isProp₀ (A : Type) : Type :=
  ∀ (a a' : A) (h h' : Identity a a'), Identity h h'

hott0 def isSet₀ (A : Type) : Type :=
  ∀ (a b : A), isProp₀ (Identity a b)

hott0
  /-- The univalence axiom for sets. See HoTT book, Axiom 2.10.3. -/
  axiom setUv₀₀ {A B : Type} (A_set : isSet₀ A) (B_set : isSet₀ B) :
    isEquiv₁₀ (@Identity.toEquiv₀₀ A B)

-- Beginning Magma Definition
hott0 def magma :=  Σ (A : Type), A → (A → A)


-- Hedberg's Rijke 12.3.5
-- hott0 theorem hedberg₀ {A : Type} (Π x, y : A) (x =y) + (x ≠ y)
-- that A has decidable equality. Furthermore, let U be a universe containing
-- the type A. We will prove that A is a set by Applying Theorem 12.3.4
-- Recall Currying
-- Prove by Hand

-- Hedberg's Theorem - Rijke 12.3.5
-- hott0 theorem hedberg₀ {A : Type} (Π x, y : A) (x =y) + (x ≠ y)
-- that A has decidable equality. Furthermore, let U be a universe containing
-- the type A. We will prove that A is a set by Applying Theorem 12.3.4

-- Define Is identity System
-- Set-Identity-System
-- 1Lab Definition : https://1lab.dev/1Lab.Path.IdentitySystem.html#sets-and-hedbergs-theorem

hott0 def setIdentitySystem {A: Type} {R : A → A → Type} : ((r : ∀ x : A, R x x ) →
  ((∀ x y : A, isProp₀ (R x y)) → (isIdentitySystem R r)) := sorry

hott0 def notnotStableIdentitySystem : {∀ x y : A} {¬¬(x = y) → x = y} → isIdentitySystem (λ x y. ¬¬(x = y)) (λ x. x ≠ x. absurd (x ≠ x) (refl))

hott0 def identitySystemPathEq : Type := sorry

hott0 def isIdentitySystem R r → ∀ x y : A, (x = y) ≃ R x y
hott0 def hedberg {A : Type} : (∀ x y : A, ((x = y) ⊕ (¬ (x = y))) → isSet₀ (A)) := sorry


-- What I'm trying out here, in case 1 is better than the other, Rijke's is looks better (the 2nd one)
/-
Hedberg's Theorem - Proof Structure (1lab.dev)

Hedberg's theorem states that any type A with decidable equality is a set A.

Proof Structure:
1. Show that decidable equality implies that the type has a stable identity system.
2. Show ¬¬ (x=y) is a prop for all x,y : A.
3. Build the identity system using R(x,y) : ¬¬ (x=y).
4. Identity system with prop-valued relations implies that A is a set.

Lemma 1: Show that decidable equality implies ¬¬-elimination
Lemma 2: Step 2
Lemma 3: Identity system (R, r) where R(x,y) := ¬¬(x = y)

Conclude: R pointwise prop → A is a set, by identity system implies A is a set.
-/



/-
Hedberg's Theorem - Proof Structure (Rijke 12.3.5)

1. Build R(x,y) by pattern matching on decidable equality

2. Do case analysis on R(x,y) decidable equality:
- Case 1: x = y (Prop)
- Case 2: x ≠ y (Prop)

3. R(x,y) → (x =y)

4. Apply Theorem 12.3.4 to conclude that A is a set.

So we need to prove 12.3.4 aswell!
-/
