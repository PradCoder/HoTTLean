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

hott0
  /-- The type `A` is (-1)-truncated-/
  def isProp₀ (A : Type) : Type :=
    ∀ (a a' : A), (Identity a a')

hott0
  /-- The type `A` is 0-truncated-/
  def isSet₀ (A : Type) : Type :=
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

-- hott0 def setIdentitySystem {A: Type} {R : A → A → Type} : ((r : ∀ x : A, R x x ) →
--   ((∀ x y : A, isProp₀ (R x y)) → (isIdentitySystem R r)) := sorry

-- hott0 def notnotStableIdentitySystem : {∀ x y : A} {¬¬(x = y) → x = y} → isIdentitySystem (λ x y. ¬¬(x = y)) (λ x. x ≠ x. absurd (x ≠ x) (refl))

-- hott0 def identitySystemPathEq : Type := sorry

-- hott0 def isIdentitySystem R r → ∀ x y : A, (x = y) ≃ R x y
-- hott0 def hedberg {A : Type} : (∀ x y : A, ((x = y) ⊕ (¬ (x = y))) → isSet₀ (A)) := sorry


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

-- Decidable equaltiy
-- hott0 def Discrete (A : Type): Type :=
--   ∀ (x y : A), (Identity x y) ⊕ (Identity x y → Empty)

-- Notation
-- Implementing Unit and Empty types, for Binary definitions
-- Current version axiomatizes them, but other forms exist Church/Bóhm-Berarducci

-- Unit type and constructor
hott0 axiom Unit : Type
hott0 axiom star : Unit

-- Unit eliminator : to prove something ∀ x : Unit, prove for star
-- Don't need
hott0 axiom unit_rec
    {C : Type}
    (c : C)
    : Unit → C

-- Computation rule
-- Same as before, Every function out is constant
hott0 axiom unit_rec_star
    {C : Type}
    (c : C)
    : Identity (unit_rec c star) c

-- Uniqueness: any element of Unit equals star
hott0 axiom unit_eta
    (x : Unit)
    : Identity x star

-- Empty type
hott0 axiom Empty : Type

-- Empty eliminator (ex falso): from Empty you can prove anything
hott0 axiom empty_rec
    {C : Type}
    : Empty → C

--Bool
-- Unit is a proposition
hott0 def unit_is_prop : isProp₀ Unit :=
  λ x y => (unit_eta x).trans₀ (unit_eta y).symm₀

hott0 axiom Bool : Type
hott0 axiom false : Bool
hott0 axiom true : Bool
-- Value-level eliminator (for values)
hott0 axiom bool_rec_val {C : Type} (c_false c_true : C) : Bool → C

-- TYPE-level eliminator (for types)
hott0 axiom bool_rec_type (A B : Type) : Bool → Type

-- hott0 axiom bool_elim₀ (P : Bool → Type) (pt : P true) (pf : P false) (b : Bool) : P b
-- hott0 axiom bool_elim_true₀ {P : Bool → Type} {pt : P true} {pf : P false} : Identity (bool_elim₀ P pt pf true) pt
-- hott0 axiom bool_elim_false₀ {P : Bool → Type} {pt : P true} {pf : P false} : Identity (bool_elim₀ P pt pf false) pf

-- hott0 axiom bool_elim₁ (P : Bool → Type 1) (pt : P true) (pf : P false) (b : Bool) : P b
-- hott0 axiom bool_elim_true₁ {P : Bool → Type 1} {pt : P true} {pf : P false} : Identity (bool_elim₁ P pt pf true) pt
-- hott0 axiom bool_elim_false₁ {P : Bool → Type 1} {pt : P true} {pf : P false} : Identity (bool_elim₁ P pt pf false) pf

-- hott0 def bool_rec_type (A B : Type) := bool_elim₁ (fun _ => Type) A B

-- Computation rule
hott0 axiom bool_rec_type_true (A B : Type) : Identity (bool_rec_type A B true) A
hott0 axiom bool_rec_type_false (A B : Type) : Identity (bool_rec_type A B false) B

-- Sum type
hott0 def Sum (A B : Type) : Type :=
  Σ (b : Bool), bool_rec_type A B b

-- In your Bool section, add these inverse axioms:
hott0 axiom bool_rec_type_true_inv (A B : Type)
    : Identity A (bool_rec_type A B true)

hott0 axiom bool_rec_type_false_inv (A B : Type)
    : Identity B (bool_rec_type A B false)

-- Helper for coercion along type paths
hott0 def coe {A B : Type} (h : Identity A B) : A → B :=
    λ a => h.rec (motive := λ T _ => T) a

-- Now constructors work:
hott0 def inl {A B : Type} (a : A) : Sum A B :=
  ⟨true, coe (bool_rec_type_true_inv A B) a⟩

hott0 def inr {A B : Type} (b : B) : Sum A B :=
  ⟨false, coe (bool_rec_type_false_inv A B) b⟩

--- NOOOO!!! I can't use my own notation for the elaborator
--infixr:30 " ⊎ " => Sum

hott0 def Not (A : Type) : Type := A → Empty

-- notation "¬" A => Not A

-- Decidable equality
hott0 def Discrete (A : Type) : Type :=
  ∀ (x  y : A), Sum (Identity x y) (Not (Identity x y))

-- Sum eliminator
-- helpers for Sum eliminator
hott0 def sum_rec_helper_true
    {A B C : Type}
    (f : A → C)
    (x : bool_rec_type A B true)
    : C :=
  f (coe (bool_rec_type_true A B) x)

hott0 def sum_rec_helper_false
    {A B C : Type}
    (f : B → C)
    (x : bool_rec_type A B false)
    : C :=
  f (coe (bool_rec_type_false A B) x)

-- HACKS!
hott0 axiom bool_rec_dep
    {C : Bool → Type}
    (c_false : C false)
    (c_true : C true)
    (b : Bool)
    : C b

-- EVEN MORE HACKS!!
-- Sum Eliminator we need
hott0 def sum_rec
    {A B C : Type}
    (f : A → C)
    (g : B → C)
    : Sum A B → C
:= λ s =>
    (@bool_rec_dep
      (λ b => bool_rec_type A B b → C)
      (sum_rec_helper_false g)
      (sum_rec_helper_true f)
      s.fst)
    s.snd -- We need to think interms of explicit projections

-- Type-level sum eliminator (returns types, not values)
-- Axiomatize type-level sum eliminator
hott0 axiom sum_rec_type
    {A B : Type}
    (f : A → Type)
    (g : B → Type)
    : Sum A B → Type

-- Rijke's Relation R Theorem 12.3.4
hott0 def R' (A : Type) (x y : A)
    (q : Sum (Identity x y) (Not (Identity x y)))
    : Type :=
  sum_rec_type (λ _ => Unit) (λ _ => Empty) q

-- The main relation R using decidability
hott0 def R (A : Type) (dec : Discrete A) (x y : A) : Type :=
  R' A x y (dec x y)

-- R(x,y) is always a proposition
hott0 axiom R_is_prop
    (A : Type)
    (dec : Discrete A)
    (x y : A)
    : isProp₀ (R A dec x y)

-- R(x,y) implies identity
hott0 axiom R_to_eq
    (A : Type)
    (dec : Discrete A)
    (x y : A)
    : R A dec x y → Identity x y

-- R is reflexive
hott0 axiom R_refl
    (A : Type)
    (dec : Discrete A)
    (x : A)
    : R A dec x x

-- AXIOMATIZED FOR NOW -- BUT should be worked out for theorem
-- The identity system theorem
-- Rijke's stuff and 1 lab proof, pretty much directly
hott0 axiom identity_system_to_set
    {A : Type}
    {R : A → A → Type}
    {r : ∀ x, R x x}
    (R_to_id : ∀ x y, R x y → Identity x y)
    (R_prop : ∀ x y, isProp₀ (R x y))
    : isSet₀ A

-- Hedberg's Theorem: Types with decidable equality are sets
hott0 def hedberg (A : Type) (dec : Discrete A) : isSet₀ A :=
  @identity_system_to_set A (R A dec) (R_refl A dec)
    (R_to_eq A dec)
    (R_is_prop A dec)
