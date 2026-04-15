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

-- Unit: the type with exactly one element.
hott0 axiom Unit : Type
hott0 axiom star : Unit -- the unique constructor; every element of Unit is equal to this

-- Eliminator: to define a function out of Unit, just say what happens at star.
-- Every function Unit → C is constant since there is only one input.
hott0 axiom unit_rec
    {C : Type}
    (c : C)      -- the value to return; this is the only case
    : Unit → C

-- Computation rule: unit_rec c applied to star reduces to c.
hott0 axiom unit_rec_star
    {C : Type}
    (c : C)
    : Identity (unit_rec c star) c

-- η-rule (uniqueness): every element x : Unit is equal to star.
-- Together with unit_rec_star this fully pins down Unit up to identity.
hott0 axiom unit_eta
    (x : Unit)
    : Identity x star

-- Empty: the type with no elements (falsehood / absurdity).
hott0 axiom Empty : Type

-- Eliminator (ex falso quodlibet): from a proof of Empty you can derive anything.
-- No cases to handle — Empty has no constructors.
hott0 axiom empty_rec
    {C : Type}
    : Empty → C

-- Unit is a proposition: any two elements x y : Unit are equal.
-- Proof: x = star (unit_eta x), and y = star (unit_eta y), so x = star = y.
--   (unit_eta x)          : Identity x star
--   (unit_eta y).symm₀    : Identity star y
--   .trans₀ of the above  : Identity x y
hott0 def unit_is_prop : isProp₀ Unit :=
  λ x y => (unit_eta x).trans₀ (unit_eta y).symm₀

-- Bool: the type with exactly two elements.
hott0 axiom Bool : Type
hott0 axiom false : Bool -- first constructor
hott0 axiom true : Bool  -- second constructor

-- Non-dependent (value-level) eliminator: choose a value for each branch.
-- Every Bool → C is determined by its values at false and true.
hott0 axiom bool_rec_val {C : Type} (c_false c_true : C) : Bool → C

-- Type-level eliminator: choose a *type* for each branch.
-- bool_rec_type A B true  is definitionally A  (enforced by bool_rec_type_true below)
-- bool_rec_type A B false is definitionally B  (enforced by bool_rec_type_false below)
-- Axiomatized directly because deriving it from a dependent eliminator
-- runs into universe level issues — see the universe polymorphism note above.
hott0 axiom bool_rec_type (A B : Type) : Bool → Type

-- Dependent eliminators are commented out due to universe level mismatches.
-- bool_elim₀ would work for P : Bool → Type (level 0 motive)
-- but passing `fun _ => Type` to bool_elim₁ (level 1 motive) fails
-- because Type 0 ≢ Type 1 in Lean's type system.
-- hott0 axiom bool_elim₀ (P : Bool → Type) (pt : P true) (pf : P false) (b : Bool) : P b
-- hott0 axiom bool_elim_true₀ {P : Bool → Type} {pt : P true} {pf : P false} : Identity (bool_elim₀ P pt pf true) pt
-- hott0 axiom bool_elim_false₀ {P : Bool → Type} {pt : P true} {pf : P false} : Identity (bool_elim₀ P pt pf false) pf
-- hott0 axiom bool_elim₁ (P : Bool → Type 1) (pt : P true) (pf : P false) (b : Bool) : P b
-- hott0 axiom bool_elim_true₁ {P : Bool → Type 1} {pt : P true} {pf : P false} : Identity (bool_elim₁ P pt pf true) pt
-- hott0 axiom bool_elim_false₁ {P : Bool → Type 1} {pt : P true} {pf : P false} : Identity (bool_elim₁ P pt pf false) pf
-- hott0 def bool_rec_type (A B : Type) := bool_elim₁ (fun _ => Type) A B

-- Computation rules: applying bool_rec_type to true gives A, to false gives B.
hott0 axiom bool_rec_type_true  (A B : Type) : Identity (bool_rec_type A B true)  A
hott0 axiom bool_rec_type_false (A B : Type) : Identity (bool_rec_type A B false) B

-- Sum type (coproduct A ⊎ B): a dependent pair of a boolean tag and a payload.
--   tag = true  → payload lives in bool_rec_type A B true  ≡ A  (left summand)
--   tag = false → payload lives in bool_rec_type A B false ≡ B  (right summand)
hott0 def Sum (A B : Type) : Type :=
  Σ (b : Bool), bool_rec_type A B b

-- The computation rules above give Identity (bool_rec_type A B true) A,
-- but to *inject* into Sum we need the equality in the other direction.
-- These inverse axioms are needed so we can coerce a : A into bool_rec_type A B true.
hott0 axiom bool_rec_type_true_inv  (A B : Type) : Identity A (bool_rec_type A B true)
hott0 axiom bool_rec_type_false_inv (A B : Type) : Identity B (bool_rec_type A B false)

-- Transport: move a value along a proof that two types are equal.
-- Uses identity recursion with motive (λ T _ => T) to substitute B for A.
hott0 def coe {A B : Type} (h : Identity A B) : A → B :=
  λ a => h.rec (motive := λ T _ => T) a

-- Left injection: tag true, coerce a : A into the true-branch type.
hott0 def inl {A B : Type} (a : A) : Sum A B :=
  ⟨true,  coe (bool_rec_type_true_inv  A B) a⟩ -- A →(coe)→ bool_rec_type A B true

-- Right injection: tag false, coerce b : B into the false-branch type.
hott0 def inr {A B : Type} (b : B) : Sum A B :=
  ⟨false, coe (bool_rec_type_false_inv A B) b⟩ -- B →(coe)→ bool_rec_type A B false

--- NOOOO!!! I can't use my own notation for the elaborator SAAD
--infixr:30 " ⊎ " => Sum

-- Negation: Not A means A implies absurdity (there is no proof of A).
hott0 def Not (A : Type) : Type := A → Empty

-- notation "¬" A => Not A

-- Decidable equality: for any two elements x y : A, we can decide x = y or x ≠ y.
-- A type with this property is called Discrete (Rijke 12.3).
hott0 def Discrete (A : Type) : Type :=
  ∀ (x y : A), Sum (Identity x y) (Not (Identity x y))

-- Helper for the true branch of sum_rec.
-- x lives in bool_rec_type A B true, which is definitionally A (by bool_rec_type_true).
-- We coerce x back to A and then apply f.
hott0 def sum_rec_helper_true
    {A B C : Type}
    (f : A → C)
    (x : bool_rec_type A B true) -- x : bool_rec_type A B true ≡ A (up to Identity)
    : C :=
  f (coe (bool_rec_type_true A B) x) -- coerce x : bool_rec_type A B true → A, then apply f

-- Helper for the false branch of sum_rec.
-- x lives in bool_rec_type A B false, which is definitionally B (by bool_rec_type_false).
-- We coerce x back to B and then apply g.
hott0 def sum_rec_helper_false
    {A B C : Type}
    (f : B → C)
    (x : bool_rec_type A B false) -- x : bool_rec_type A B false ≡ B (up to Identity)
    : C :=
  f (coe (bool_rec_type_false A B) x) -- coerce x : bool_rec_type A B false → B, then apply f

-- Dependent Bool eliminator into a type family C : Bool → Type.
-- Given values at false and true, produce a value at any b : Bool.
-- Axiomatized because the universe level of C (level 1, since Bool → Type lives at level 1)
-- cannot be derived from bool_rec_type using the current universe infrastructure.
hott0 axiom bool_rec_dep
    {C : Bool → Type}  -- the type family to eliminate into
    (c_false : C false) -- value at false
    (c_true  : C true)  -- value at true
    (b : Bool)
    : C b               -- result at any b

-- Non-dependent sum eliminator: given f : A → C and g : B → C, eliminate out of Sum A B.
-- Strategy: use bool_rec_dep with the family (λ b => bool_rec_type A B b → C).
--   - At b = true:  we need bool_rec_type A B true → C, i.e. A → C  (handled by sum_rec_helper_true)
--   - At b = false: we need bool_rec_type A B false → C, i.e. B → C (handled by sum_rec_helper_false)
-- This gives a function (bool_rec_type A B s.fst → C), which we then apply to s.snd.
hott0 def sum_rec
    {A B C : Type}
    (f : A → C) -- what to do with a left element
    (g : B → C) -- what to do with a right element
    : Sum A B → C
:= λ s =>
    (@bool_rec_dep
      (λ b => bool_rec_type A B b → C) -- family: at each tag b, a function from the b-branch to C
      (sum_rec_helper_false g)          -- false branch: coerce to B then apply g
      (sum_rec_helper_true f)           -- true branch:  coerce to A then apply f
      s.fst)                            -- dispatch on the tag of s
    s.snd                               -- apply the resulting function to the payload of s

-- Type-valued sum eliminator: given f : A → Type and g : B → Type,
-- compute the type for each branch of a Sum A B.
-- Axiomatized separately because type-returning functions live at a higher universe
-- level than value-returning ones; see the universe polymorphism note above.
hott0 axiom sum_rec_type
    {A B : Type}
    (f : A → Type) -- type to assign to each element of the left summand
    (g : B → Type) -- type to assign to each element of the right summand
    : Sum A B → Type

-- R' turns a decidability witness into a proposition:
--   if q says "x = y"  → R' = Unit  (inhabited, but only one element)
--   if q says "x ≠ y"  → R' = Empty (uninhabited)
-- Either way R' is a proposition, so it carries no information beyond yes/no.
hott0 def R' (A : Type) (x y : A)
    (q : Sum (Identity x y) (Not (Identity x y)))
    : Type :=
  sum_rec_type (λ _ => Unit) (λ _ => Empty) q -- branch on q: left ↦ Unit, right ↦ Empty

-- R(x, y) applies R' to the output of decidability: dec x y decides x = y or x ≠ y,
-- then R' collapses that choice into a proposition.
hott0 def R (A : Type) (dec : Discrete A) (x y : A) : Type :=
  R' A x y (dec x y) -- feed the decision for this specific x, y into R'

-- R(x, y) is a proposition: it's either Unit (one element) or Empty (no elements),
-- both of which have at most one element.
-- TODO: derive from unit_is_prop and empty_rec instead of axiomatizing.
hott0 axiom R_is_prop
    (A : Type)
    (dec : Discrete A)
    (x y : A)
    : isProp₀ (R A dec x y)

-- R(x, y) → Identity x y: the only way R(x, y) is inhabited is if dec chose "x = y",
-- meaning the original identity proof is recoverable.
-- TODO: derive by case-splitting on dec x y.
hott0 axiom R_to_eq
    (A : Type)
    (dec : Discrete A)
    (x y : A)
    : R A dec x y → Identity x y

-- R(x, x) is always inhabited: dec x x returns "left (refl)" so R(x,x) = Unit,
-- which is inhabited by star.
-- TODO: derive by transporting star along bool_rec_type_true.
hott0 axiom R_refl
    (A : Type)
    (dec : Discrete A)
    (x : A)
    : R A dec x x

-- Identity system theorem (Rijke 12.3.4): if R is reflexive, prop-valued, and implies
-- identity, then A is a set. The idea: since R(x,y) → (x = y) and R is a prop,
-- the identity type (x = y) is sandwiched between two propositions, forcing it to be one.
-- TODO: prove from path induction / encode-decode argument.
hott0 axiom identity_system_to_set
    {A : Type}
    {R : A → A → Type}
    {r : ∀ x, R x x}       -- reflexivity witness (used implicitly in the proof)
    (R_to_id : ∀ x y, R x y → Identity x y) -- R implies equality
    (R_prop : ∀ x y, isProp₀ (R x y))        -- R is a proposition
    : isSet₀ A

-- Hedberg's Theorem: if A has decidable equality then A is a set.
-- We simply supply the relation R built from decidability, together with
-- the three properties verified above.
hott0 def hedberg (A : Type) (dec : Discrete A) : isSet₀ A :=
  @identity_system_to_set A (R A dec) (R_refl A dec) -- the relation and its reflexivity proof
    (R_to_eq A dec)   -- R implies identity
    (R_is_prop A dec) -- R is prop-valued

-- Next up isSection stuff
