import HoTTLean.Frontend.Commands

set_option profiler true

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

--Adding Is Contractible over here
hott0 def isContr₀ (A : Type) : Type := Σ (a : A), (∀ (b : A), Identity a b)

hott0
  /-- The type `A` is (-1)-truncated. -/
  def isProp₀ (A : Type) : Type :=
    ∀ (a a' : A), Identity a a'

hott0
  /-- The type `A` is 0-truncated. -/
  def isSet₀ (A : Type) : Type :=
    ∀ (a b : A), isProp₀ (Identity a b)

hott0
  /-- The univalence axiom for sets. See HoTT book, Axiom 2.10.3. -/
  axiom setUv₀₀ {A B : Type} (A_set : isSet₀ A) (B_set : isSet₀ B) :
    isEquiv₁₀ (@Identity.toEquiv₀₀ A B)


-- Functions preserve paths
hott0 def ap {A B : Type} (f : A → B) {a a' : A} (p : Identity a a') : Identity (f a) (f a') :=
  p.rec (Identity.rfl₀)

-- Binary functions preserve paths in both arguments
hott0 def ap₂ {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
    (p : Identity a a') (q : Identity b b') : Identity (f a b) (f a' b') :=
  p.rec (ap (f a) q)

-- =======================================
-- Sigma (dependent pair) type lemmas
-- =======================================

-- Eta expansion: every pair w is equal to the pair rebuilt from its components.
-- w.1 is the first component, w.2 is the second.
-- This is trivially true by reflexivity — ⟨w.1, w.2⟩ is just notation for w.
hott0 def Sigma.eta {A : Type} {B : A → Type} (w : Σ (a : A), B a) :
    Identity w ⟨w.1, w.2⟩ := Identity.rfl₀

-- Sigma.eq: to prove two dependent pairs equal, it suffices to prove
-- (1) their first components are equal: p : Identity w.1 w'.1
-- (2) their second components are equal *after transporting along p*:
--     q : Identity (p.rec w.2) w'.2
--
-- Why transport? Because w.2 and w'.2 live in different types
-- (B(w.1) and B(w'.1) respectively), so you can't compare them directly.
-- You first move w.2 along p into B(w'.1), then compare.
--
-- Proof structure: two nested identity recursions.
-- Outer: induct on p : w.1 = w'.1, reducing to the case w.1 = w'.1 = x.
-- Inner: induct on q : w.2 = w'.2 (now in the same type B(w.1)), giving refl.
hott0 def Sigma.eq {A : Type} {B : A → Type} {w w' : Σ (a : A), B a}
    (p : Identity w.1 w'.1)            -- first components are equal
    (q : Identity (p.rec w.2) w'.2)    -- second components are equal after transport
    : Identity w w' :=
  @Identity.rec
    A
    w.1
    -- motive: for any x equal to w.1, and any b' in B(x), if transporting w.2 gives b',
    -- then the pair ⟨w.1, w.2⟩ equals ⟨x, b'⟩
    (fun x p' => ∀ (b' : B x), Identity (p'.rec w.2) b' → Identity w ⟨x, b'⟩)
    -- base case: x = w.1, p' = refl, so transport is trivial; now induct on q
    (fun b' q' =>
      @Identity.rec
        (B w.1)
        w.2
        (fun b'' q'' => Identity w ⟨w.1, b''⟩) -- motive: w = ⟨w.1, b''⟩
        Identity.rfl₀                            -- base case: b'' = w.2, so w = ⟨w.1, w.2⟩ = w
        b'
        q')
    w'.1
    p   -- apply outer recursion to the path p : w.1 = w'.1
    w'.2
    q   -- apply inner recursion to the path q

-- Same as Sigma.eq but for the case where the first component lives in Type 1
-- (a higher universe). The only difference is rfl₁ instead of rfl₀.
hott0 def Sigma.eq₁ {A : Type 1} {B : A → Type} {w w' : Σ (a : A), B a}
    (p : Identity w.1 w'.1)
    (q : Identity (p.rec w.2) w'.2)
    : Identity w w' :=
  @Identity.rec
    A
    w.1
    (fun x p' => ∀ (b' : B x), Identity (p'.rec w.2) b' → Identity w ⟨x, b'⟩)
    (fun b' q' =>
      @Identity.rec
        (B w.1)
        w.2
        (fun b'' q'' => Identity w ⟨w.1, b''⟩)
        Identity.rfl₁  -- rfl₁ because A : Type 1 here
        b'
        q')
    w'.1
    p
    w'.2
    q

-- =======================================
-- Function extensionality
-- =======================================

-- funext₀: two functions are equal if they agree at every input.
-- This is *not* provable from the basic rules of type theory alone —
-- it must be assumed as an axiom (funext₀₀, declared above).
-- Here we just extract the forward direction from the equivalence funext₀₀ provides.
-- h : for every a, f(a) = g(a)   →   Identity f g
hott0 def funext₀ {A : Type} {B : A → Type} {f g : (a : A) → B a}
    (h : ∀ (a : A), Identity (f a) (g a)) : Identity f g :=
  (funext₀₀ f g).1 h -- .1 extracts the forward map of the equivalence

-- =======================================
-- Transport on binary operations
-- =======================================

-- transport_op: describes how a binary operation transforms when transported
-- along a path between types induced by an equivalence.
--
-- Setup: A and B are sets, f : A → B is an equivalence with inverse e.1 : B → A.
-- op : A → A → A is a binary operation on A.
-- The univalence axiom (setUv₀₀) gives a path p : Identity A B from f and e.
-- Transporting op along p gives an operation on B.
--
-- This axiom says the transported operation computes as:
--   transported_op(b₁, b₂) = f(op(f⁻¹(b₁), f⁻¹(b₂)))
-- i.e. pull back to A, apply op, push forward to B.
hott0
  axiom transport_op {A B : Type}
      (A_set : isSet₀ A) (B_set : isSet₀ B)
      (f : A → B) (e : isEquiv₀₀ f)
      (op : A → A → A) (b₁ b₂ : B) :
    Identity
      -- left side: op transported along the univalence path, applied to b₁ b₂
      (@Identity.rec Type A (fun X _ => X → X → X) op B ((setUv₀₀ A_set B_set).1 ⟨f, e⟩) b₁ b₂)
      -- right side: pull back via e.1 (= f⁻¹), apply op, push forward via f
      (f (op (e.1 b₁) (e.1 b₂)))

-- =======================================
-- Magma: the simplest algebraic structure
-- =======================================

-- A magma is just a type together with a binary operation.
-- No axioms (no associativity, no unit, no commutativity — just a set and an operation).
-- Represented as a dependent pair: (carrier type, binary operation on it).
hott0 def magma := Σ (A : Type), A → (A → A)

-- magma.carrier: extract the underlying type (the "set of elements").
hott0 def magma.carrier (M : magma) : Type := M.1

-- magma.op: extract the binary operation.
hott0 def magma.op (M : magma) : M.carrier → M.carrier → M.carrier := M.2

-- A magma homomorphism (commented out — not needed for the main theorem):
-- a function between carriers that preserves the operation.
-- hott0 def magma_hom (M N : magma) : Type :=
--   Σ (f : M.carrier → N.carrier),
--     ∀ (x y : M.carrier), Identity (f (M.op x y)) (N.op (f x) (f y))

/-

Main theorem: equivalent set-magmas are equal.
----------------------------------------------
A "set-magma" is a magma (A, m) where the carrier A is a set (0-truncated).

Two set-magmas M = (A, m) and N = (B, n) are equal as magmas if:
- There is an equivalence f : A ≃ B  (a bijection with homotopy-inverse)
- f is a magma homomorphism: f(m(x,y)) = n(f(x), f(y)) for all x y : A

Proof sketch (5 steps):

Step 1: Carriers are equal.
  The equivalence f : A ≃ B, combined with the set-univalence axiom (setUv₀₀),
  gives a path p : Identity A B.  (Univalence: equivalences are the same as equalities.)

Step 2: Transport the operation.
  Using p, transport M's operation m : A→A→A across to get an operation on B:
    transported_op : B → B → B
    defined as  Identity.rec (motive X ↦ X→X→X) m  applied to p.

Step 3: Show transported_op = N.op pointwise.
  For any x y : B:
    transported_op(x, y)
      = f(m(f⁻¹(x), f⁻¹(y)))   -- by transport_op axiom
      = n(f(f⁻¹(x)), f(f⁻¹(y))) -- by homomorphism property of f
      = n(x, y)                  -- by retraction: f(f⁻¹(b)) = b, applied to x and y

Step 4: Operations are equal as functions.
  Apply funext₀ twice (once per argument) to the pointwise equality from Step 3
  to get  Identity transported_op N.op.

Step 5: Combine into equality of pairs.
  Use Sigma.eq₁ with:
  - the path between carriers from Step 1
  - the path between operations from Step 4  (after transporting along the carrier path)
  to conclude Identity M N.

-/

-- Structure-preserving equivalence between magmas
hott0 def magma_equiv (M N : magma) : Type :=
  Σ (f : M.carrier → N.carrier),       -- the map
    Σ (e : isEquiv₀₀ f),               -- equivalence
      ∀ (x y : M.carrier),
        Identity (f (M.op x y)) (N.op (f x) (f y))

-- Identity is an equivalence
hott0 def id_is_equiv {A : Type} : isEquiv₀₀ (fun (a : A) => a) :=
  ⟨fun a => a,
   fun a => a,
   fun _ => Identity.rfl₀,
   fun _ => Identity.rfl₀⟩

-- M = N → M ≃ N as magmas
hott0 def magma_equiv_of_eq
    (M N : magma)
    (p : Identity M N)
    : magma_equiv M N :=
  p.rec ⟨fun a => a, id_is_equiv, fun _ _ => Identity.rfl₀⟩

-- f(f⁻¹(b)) = b for set-magmas
hott0
  axiom equiv_retraction {A B : Type}
      (A_set : isSet₀ A) (B_set : isSet₀ B)
      (f : A → B) (e : isEquiv₀₀ f) (b : B) :
    Identity (f (e.1 b)) b

set_option maxHeartbeats 500000000

-- Step 1: Extract carrier equality from equivalence via set univalence
hott0 def magma_carrier_eq
    (M N : magma)
    (M_set : isSet₀ M.carrier)
    (N_set : isSet₀ N.carrier)
    (e : magma_equiv M N)
    : Identity M.carrier N.carrier :=
  (setUv₀₀ M_set N_set).1 ⟨e.1, e.2.1⟩

-- Step 2: Transport M's operation to N.carrier via carrier equality
hott0 def transported_op
    (M N : magma)
    (M_set : isSet₀ M.carrier)
    (N_set : isSet₀ N.carrier)
    (e : magma_equiv M N)
    : N.carrier → N.carrier → N.carrier :=
  @Identity.rec Type M.carrier
    (fun X _ => X → X → X)
    M.op
    N.carrier
    ((setUv₀₀ M_set N_set).1 ⟨e.1, e.2.1⟩)

set_option diagnostics true

-- Step 3a: Pointwise equality chain (deferred due to performance)
hott0 def subexpr
    (M N : magma)
    (M_set : isSet₀ M.carrier)
    (N_set : isSet₀ N.carrier)
    (e : magma_equiv M N)
    (x y : N.carrier)
    :=
    sorry

-- Step 3: Transported operation equals N's operation pointwise
hott0 def magma_op_eq_pointwise
    (M N : magma)
    (M_set : isSet₀ M.carrier)
    (N_set : isSet₀ N.carrier)
    (e : magma_equiv M N)
    (x y : N.carrier)
    : Identity (transported_op M N M_set N_set e x y) (N.op x y) :=
      sorry

-- Step 4: Operations equal as functions via function extensionality
hott0 def magma_op_eq
    (M N : magma)
    (M_set : isSet₀ M.carrier)
    (N_set : isSet₀ N.carrier)
    (e : magma_equiv M N)
    : Identity (transported_op M N M_set N_set e) N.op :=
  funext₀ (fun x =>
    funext₀ (fun y =>
      magma_op_eq_pointwise M N M_set N_set e x y))

-- Step 5: Combine carrier and operation equalities into magma equality
hott0 def magma_eq_of_equiv
    (M N : magma)
    (M_set : isSet₀ M.carrier)
    (N_set : isSet₀ N.carrier)
    (e : magma_equiv M N)
    : Identity M N :=
  Sigma.eq₁
    (magma_carrier_eq M N M_set N_set e)
    (magma_op_eq M N M_set N_set e)
