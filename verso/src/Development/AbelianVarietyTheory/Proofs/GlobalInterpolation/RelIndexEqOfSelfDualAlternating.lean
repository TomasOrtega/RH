import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.DualCount

/- English proof (translation)
Establish `hadd' : ∀ x y z, ω x (y + z) = ω x y + ω x z`. Introduce `x y z`. Rewrite using `[hanti x (y + z), hadd, hanti x y, hanti x z]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsub : ∀ x y z, ω (x - y) z = ω x z - ω y z`.

Introduce `x y z`. Use `hadd (x - y) y z` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hint : ∀ r : ℝ, ((r : ℝ) : UnitAddCircle) = 0 ↔ ∃ n : ℤ, r = n`.

Introduce `r`. Rewrite using `[AddCircle.coe_eq_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩`. Introduce and unpack `⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩`.

Set `φ : H → (Λ₂ →+ UnitAddCircle)` to `fun x => AddMonoidHom.mk' (fun y => ((ω x y : ℝ) : UnitAddCircle)) (by`. Introduce `a b`. Simplify using `only [AddSubgroup.coe_add, hadd', AddCircle.coe_add])`. Establish `hφ : ∀ x : Λ₁, Λ₁.addSubgroupOf Λ₂ ≤ (φ x).ker`. Introduce `x y hy`.

Rewrite using `[AddMonoidHom.mem_ker]`. Conclude with `(hint _).2 ((h₁ x).1 x.2 y (AddSubgroup.mem_addSubgroupOf.1 hy))`. Set `ψ : Λ₁ → (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ →+ UnitAddCircle)` to `fun x => QuotientAddGroup.lift _ (φ x) (hφ x)`. Use `haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩`. Set `χ : Λ₁ → AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) Circle` to `fun x => (AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom (ψ x)`.

Establish `hχ : ∀ a b : Λ₁, χ a = χ b → ((a : H) - b) ∈ Λ₂`. Introduce `a b hab`. Rewrite using `[h₂]`. Introduce `y hy`. Establish `h` using `DFunLike.congr_fun hab (QuotientAddGroup.mk ⟨y, hy⟩)`.

Establish `h' : AddCircle.toCircle (((ω a y : ℝ)) : UnitAddCircle) = AddCircle.toCircle (((ω b y : ℝ)) : UnitAddCircle)` using `h`. Establish `h''` using `AddCircle.injective_toCircle (T := 1) one_ne_zero h'`. Rewrite using `[← hint, hsub, AddCircle.coe_sub, h'', sub_self]`. Use `haveI hG : Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Nat.finite_of_card_ne_zero hfin`. Use `haveI : Fintype (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Fintype.ofFinite _`.

Set `f : (Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁) → AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ℂ` to `fun q => AddChar.circleEquivComplex (χ q.out)`. Establish `hf : Function.Injective f`. Introduce `p q hpq`. Establish `h` using `hχ _ _ (AddChar.circleEquivComplex.injective hpq)`. Rewrite using `[← QuotientAddGroup.out_eq' p, ← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]`.

Conclude with `h`. Establish `hle` using `Nat.card_le_card_of_injective f hf`. Establish `hc : Nat.card (AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ℂ) = Nat.card (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂)`. Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]`. Rewrite `hle` using `[hc]`.

Conclude with `hle`.
-/
theorem relIndex_le_of_selfDual (H : Type) [AddCommGroup H] (ω : H → H → ℝ)
    (Λ₁ Λ₂ : AddSubgroup H) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (hanti : ∀ x y, ω x y = -ω y x)
    (h₁ : ∀ x, x ∈ Λ₁ ↔ ∀ y ∈ Λ₁, ∃ n : ℤ, ω x y = n)
    (h₂ : ∀ x, x ∈ Λ₂ ↔ ∀ y ∈ Λ₂, ∃ n : ℤ, ω x y = n)
    (hfin : Λ₁.relIndex Λ₂ ≠ 0) : Λ₂.relIndex Λ₁ ≤ Λ₁.relIndex Λ₂ := by
  classical
  have hadd' : ∀ x y z, ω x (y + z) = ω x y + ω x z := by
    intro x y z
    rw [hanti x (y + z), hadd, hanti x y, hanti x z]; ring
  have hsub : ∀ x y z, ω (x - y) z = ω x z - ω y z := by
    intro x y z
    have := hadd (x - y) y z
    rw [sub_add_cancel] at this
    linarith
  have hint : ∀ r : ℝ, ((r : ℝ) : UnitAddCircle) = 0 ↔ ∃ n : ℤ, r = n := by
    intro r
    rw [AddCircle.coe_eq_zero_iff]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩
  let φ : H → (Λ₂ →+ UnitAddCircle) := fun x =>
    AddMonoidHom.mk' (fun y => ((ω x y : ℝ) : UnitAddCircle)) (by
      intro a b
      simp only [AddSubgroup.coe_add, hadd', AddCircle.coe_add])
  have hφ : ∀ x : Λ₁, Λ₁.addSubgroupOf Λ₂ ≤ (φ x).ker := by
    intro x y hy
    rw [AddMonoidHom.mem_ker]
    exact (hint _).2 ((h₁ x).1 x.2 y (AddSubgroup.mem_addSubgroupOf.1 hy))
  let ψ : Λ₁ → (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ →+ UnitAddCircle) := fun x =>
    QuotientAddGroup.lift _ (φ x) (hφ x)
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let χ : Λ₁ → AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) Circle := fun x =>
    (AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom (ψ x)
  have hχ : ∀ a b : Λ₁, χ a = χ b → ((a : H) - b) ∈ Λ₂ := by
    intro a b hab
    rw [h₂]
    intro y hy
    have h := DFunLike.congr_fun hab (QuotientAddGroup.mk ⟨y, hy⟩)
    have h' : AddCircle.toCircle (((ω a y : ℝ)) : UnitAddCircle)
        = AddCircle.toCircle (((ω b y : ℝ)) : UnitAddCircle) := h
    have h'' := AddCircle.injective_toCircle (T := 1) one_ne_zero h'
    rw [← hint, hsub, AddCircle.coe_sub, h'', sub_self]
  haveI hG : Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Nat.finite_of_card_ne_zero hfin
  haveI : Fintype (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Fintype.ofFinite _
  let f : (Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁) → AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ℂ := fun q =>
    AddChar.circleEquivComplex (χ q.out)
  have hf : Function.Injective f := by
    intro p q hpq
    have h := hχ _ _ (AddChar.circleEquivComplex.injective hpq)
    rw [← QuotientAddGroup.out_eq' p, ← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_iff_sub_mem,
      AddSubgroup.mem_addSubgroupOf]
    exact h
  have hle := Nat.card_le_card_of_injective f hf
  have hc : Nat.card (AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ℂ)
      = Nat.card (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  rw [hc] at hle
  exact hle

/- English proof (translation)
Introduce `H _ ω Λ₁ Λ₂ hadd hanti h₁ h₂ f₁ f₂`. Conclude with `le_antisymm (relIndex_le_of_selfDual H ω Λ₂ Λ₁ hadd hanti h₂ h₁ f₂) (relIndex_le_of_selfDual H ω Λ₁ Λ₂ hadd hanti h₁ h₂ f₁)`.
-/
theorem relIndex_eq_of_selfDual : ∀ (H : Type) [AddCommGroup H] (ω : H → H → ℝ)
    (Λ₁ Λ₂ : AddSubgroup H), (∀ x y z, ω (x + y) z = ω x z + ω y z) → (∀ x y, ω x y = -ω y x) →
    (∀ x, x ∈ Λ₁ ↔ ∀ y ∈ Λ₁, ∃ n : ℤ, ω x y = n) → (∀ x, x ∈ Λ₂ ↔ ∀ y ∈ Λ₂, ∃ n : ℤ, ω x y = n) →
    Λ₁.relIndex Λ₂ ≠ 0 → Λ₂.relIndex Λ₁ ≠ 0 → Λ₁.relIndex Λ₂ = Λ₂.relIndex Λ₁ := by
  intro H _ ω Λ₁ Λ₂ hadd hanti h₁ h₂ f₁ f₂
  exact le_antisymm (relIndex_le_of_selfDual H ω Λ₂ Λ₁ hadd hanti h₂ h₁ f₂)
    (relIndex_le_of_selfDual H ω Λ₁ Λ₂ hadd hanti h₁ h₂ f₁)

end GlobalTheory.MomT.DualCount
