import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open MulAction

/- English proof (translation)
Use `Fintype.ofFinite α` as an intermediate fact. Simplify using `only [Nat.card_eq_fintype_card, Fintype.card_subtype]`. Rewrite using `[Finset.card_eq_sum_card_fiberwise (f := f) (t := t) (fun a ha => (hP a).1 (Finset.mem_filter.1 ha).2)]`. Use `Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Use `congr 1`.

Use extensionality with `a`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `⟨And.right, fun h => ⟨(hP a).2 (h ▸ hb), h⟩⟩`.
-/
theorem natCard_subtype_eq_sum_natCard_fiber {α β : Type*} [Finite α] [DecidableEq β] (f : α → β)
    (t : Finset β) (P : α → Prop) (hP : ∀ a, P a ↔ f a ∈ t) :
    Nat.card {a // P a} = ∑ b ∈ t, Nat.card {a // f a = b} := by
  classical
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := t)
    (fun a ha => (hP a).1 (Finset.mem_filter.1 ha).2)]
  refine Finset.sum_congr rfl fun b hb => ?_
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨And.right, fun h => ⟨(hP a).2 (h ▸ hb), h⟩⟩

variable {Γ : Type*} [Group Γ]

/- English proof (translation)
Establish `hP : ∀ y : Γ, y⁻¹ * x * y ∈ D ↔ (Subgroup.groupEquivQuotientProdSubgroup (s` using `D) y).1 ∈ fixedBy (Γ ⧸ D) x := by`. Introduce `y`. Express the relevant statement in the definitionally equal form `_ ↔ x • (y : Γ ⧸ D) = y`. Rewrite using `[MulAction.Quotient.smul_mk, eq_comm, QuotientGroup.eq, smul_eq_mul, ← mul_assoc]`. Set `e : {y : Γ // y⁻¹ * x * y ∈ D} ≃ fixedBy (Γ ⧸ D) x × D` to `(Subgroup.groupEquivQuotientProdSubgroup.subtypeEquiv hP).trans (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun q => q ∈ fixedBy (Γ ⧸ D) x))`.

Rewrite using `[Nat.card_congr e, Nat.card_prod, mul_comm]`.
-/
theorem card_mul_card_fixedBy_quotient [Finite Γ] (D : Subgroup Γ) (x : Γ) :
    Nat.card D * Nat.card (fixedBy (Γ ⧸ D) x) = Nat.card {y : Γ // y⁻¹ * x * y ∈ D} := by
  have hP : ∀ y : Γ, y⁻¹ * x * y ∈ D ↔
      (Subgroup.groupEquivQuotientProdSubgroup (s := D) y).1 ∈ fixedBy (Γ ⧸ D) x := by
    intro y
    change _ ↔ x • (y : Γ ⧸ D) = y
    rw [MulAction.Quotient.smul_mk, eq_comm, QuotientGroup.eq, smul_eq_mul, ← mul_assoc]
  let e : {y : Γ // y⁻¹ * x * y ∈ D} ≃ fixedBy (Γ ⧸ D) x × D :=
    (Subgroup.groupEquivQuotientProdSubgroup.subtypeEquiv hP).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun q => q ∈ fixedBy (Γ ⧸ D) x))
  rw [Nat.card_congr e, Nat.card_prod, mul_comm]

/- English proof (translation)
Use `Fintype.ofFinite (Subgroup Γ)` as an intermediate fact. Set `π : Subgroup Γ → Γ → ℤ` to `fun D x => Nat.card (fixedBy (Γ ⧸ D) x)`. Set `f : Subgroup Γ → Γ → ℤ` to `fun C x => Nat.card {y : Γ // Subgroup.zpowers (y⁻¹ * x * y) = C}`. Set `V : Submodule ℤ (Γ → ℤ)` to `Submodule.span ℤ (Set.range fun D : {D : Subgroup Γ // IsCyclic D} => π D)`. Establish `hrec : ∀ (C : Subgroup Γ) (x : Γ), (Nat.card C : ℤ) * π C x = ∑ D ∈ Finset.univ.filter (· ≤ C), f D x`.

Introduce `C x`. Simplify using `only [π, f]`. Rewrite using `[← Nat.cast_mul, card_mul_card_fixedBy_quotient, natCard_subtype_eq_sum_natCard_fiber (fun y => Subgroup.zpowers (y⁻¹ * x * y)) (Finset.univ.filter (· ≤ C)) _ (fun y => by simp [Subgroup.zpowers_le])]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `htot : ∀ x : Γ, (Nat.card Γ : ℤ) = ∑ C, f C x`. Introduce `x`. Establish `h` using `natCard_subtype_eq_sum_natCard_fiber (fun y : Γ => Subgroup.zpowers (y⁻¹ * x * y)) Finset.univ (fun _ => True) (by simp)`. Rewrite `h` using `[Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))]`. Simplify using `only [f]`.

Conclude with `h` after adjusting the coercions. Establish `hcyc : ∀ C : Subgroup Γ, ¬ IsCyclic C → f C = 0`. Introduce `C hC`. Use function extensionality and compare the values at `x`. Simplify using `only [f, Pi.zero_apply, Nat.cast_eq_zero]`.

Rewrite using `[Nat.card_eq_zero]`. Use `left`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Conclude with `hC (hy ▸ inferInstance)`.

Establish `hmem : ∀ C, f C ∈ V`. Introduce `C`. Use `WellFounded.induction (C := fun C => f C ∈ V) wellFounded_lt C ?_` and prove the remaining obligations. Introduce `C ih`. Distinguish the cases in `hC : IsCyclic C`.

Establish `hsplit : Finset.univ.filter (· ≤ C) = insert C (Finset.univ.filter (· < C))`. Use extensionality with `D`. Simplify using `[le_iff_eq_or_lt]`. Establish `hnot : C ∉ Finset.univ.filter (· < C)` using `by simp`. Establish `heq : f C = (Nat.card C : ℤ) • π C - ∑ D ∈ Finset.univ.filter (· < C), f D`.

Use function extensionality and compare the values at `x`. Establish `h` using `hrec C x`. Rewrite `h` using `[hsplit, Finset.sum_insert hnot]`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[heq]`. Conclude with `V.sub_mem (V.smul_mem _ (Submodule.subset_span ⟨⟨C, hC⟩, rfl⟩)) (V.sum_mem fun D hD => ih D (Finset.mem_filter.1 hD).2)`. Rewrite using `[hcyc C hC]`. Conclude with `V.zero_mem`. Establish `hconst : (fun _ : Γ => (Nat.card Γ : ℤ)) ∈ V`.

Establish `h : (fun _ : Γ => (Nat.card Γ : ℤ)) = ∑ C, f C`. Use function extensionality and compare the values at `x`. Rewrite using `[Finset.sum_apply]`. Conclude with `htot x`. Rewrite using `[h]`.

Conclude with `V.sum_mem fun C _ => hmem C`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hconst`. Use `⟨Finset.univ.filter (fun D => IsCyclic D), fun D => if h : IsCyclic D then c ⟨D, h⟩ else 0, fun D hD => (Finset.mem_filter.1 hD).2, fun x => ?_⟩` and prove the remaining obligations. Establish `h` using `congrFun hc x`. Rewrite `h` using `[Finset.sum_apply]`.

Rewrite using `[← h, Finset.sum_subtype (Finset.univ.filter (fun D => IsCyclic D)) (p := fun D : Subgroup Γ => IsCyclic D) (by simp)]`. Use `Finset.sum_congr rfl fun D _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Use `show c D * π D x = (if h : IsCyclic (D : Subgroup Γ) then c ⟨D, h⟩ else 0) * π D x`. Rewrite using `[dif_pos D.2]`.
-/
theorem exists_artin_relation [Finite Γ] :
    ∃ (s : Finset (Subgroup Γ)) (c : Subgroup Γ → ℤ), (∀ D ∈ s, IsCyclic D) ∧
      ∀ x : Γ, (Nat.card Γ : ℤ) = ∑ D ∈ s, c D * Nat.card (fixedBy (Γ ⧸ D) x) := by
  classical
  have := Fintype.ofFinite (Subgroup Γ)
  let π : Subgroup Γ → Γ → ℤ := fun D x => Nat.card (fixedBy (Γ ⧸ D) x)
  let f : Subgroup Γ → Γ → ℤ := fun C x => Nat.card {y : Γ // Subgroup.zpowers (y⁻¹ * x * y) = C}
  let V : Submodule ℤ (Γ → ℤ) :=
    Submodule.span ℤ (Set.range fun D : {D : Subgroup Γ // IsCyclic D} => π D)
  have hrec : ∀ (C : Subgroup Γ) (x : Γ),
      (Nat.card C : ℤ) * π C x = ∑ D ∈ Finset.univ.filter (· ≤ C), f D x := by
    intro C x
    simp only [π, f]
    rw [← Nat.cast_mul, card_mul_card_fixedBy_quotient,
      natCard_subtype_eq_sum_natCard_fiber (fun y => Subgroup.zpowers (y⁻¹ * x * y))
        (Finset.univ.filter (· ≤ C)) _ (fun y => by simp [Subgroup.zpowers_le])]
    push_cast
    rfl
  have htot : ∀ x : Γ, (Nat.card Γ : ℤ) = ∑ C, f C x := by
    intro x
    have h := natCard_subtype_eq_sum_natCard_fiber (fun y : Γ => Subgroup.zpowers (y⁻¹ * x * y))
      Finset.univ (fun _ => True) (by simp)
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))] at h
    simp only [f]
    exact_mod_cast h
  have hcyc : ∀ C : Subgroup Γ, ¬ IsCyclic C → f C = 0 := by
    intro C hC
    funext x
    simp only [f, Pi.zero_apply, Nat.cast_eq_zero]
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨y, hy⟩
    exact hC (hy ▸ inferInstance)
  have hmem : ∀ C, f C ∈ V := by
    intro C
    refine WellFounded.induction (C := fun C => f C ∈ V) wellFounded_lt C ?_
    intro C ih
    by_cases hC : IsCyclic C
    · have hsplit : Finset.univ.filter (· ≤ C) = insert C (Finset.univ.filter (· < C)) := by
        ext D
        simp [le_iff_eq_or_lt]
      have hnot : C ∉ Finset.univ.filter (· < C) := by simp
      have heq : f C = (Nat.card C : ℤ) • π C - ∑ D ∈ Finset.univ.filter (· < C), f D := by
        funext x
        have h := hrec C x
        rw [hsplit, Finset.sum_insert hnot] at h
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
        linarith
      rw [heq]
      exact V.sub_mem (V.smul_mem _ (Submodule.subset_span ⟨⟨C, hC⟩, rfl⟩))
        (V.sum_mem fun D hD => ih D (Finset.mem_filter.1 hD).2)
    · rw [hcyc C hC]
      exact V.zero_mem
  have hconst : (fun _ : Γ => (Nat.card Γ : ℤ)) ∈ V := by
    have h : (fun _ : Γ => (Nat.card Γ : ℤ)) = ∑ C, f C := by
      funext x
      rw [Finset.sum_apply]
      exact htot x
    rw [h]
    exact V.sum_mem fun C _ => hmem C
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hconst
  refine ⟨Finset.univ.filter (fun D => IsCyclic D), fun D => if h : IsCyclic D then c ⟨D, h⟩ else 0,
    fun D hD => (Finset.mem_filter.1 hD).2, fun x => ?_⟩
  have h := congrFun hc x
  rw [Finset.sum_apply] at h
  rw [← h, Finset.sum_subtype (Finset.univ.filter (fun D => IsCyclic D))
    (p := fun D : Subgroup Γ => IsCyclic D) (by simp)]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  show c D * π D x = (if h : IsCyclic (D : Subgroup Γ) then c ⟨D, h⟩ else 0) * π D x
  rw [dif_pos D.2]

end GroundTheory.ProfCoh
