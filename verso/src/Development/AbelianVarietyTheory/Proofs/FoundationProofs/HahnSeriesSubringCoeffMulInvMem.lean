import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HahnSub

/- English proof (translation)
Rewrite using `[HahnSeries.coeff_mul]`. Conclude with `A.sum_mem fun ij _ => A.mul_mem (hh ij.1) (hh' ij.2)`.
-/
theorem coeff_mul_mem {Ω : Type} [Field Ω] (A : Subring Ω) (h h' : HahnSeries ℚ Ω)
    (hh : ∀ r, h.coeff r ∈ A) (hh' : ∀ r, h'.coeff r ∈ A) (r : ℚ) : (h * h').coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact A.sum_mem fun ij _ => A.mul_mem (hh ij.1) (hh' ij.2)

/- English proof (translation)
Distinguish the cases in `h0 : h = 0`. Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Set `g : HahnSeries ℚ A` to `{ coeff := fun s => ⟨h.coeff s, hh s⟩ isPWO_support' := h.isPWO_support.mono fun s hs e => hs (Subtype.ext e) }`. Establish `hg : ∀ s, (g.coeff s : Ω) = h.coeff s` using `fun s => rfl`.

Establish `hg0 : g ≠ 0`. Introduce `e`. Apply `h0` to reduce the goal to its premises. Use extensionality with `s`. Rewrite using `[← hg, e]`.

Both sides reduce to the same expression. Establish `hord : g.order = h.order`. Apply `le_antisymm` to reduce the goal to its premises. Apply `HahnSeries.order_le_of_coeff_ne_zero` to reduce the goal to its premises. Introduce `e`.

Apply `HahnSeries.leadingCoeff_ne_zero.2 h0` to reduce the goal to its premises. Rewrite using `[HahnSeries.leadingCoeff_eq, ← hg, e]`. Both sides reduce to the same expression. Apply `HahnSeries.order_le_of_coeff_ne_zero` to reduce the goal to its premises. Rewrite using `[← hg]`.

Introduce `e`. Apply `HahnSeries.leadingCoeff_ne_zero.2 hg0` to reduce the goal to its premises. Rewrite using `[HahnSeries.leadingCoeff_eq]`. Conclude with `Subtype.ext e`. Establish `hlead : (g.leadingCoeff : Ω) = h.leadingCoeff`.

Rewrite using `[HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hg, hord]`. Establish `hunit : IsUnit g.leadingCoeff`. Use `IsUnit.of_mul_eq_one (⟨h.leadingCoeff⁻¹, hl⟩ : A) ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (g.leadingCoeff : Ω) * h.leadingCoeff⁻¹ = 1`.

Rewrite using `[hlead]`. Conclude with `mul_inv_cancel₀ (HahnSeries.leadingCoeff_ne_zero.2 h0)`. Take `⟨v, hv⟩` from `(HahnSeries.isUnit_iff.2 hunit).exists_right_inv`. Set `f : A →ₙ+* Ω` to `A.subtype.toNonUnitalRingHom`. Establish `hgf : g.map f = h`.

Use extensionality with `s`. Both sides reduce to the same expression. Establish `hone : (1 : HahnSeries ℚ A).map f = 1`. Use extensionality with `s`. Rewrite using `[HahnSeries.map_coeff, HahnSeries.coeff_one, HahnSeries.coeff_one]`.

Apply the tactic sequence `split_ifs <;> rfl`. Establish `key : h * v.map f = 1`. Rewrite using `[← hgf, ← HahnSeries.map_mul, hv, hone]`. Rewrite using `[inv_eq_of_mul_eq_one_right key, HahnSeries.map_coeff]`. Conclude with `(v.coeff r).2`.
-/
theorem coeff_inv_mem {Ω : Type} [Field Ω] (A : Subring Ω) (h : HahnSeries ℚ Ω)
    (hh : ∀ r, h.coeff r ∈ A) (hl : h.leadingCoeff⁻¹ ∈ A) (r : ℚ) : (h⁻¹).coeff r ∈ A := by
  by_cases h0 : h = 0
  · subst h0
    simp

  let g : HahnSeries ℚ A :=
    { coeff := fun s => ⟨h.coeff s, hh s⟩
      isPWO_support' := h.isPWO_support.mono fun s hs e => hs (Subtype.ext e) }
  have hg : ∀ s, (g.coeff s : Ω) = h.coeff s := fun s => rfl
  have hg0 : g ≠ 0 := by
    intro e
    apply h0
    ext s
    rw [← hg, e]
    rfl
  have hord : g.order = h.order := by
    apply le_antisymm
    · apply HahnSeries.order_le_of_coeff_ne_zero
      intro e
      apply HahnSeries.leadingCoeff_ne_zero.2 h0
      rw [HahnSeries.leadingCoeff_eq, ← hg, e]
      rfl
    · apply HahnSeries.order_le_of_coeff_ne_zero
      rw [← hg]
      intro e
      apply HahnSeries.leadingCoeff_ne_zero.2 hg0
      rw [HahnSeries.leadingCoeff_eq]
      exact Subtype.ext e
  have hlead : (g.leadingCoeff : Ω) = h.leadingCoeff := by
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hg, hord]
  have hunit : IsUnit g.leadingCoeff := by
    refine IsUnit.of_mul_eq_one (⟨h.leadingCoeff⁻¹, hl⟩ : A) ?_
    apply Subtype.ext
    show (g.leadingCoeff : Ω) * h.leadingCoeff⁻¹ = 1
    rw [hlead]
    exact mul_inv_cancel₀ (HahnSeries.leadingCoeff_ne_zero.2 h0)
  obtain ⟨v, hv⟩ := (HahnSeries.isUnit_iff.2 hunit).exists_right_inv
  let f : A →ₙ+* Ω := A.subtype.toNonUnitalRingHom
  have hgf : g.map f = h := by
    ext s
    rfl
  have hone : (1 : HahnSeries ℚ A).map f = 1 := by
    ext s
    rw [HahnSeries.map_coeff, HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs <;> rfl
  have key : h * v.map f = 1 := by
    rw [← hgf, ← HahnSeries.map_mul, hv, hone]
  rw [inv_eq_of_mul_eq_one_right key, HahnSeries.map_coeff]
  exact (v.coeff r).2

/- English proof (translation)
Introduce `Ω _ A`. Conclude with `⟨fun h h' hh hh' r => coeff_mul_mem A h h' hh hh' r, fun h hh hl r => coeff_inv_mem A h hh hl r⟩`.
-/
theorem coeff_mul_inv_mem : ∀ (Ω : Type) [Field Ω] (A : Subring Ω), (∀ h h' : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → (∀ r, h'.coeff r ∈ A) → ∀ r, (h * h').coeff r ∈ A) ∧ ∀ h : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → h.leadingCoeff⁻¹ ∈ A → ∀ r, (h⁻¹).coeff r ∈ A := by
  intro Ω _ A
  exact ⟨fun h h' hh hh' r => coeff_mul_mem A h h' hh hh' r,
    fun h hh hl r => coeff_inv_mem A h hh hl r⟩

end GlobalTheory.HahnSub
