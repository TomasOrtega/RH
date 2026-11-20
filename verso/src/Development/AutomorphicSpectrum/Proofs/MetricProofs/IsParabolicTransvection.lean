import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.Parab

def IsParabolic {N : ℕ} (ca cb : Fin N) (M : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ a b, b < a → ¬ (a = cb ∧ b = ca) → M a b = 0

/- English proof (translation)
Introduce `a b hba hne`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : c < a ∧ ¬ (a = cb ∧ c = ca)`. Rewrite using `[hA a c h1.1 h1.2, zero_mul]`.

Distinguish the cases in `h2 : b < c ∧ ¬ (c = cb ∧ b = ca)`. Rewrite using `[hB c b h2.1 h2.2, mul_zero]`. It suffices to derive a contradiction. Simplify using `only [Fin.lt_def, Fin.ext_iff] at *`. Use linear arithmetic over natural numbers and integers.
-/
theorem IsParabolic.mul {N : ℕ} {ca cb : Fin N} (hc : (cb : ℕ) = ca + 1)
    {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsParabolic ca cb A) (hB : IsParabolic ca cb B) :
    IsParabolic ca cb (A * B) := by
  intro a b hba hne
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h1 : c < a ∧ ¬ (a = cb ∧ c = ca)
  · rw [hA a c h1.1 h1.2, zero_mul]
  by_cases h2 : b < c ∧ ¬ (c = cb ∧ b = ca)
  · rw [hB c b h2.1 h2.2, mul_zero]
  exfalso
  simp only [Fin.lt_def, Fin.ext_iff] at *
  omega

/- English proof (translation)
Introduce `_ _ h _` and use `hM h`.
-/
theorem isParabolic_of_upper {N : ℕ} (ca cb : Fin N) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : M.BlockTriangular id) : IsParabolic ca cb M := fun _ _ h _ => hM h

/- English proof (translation)
Introduce `a b hba hne`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne hba.ne', Matrix.single_apply_of_ne, add_zero]`. Introduce `h`. Conclude with `hne ⟨h.1.symm, h.2.symm⟩`.
-/
theorem isParabolic_transvection {N : ℕ} (ca cb : Fin N) (t : ℂ) :
    IsParabolic ca cb (1 + Matrix.single cb ca t) := by
  intro a b hba hne
  rw [Matrix.add_apply, Matrix.one_apply_ne hba.ne', Matrix.single_apply_of_ne, add_zero]
  intro h
  exact hne ⟨h.1.symm, h.2.symm⟩

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.add_apply]`. Distinguish the cases in `e : a = cb ∧ b = ca`. Take `⟨rfl, rfl⟩` from `e`. Rewrite using `[Matrix.one_apply_ne hne, Matrix.single_apply_same, zero_add]`.

Establish `hs : Matrix.single cb ca (Y cb ca) a b = 0` using `Matrix.single_apply_of_ne _ _ _ _ _ (fun h => e ⟨h.1.symm, h.2.symm⟩)`. Rewrite using `[hs, add_zero]`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Rewrite using `[hY.2 a b h, Matrix.one_apply_ne h.ne]`. Substitute `h` using the available equality.

Rewrite using `[hY.1 a, Matrix.one_apply_eq]`. Rewrite using `[hP a b h e, Matrix.one_apply_ne h.ne']`.
-/
theorem eq_transvection {N : ℕ} {ca cb : Fin N} {Y : Matrix (Fin N) (Fin N) ℂ} (hne : cb ≠ ca)
    (hlt : ca < cb) (hY : IsLowerUni Y) (hP : IsParabolic ca cb Y) :
    Y = 1 + Matrix.single cb ca (Y cb ca) := by
  ext a b
  rw [Matrix.add_apply]
  by_cases e : a = cb ∧ b = ca
  · obtain ⟨rfl, rfl⟩ := e
    rw [Matrix.one_apply_ne hne, Matrix.single_apply_same, zero_add]
  · have hs : Matrix.single cb ca (Y cb ca) a b = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ (fun h => e ⟨h.1.symm, h.2.symm⟩)
    rw [hs, add_zero]
    rcases lt_trichotomy a b with h | h | h
    · rw [hY.2 a b h, Matrix.one_apply_ne h.ne]
    · subst h
      rw [hY.1 a, Matrix.one_apply_eq]
    · rw [hP a b h e, Matrix.one_apply_ne h.ne']

/- English proof (translation)
Introduce `N h B₀ B₁ ca cb t hc h0 h1 d0 _ L0 L1`. Establish `hlt : ca < cb` using `by simp only [Fin.lt_def]; omega`. Establish `hL0 : IsUnit (h * B₀).det` using `by rw [L0.det]; exact isUnit_one`. Establish `hB0 : IsUnit B₀.det` using `isUnit_iff_ne_zero.mpr d0`. Use `letI := Matrix.invertibleOfIsUnitDet (h * B₀) hL0`.

Use `letI := Matrix.invertibleOfIsUnitDet B₀ hB0`. Use `set E : Matrix (Fin N) (Fin N) ℂ := 1 + Matrix.single cb ca t with hE`. Use `set Y : Matrix (Fin N) (Fin N) ℂ := B₀⁻¹ * (E * B₁) with hYdef`. Establish `hY : h * B₀ * Y = h * E * B₁`. Rewrite using `[hYdef, Matrix.mul_assoc h B₀, Matrix.mul_nonsing_inv_cancel_left _ _ hB0, Matrix.mul_assoc]`.

Establish `low : Y.BlockTriangular OrderDual.toDual`. Establish `e1 : (h * B₀).BlockTriangular OrderDual.toDual` using `fun a b e => L0.2 _ _ e`. Establish `e2 : (h * E * B₁).BlockTriangular OrderDual.toDual` using `fun a b e => L1.2 _ _ e`. Use `(blockTriangular_inv_of_blockTriangular e1).mul e2` as an intermediate fact. Rewrite `this` using `[← hY, Matrix.nonsing_inv_mul_cancel_left _ _ hL0]`. Then use the resulting hypothesis.

Establish `hYl : IsLowerUni Y`. Use `⟨fun a => ?_, fun a b e => low e⟩` and prove the remaining obligations. Use `L1.1 a` as an intermediate fact. Rewrite using `[← hY, Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc' => by`. Break down `lt_or_gt_of_ne hc' with e | e` into its components or cases.

Rewrite using `[low e, mul_zero]`. Rewrite `this` using `[L0.2 a c e, zero_mul]) (by simp), L0.1, one_mul]`. Conclude with `this`. Establish `hP : IsParabolic ca cb Y` using `(isParabolic_of_upper ca cb (blockTriangular_inv_of_blockTriangular h0)).mul hc ((isParabolic_transvection ca cb t).mul hc (isParabolic_of_upper ca cb h1))`. Conclude with `⟨Y cb ca, by rw [← hY, ← eq_transvection hlt.ne' hlt hYl hP]⟩`.
-/
theorem mul_transvection_eq : ∀ (N : ℕ) (h B₀ B₁ : Matrix (Fin N) (Fin N) ℂ) (ca cb : Fin N) (t : ℂ),
    (cb : ℕ) = ca + 1 → B₀.BlockTriangular id → B₁.BlockTriangular id → B₀.det ≠ 0 → B₁.det ≠ 0 →
    IsLowerUni (h * B₀) → IsLowerUni (h * (1 + Matrix.single cb ca t) * B₁) →
    ∃ y : ℂ, h * (1 + Matrix.single cb ca t) * B₁ = h * B₀ * (1 + Matrix.single cb ca y) := by
  intro N h B₀ B₁ ca cb t hc h0 h1 d0 _ L0 L1
  have hlt : ca < cb := by simp only [Fin.lt_def]; omega
  have hL0 : IsUnit (h * B₀).det := by rw [L0.det]; exact isUnit_one
  have hB0 : IsUnit B₀.det := isUnit_iff_ne_zero.mpr d0
  letI := Matrix.invertibleOfIsUnitDet (h * B₀) hL0
  letI := Matrix.invertibleOfIsUnitDet B₀ hB0
  set E : Matrix (Fin N) (Fin N) ℂ := 1 + Matrix.single cb ca t with hE
  set Y : Matrix (Fin N) (Fin N) ℂ := B₀⁻¹ * (E * B₁) with hYdef
  have hY : h * B₀ * Y = h * E * B₁ := by
    rw [hYdef, Matrix.mul_assoc h B₀, Matrix.mul_nonsing_inv_cancel_left _ _ hB0, Matrix.mul_assoc]
  have low : Y.BlockTriangular OrderDual.toDual := by
    have e1 : (h * B₀).BlockTriangular OrderDual.toDual := fun a b e => L0.2 _ _ e
    have e2 : (h * E * B₁).BlockTriangular OrderDual.toDual := fun a b e => L1.2 _ _ e
    have := (blockTriangular_inv_of_blockTriangular e1).mul e2
    rwa [← hY, Matrix.nonsing_inv_mul_cancel_left _ _ hL0] at this
  have hYl : IsLowerUni Y := by
    refine ⟨fun a => ?_, fun a b e => low e⟩
    have := L1.1 a
    rw [← hY, Matrix.mul_apply, Finset.sum_eq_single a
      (fun c _ hc' => by
        rcases lt_or_gt_of_ne hc' with e | e
        · rw [low e, mul_zero]
        · rw [L0.2 a c e, zero_mul]) (by simp), L0.1, one_mul] at this
    exact this
  have hP : IsParabolic ca cb Y :=
    (isParabolic_of_upper ca cb (blockTriangular_inv_of_blockTriangular h0)).mul hc
      ((isParabolic_transvection ca cb t).mul hc (isParabolic_of_upper ca cb h1))
  exact ⟨Y cb ca, by rw [← hY, ← eq_transvection hlt.ne' hlt hYl hP]⟩

end GlobalTheory.CompanionTheory.Ar.PB.Parab
