import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightSubstNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShapeStatement

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DepthCount

variable {C : Type} [Field C]

/- English proof (translation)
Proceed by induction on `d using Finsupp.induction with`. Consider the case `zero => simp`. Consider the case `single_add s n d hs hn ih`. Rewrite using `[Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.prod_single_index (by simp), X_pow_eq, monomial_mul_monomial, one_mul]`.
-/
theorem prod_X_col {i : ℕ} (b : Fin i) (d : Fin i →₀ ℕ) :
    (d.prod fun s e => (X (⟨b, s⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C) ^ e)
      = monomial (Finsupp.mapDomain (Sigma.mk b) d) 1 := by
  induction d using Finsupp.induction with
  | zero => simp
  | single_add s n d hs hn ih =>
    rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), ih, Finsupp.mapDomain_add,
      Finsupp.mapDomain_single, Finsupp.prod_single_index (by simp), X_pow_eq,
      monomial_mul_monomial, one_mul]

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero (fun a => constantCoeff_X _)`.
-/
theorem hasSubst_col {i : ℕ} (b : Fin i) :
    HasSubst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) :=
  hasSubst_of_constantCoeff_zero (fun a => constantCoeff_X _)

/- English proof (translation)
Establish `hs` using `hasSubst_col (C := C) b`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_subst hs]`. Use `finsum_zero with d` and compare the differences between its conclusion and the goal. Rewrite using `[prod_X_col, coeff_monomial, smul_eq_mul]`. Use `split_ifs with h`.

Establish `hd : d = 0`. Establish `h'` using `h.symm`. Rewrite `h'` using `[← Finsupp.mapDomain_zero (f := Sigma.mk b)]`. Conclude with `Finsupp.mapDomain_injective (sigma_mk_injective (i := b)) h'`. Substitute `hd` using the available equality.

Simplify using `[hg]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_col {i : ℕ} (b : Fin i) (g : MvPowerSeries (Fin i) C)
    (hg : constantCoeff g = 0) :
    constantCoeff (subst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) g)
      = 0 := by
  have hs := hasSubst_col (C := C) b
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst hs]
  convert finsum_zero with d
  rw [prod_X_col, coeff_monomial, smul_eq_mul]
  split_ifs with h
  · have hd : d = 0 := by
      have h' := h.symm
      rw [← Finsupp.mapDomain_zero (f := Sigma.mk b)] at h'
      exact Finsupp.mapDomain_injective (sigma_mk_injective (i := b)) h'
    subst hd
    simp [hg]
  · simp

/- English proof (translation)
Establish `hs` using `hasSubst_col (C := C) b`. Rewrite using `[coeff_subst hs, finsum_eq_sum _ (coeff_subst_finite hs g β)]`. Apply `v.map_le_sum` to reduce the goal to its premises. Introduce `d _`. Rewrite using `[prod_X_col, coeff_monomial, smul_eq_mul]`.

Use `split_ifs with h`. Rewrite using `[mul_one]`. Substitute `h` using the available equality. Rewrite using `[Finsupp.sum_mapDomain_index (by simp) (by intros; push_cast; ring), Finsupp.sum_fintype _ _ (by simp)]`. Conclude with `hg d`.

Simplify using the standard rewrite rules.
-/
theorem wt_col {i : ℕ} (v : AddValuation C (WithTop ℝ)) (ρ : Fin i → ℝ) (b : Fin i)
    (g : MvPowerSeries (Fin i) C) (hg : OrdGe v ρ g 0) (β : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    (((0 - β.sum (fun y e => ρ y.2 * (e : ℝ)) : ℝ)) : WithTop ℝ) ≤
      v (coeff β (subst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) g)) := by
  have hs := hasSubst_col (C := C) b
  rw [coeff_subst hs, finsum_eq_sum _ (coeff_subst_finite hs g β)]
  apply v.map_le_sum
  intro d _
  rw [prod_X_col, coeff_monomial, smul_eq_mul]
  split_ifs with h
  · rw [mul_one]
    subst h
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; push_cast; ring),
      Finsupp.sum_fintype _ _ (by simp)]
    exact hg d
  · simp

/- English proof (translation)
Introduce `C _ _ v i d c ρ t B ht0 ht hP f hf`. Establish `hw` using `GlobalTheory.WeightSubst.weight_subst_nonneg C v (Σ _ : Fin i, Fin i) (Σ _ : Fin i, Fin d) (fun y => ρ y.2) f (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) hf (fun x => constantCoeff_col x.1 _ (ht0 x.2)) (fu …`. Unfold `derivAt0`. Apply `v.map_le_sum` to reduce the goal to its premises. Introduce `α hα`.

Establish `hrow` using `((GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c).2.2.2 α hα).1`. Rewrite using `[v.map_mul]`. Establish `e : B = (B + c * ∑ a, ρ a) + (0 - α.sum (fun y e => ρ y.2 * (e : ℝ)))`. Rewrite using `[Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.mul_sum]`.

Establish `hc : ∀ a : Fin i, (∑ b : Fin i, ((α ⟨b, a⟩ : ℕ) : ℝ)) = c` using `fun a => by`. Conclude with `hrow a` after adjusting the coercions. Repeatedly rewrite using `[hc]`. Rewrite using `[← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, WithTop.coe_add]`. Conclude with `add_le_add (hP α hα) (hw α)`.
-/
theorem depth_count : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (ρ : Fin i → ℝ) (t : Fin d → MvPowerSeries (Fin i) C) (B : ℝ), (∀ a, constantCoeff (t a) = 0) → (∀ a, OrdGe v ρ (t a) 0) → (∀ α ∈ (detPow C i c).support, (((B + c * ∑ a, ρ a : ℝ)) : WithTop ℝ) ≤ v ((detPow C i c).coeff α * mfact α)) → ∀ f : MvPowerSeries (Σ _ : Fin i, Fin d) C, MvIsInt v f → ((B : ℝ) : WithTop ℝ) ≤ v (derivAt0 (detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) f)) := by
  intro C _ _ v i d c ρ t B ht0 ht hP f hf
  have hw := GlobalTheory.WeightSubst.weight_subst_nonneg C v (Σ _ : Fin i, Fin i) (Σ _ : Fin i, Fin d)
    (fun y => ρ y.2) f
    (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i =>
      (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) hf
    (fun x => constantCoeff_col x.1 _ (ht0 x.2)) (fun x => wt_col v ρ x.1 _ (ht x.2))
  unfold derivAt0
  apply v.map_le_sum
  intro α hα
  have hrow := ((GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c).2.2.2 α hα).1
  rw [v.map_mul]
  have e : B = (B + c * ∑ a, ρ a) + (0 - α.sum (fun y e => ρ y.2 * (e : ℝ))) := by
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hc : ∀ a : Fin i, (∑ b : Fin i, ((α ⟨b, a⟩ : ℕ) : ℝ)) = c := fun a => by
      exact_mod_cast hrow a
    simp_rw [hc]
    rw [← Finset.sum_mul]
    ring
  rw [e, WithTop.coe_add]
  exact add_le_add (hP α hα) (hw α)

end GlobalTheory.DepthCount
