import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoordsNoHomogeneousRelationGenericHyperplaStatement

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares

/- English proof (translation)
Use `set f : (Fin N → ℂ) → ℝ := fun ζ => ∑ i, ‖∑ j, t (i, j) * ζ j‖ ^ 2 with hf`. Use `set g : (Fin N → ℂ) → ℝ := fun ζ => ∑ k, ‖ζ k‖ ^ 2 with hg`. Establish `hfc : Continuous f` using `by simp only [hf]; fun_prop`. Establish `hgc : Continuous g` using `by simp only [hg]; fun_prop`. Establish `hS : IsCompact (Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z)` using `(isCompact_sphere _ _).inter_right hZ`.

Establish `hfnn : ∀ ζ, 0 ≤ f ζ` using `fun ζ => Finset.sum_nonneg fun i _ => by positivity`. Establish `hpos : ∀ ζ ∈ Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z, 0 < f ζ`. Introduce and unpack `ζ ⟨h1, h2⟩`. Use `lt_of_le_of_ne (hfnn ζ) fun h => ?_` and prove the remaining obligations. Establish `h3` using `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h.symm`.

Establish `h4 : ζ = 0` using `h0 ζ h2 fun i => by simpa using h3 i (Finset.mem_univ i)`. Simplify using `[h4] at h1`. Take `⟨C, hC⟩` from `hS.bddAbove_image (f := fun ζ => g ζ / f ζ) (hgc.continuousOn.div hfc.continuousOn fun ζ hζ => (hpos ζ hζ).ne')`. Use `⟨C, fun ζ hζ => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hz : ζ = 0`.

Simplify using `[hz]`. Establish `hn : 0 < ‖ζ‖` using `norm_pos_iff.2 hz`. Use `set c : ℂ := ((‖ζ‖⁻¹ : ℝ) : ℂ) with hcdef`. Establish `hcn : ‖c‖ = ‖ζ‖⁻¹` using `by simp [hcdef]`. Establish `hmem : c • ζ ∈ Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z` using `⟨by rw [mem_sphere_zero_iff_norm, norm_smul, hcn, inv_mul_cancel₀ hn.ne'], hc c ζ hζ⟩`.

Establish `h1 : g (c • ζ) ≤ C * f (c • ζ)` using `(div_le_iff₀ (hpos _ hmem)).1 (hC ⟨_, hmem, rfl⟩)`. Establish `h2 : g (c • ζ) = ‖c‖ ^ 2 * g ζ`. Simplify using `only [hg, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]`. Establish `h3 : f (c • ζ) = ‖c‖ ^ 2 * f ζ`. Simplify using `only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow, ← norm_mul, Finset.mul_sum]`. Use `congr 2`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Establish `h4 : 0 < ‖c‖ ^ 2` using `by rw [hcn]; positivity`.

Rewrite `h1` using `[h2, h3, mul_left_comm]`. Conclude with `le_of_mul_le_mul_left h1 h4`.
-/
theorem cone_sum_sq_le {m N : ℕ} (t : Fin m × Fin N → ℂ) (Z : Set (Fin N → ℂ)) (hZ : IsClosed Z)
    (hc : ∀ (c : ℂ), ∀ ζ ∈ Z, c • ζ ∈ Z) (h0 : ∀ ζ ∈ Z, (∀ i, ∑ j, t (i, j) * ζ j = 0) → ζ = 0) :
    ∃ C : ℝ, ∀ ζ ∈ Z, ∑ k, ‖ζ k‖ ^ 2 ≤ C * ∑ i, ‖∑ j, t (i, j) * ζ j‖ ^ 2 := by
  set f : (Fin N → ℂ) → ℝ := fun ζ => ∑ i, ‖∑ j, t (i, j) * ζ j‖ ^ 2 with hf
  set g : (Fin N → ℂ) → ℝ := fun ζ => ∑ k, ‖ζ k‖ ^ 2 with hg
  have hfc : Continuous f := by simp only [hf]; fun_prop
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hS : IsCompact (Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z) := (isCompact_sphere _ _).inter_right hZ
  have hfnn : ∀ ζ, 0 ≤ f ζ := fun ζ => Finset.sum_nonneg fun i _ => by positivity
  have hpos : ∀ ζ ∈ Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z, 0 < f ζ := by
    rintro ζ ⟨h1, h2⟩
    refine lt_of_le_of_ne (hfnn ζ) fun h => ?_
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h.symm
    have h4 : ζ = 0 := h0 ζ h2 fun i => by simpa using h3 i (Finset.mem_univ i)
    simp [h4] at h1
  obtain ⟨C, hC⟩ := hS.bddAbove_image (f := fun ζ => g ζ / f ζ)
    (hgc.continuousOn.div hfc.continuousOn fun ζ hζ => (hpos ζ hζ).ne')
  refine ⟨C, fun ζ hζ => ?_⟩
  by_cases hz : ζ = 0
  · simp [hz]
  have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hz
  set c : ℂ := ((‖ζ‖⁻¹ : ℝ) : ℂ) with hcdef
  have hcn : ‖c‖ = ‖ζ‖⁻¹ := by simp [hcdef]
  have hmem : c • ζ ∈ Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z :=
    ⟨by rw [mem_sphere_zero_iff_norm, norm_smul, hcn, inv_mul_cancel₀ hn.ne'], hc c ζ hζ⟩
  have h1 : g (c • ζ) ≤ C * f (c • ζ) := (div_le_iff₀ (hpos _ hmem)).1 (hC ⟨_, hmem, rfl⟩)
  have h2 : g (c • ζ) = ‖c‖ ^ 2 * g ζ := by
    simp only [hg, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  have h3 : f (c • ζ) = ‖c‖ ^ 2 * f ζ := by
    simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_pow, ← norm_mul, Finset.mul_sum]
    congr 2
    exact Finset.sum_congr rfl fun j _ => by ring
  have h4 : 0 < ‖c‖ ^ 2 := by rw [hcn]; positivity
  rw [h2, h3, mul_left_comm] at h1
  exact le_of_mul_le_mul_left h1 h4

/- English proof (translation)
Rewrite using `[MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Establish `h` using `hQ (MvPolynomial.mem_support_iff.1 hs)`. Establish `h' : ∑ a, s a = d`. Rewrite using `[← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`.

Simplify using the standard rewrite rules. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval₂_smul_of_isHomogeneous {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} {Q : MvPolynomial (Fin n) K}
    (hQ : Q.IsHomogeneous d) (c : ℂ) (z : Fin n → ℂ) :
    MvPolynomial.eval₂ σ (fun a => c * z a) Q = c ^ d * MvPolynomial.eval₂ σ z Q := by
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h := hQ (MvPolynomial.mem_support_iff.1 hs)
  have h' : ∑ a, s a = d := by
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h']
  ring

/- English proof (translation)
Introduce `E _ _ _ r X Xa K _ σ t ht hrel sf`. Use `choose Q d hQ0 hQd hQ using hrel.1`. Set `Z : Set (Fin Xa.N → ℂ)` to `{ζ | ∀ jj, MvPolynomial.eval₂ σ (fun a => ζ (jj a)) (Q jj) = 0}`. Establish `hZ : IsClosed Z`. Simplify using `only [Z, Set.setOf_forall]`.

Use `isClosed_iInter fun jj => isClosed_eq ?_ continuous_const` and prove the remaining obligations. Simplify using `only [MvPolynomial.eval₂_eq']`. Use `fun_prop`. Take `⟨C, hC⟩` from `cone_sum_sq_le t Z hZ (fun c ζ hζ jj => by`. Use `eval₂_smul_of_isHomogeneous σ (hQd jj) c fun a => ζ (jj a)` as an intermediate fact.

Rewrite `this` using `[hζ jj, mul_zero]`. Conclude with `this)`. Use the proof step `(fun ζ hζ h => by`. Assume the negation of the conclusion as `hz`. Take `⟨jj, hjj⟩` from `GlobalTheory.T.exists_coords_no_homogeneous_relation_generic_hyperplanes K σ _ _ t ζ ht hz h`.

Conclude with `hjj _ _ (hQ0 jj) (hQd jj) (hζ jj))`. Conclude with `⟨C, fun x hx => hC (fun k => Xa.w k x) fun jj => hQ jj x hx⟩`.
-/
theorem forms_le_generic_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] (σ : K →+* ℂ) (t : Fin (nd X + 1) × Fin Xa.N → ℂ), (∀ Q : MvPolynomial (Fin (nd X + 1) × Fin Xa.N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → RelIn σ X Xa → let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ C * ∑ i, ‖sf i x‖ ^ 2 := by
  intro E _ _ _ r X Xa K _ σ t ht hrel sf
  choose Q d hQ0 hQd hQ using hrel.1
  let Z : Set (Fin Xa.N → ℂ) := {ζ | ∀ jj, MvPolynomial.eval₂ σ (fun a => ζ (jj a)) (Q jj) = 0}
  have hZ : IsClosed Z := by
    simp only [Z, Set.setOf_forall]
    refine isClosed_iInter fun jj => isClosed_eq ?_ continuous_const
    simp only [MvPolynomial.eval₂_eq']
    fun_prop
  obtain ⟨C, hC⟩ := cone_sum_sq_le t Z hZ
    (fun c ζ hζ jj => by
      have := eval₂_smul_of_isHomogeneous σ (hQd jj) c fun a => ζ (jj a)
      rw [hζ jj, mul_zero] at this
      exact this)
    (fun ζ hζ h => by
      by_contra hz
      obtain ⟨jj, hjj⟩ := GlobalTheory.T.exists_coords_no_homogeneous_relation_generic_hyperplanes K σ _ _ t ζ ht hz h
      exact hjj _ _ (hQ0 jj) (hQd jj) (hζ jj))
  exact ⟨C, fun x hx => hC (fun k => Xa.w k x) fun jj => hQ jj x hx⟩

end GlobalTheory.Shares
