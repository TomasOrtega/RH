import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ActInf
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.NormMatrixMulLeTwo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hm0 : 0 ≤ m ^ N` using `by positivity`. Distinguish the cases in `hv : finPartPi w ∈ K`. Establish `hv' : finPartPi v ∈ K` using `hf ▸ hv`. Generalize the expression as in `hsd : ‖infPartPi v‖ = s at h`. Generalize the expression as in `htd : ‖infPartPi w‖ = t at h`.

Establish `ht0 : 0 ≤ t` using `htd ▸ norm_nonneg _`. Establish `hs0 : 0 ≤ s` using `hsd ▸ norm_nonneg _`. Establish `h1 : 1 + s ≤ m * (1 + t)` using `by nlinarith`. Establish `hp : (1 + s) ^ N ≤ m ^ N * (1 + t) ^ N`. Rewrite using `[← mul_pow]`.

Conclude with `pow_le_pow_left₀ (by positivity) h1 N`. Establish `e1 : wt K N w = ((1 + t) ^ N)⁻¹` using `by rw [← htd]; exact if_pos hv`. Establish `e2 : wt K N v = ((1 + s) ^ N)⁻¹` using `by rw [← hsd]; exact if_pos hv'`. Rewrite using `[e1, e2, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e : wt K N w = 0` using `if_neg hv`. Rewrite using `[e]`. Use `mul_nonneg hm0 ?_` and prove the remaining obligations. Unfold `wt`. Use `split_ifs`.

Check the signs of the components of the expression. Conclude with `le_rfl`.
-/
private theorem wt_le_of_norm {K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} {N : ℕ} {v w : V4 F} {m : ℝ}
    (hm1 : 1 ≤ m) (hf : finPartPi w = finPartPi v) (h : ‖infPartPi v‖ ≤ m * ‖infPartPi w‖) :
    wt K N w ≤ m ^ N * wt K N v := by
  have hm0 : 0 ≤ m ^ N := by positivity
  by_cases hv : finPartPi w ∈ K
  · have hv' : finPartPi v ∈ K := hf ▸ hv
    generalize hsd : ‖infPartPi v‖ = s at h
    generalize htd : ‖infPartPi w‖ = t at h
    have ht0 : 0 ≤ t := htd ▸ norm_nonneg _
    have hs0 : 0 ≤ s := hsd ▸ norm_nonneg _
    have h1 : 1 + s ≤ m * (1 + t) := by nlinarith
    have hp : (1 + s) ^ N ≤ m ^ N * (1 + t) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1 N
    have e1 : wt K N w = ((1 + t) ^ N)⁻¹ := by rw [← htd]; exact if_pos hv
    have e2 : wt K N v = ((1 + s) ^ N)⁻¹ := by rw [← hsd]; exact if_pos hv'
    rw [e1, e2, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  · have e : wt K N w = 0 := if_neg hv
    rw [e]
    refine mul_nonneg hm0 ?_
    unfold wt
    split_ifs
    · positivity
    · exact le_rfl

/- English proof (translation)
Take `⟨w', hw'⟩` from `InfinitePlace.comap_surjective (k := F) (K := E) w`. Use `⟨w'.embedding, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `InfinitePlace.mk (w'.embedding.comp (algebraMap F E)) = w`. Rewrite using `[← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]`. Conclude with `hw'`.
-/
private theorem exists_pl (w : InfinitePlace F) : ∃ τ : E →+* ℂ, UpperTheory.ConvolutionTheory.R2.Fo.pl F τ = w := by
  obtain ⟨w', hw'⟩ := InfinitePlace.comap_surjective (k := F) (K := E) w
  refine ⟨w'.embedding, ?_⟩
  change InfinitePlace.mk (w'.embedding.comp (algebraMap F E)) = w
  rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  exact hw'

/- English proof (translation)
Establish `T : ∀ a b, ‖Y i a * H a b * star (Y j b)‖ ≤ t ^ 2 * B` using `fun a b => by`. Rewrite using `[norm_mul, norm_mul, norm_star]`. Combine the equalities or inequalities in the displayed calculation. Establish `e : (Y * H * Yᴴ) i j = Y i 0 * H 0 0 * star (Y j 0) + Y i 1 * H 1 0 * star (Y j 0) + (Y i 0 * H 0 1 * star (Y j 1) + Y i 1 * H 1 1 * star (Y j 1))`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Combine the linear relations using `[norm_add_le (Y i 0 * H 0 0 * star (Y j 0)) (Y i 1 * H 1 0 * star (Y j 0)), norm_add_le (Y i 0 * H 0 1 * star (Y j 1)) (Y i 1 * H 1 1 * star (Y j 1)), T 0 0, T 1 0, T 0 1, T 1 1]`.
-/
private theorem entry_le (Y H : Matrix (Fin 2) (Fin 2) ℂ) {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hY : ∀ i j, ‖Y i j‖ ≤ t) (hH : ∀ i j, ‖H i j‖ ≤ B) (i j : Fin 2) :
    ‖(Y * H * Yᴴ) i j‖ ≤ 4 * t ^ 2 * B := by
  have T : ∀ a b, ‖Y i a * H a b * star (Y j b)‖ ≤ t ^ 2 * B := fun a b => by
    rw [norm_mul, norm_mul, norm_star]
    calc ‖Y i a‖ * ‖H a b‖ * ‖Y j b‖ ≤ t * B * t :=
          mul_le_mul (mul_le_mul (hY _ _) (hH _ _) (norm_nonneg _) ht) (hY _ _) (norm_nonneg _)
            (mul_nonneg ht hB)
      _ = t ^ 2 * B := by ring
  have e : (Y * H * Yᴴ) i j = Y i 0 * H 0 0 * star (Y j 0) + Y i 1 * H 1 0 * star (Y j 0) +
      (Y i 0 * H 0 1 * star (Y j 1) + Y i 1 * H 1 1 * star (Y j 1)) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  linarith [norm_add_le (Y i 0 * H 0 0 * star (Y j 0)) (Y i 1 * H 1 0 * star (Y j 0)),
    norm_add_le (Y i 0 * H 0 1 * star (Y j 1)) (Y i 1 * H 1 1 * star (Y j 1)), T 0 0, T 1 0, T 0 1, T 1 1]

end

section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
The claim follows from `|TR.pInf F (v i) w| ≤ ‖infPartPi v‖ := by have hw : w.IsReal := IsTotallyReal.isReal w have e : (infPartPi v i).1 ⟨w, hw⟩ = TR.pInf F (v i) w := rfl calc |TR.pInf F (v i) w| = ‖(infPartPi v i).1 ⟨w, hw⟩‖ := by rw [e, Real.norm_eq_abs] _ ≤ ‖(infPartPi v i).1‖ := norm_le_pi_norm _ …`.
-/
private theorem abs_pInf_le (v : V4 F) (i : Fin 4) (w : InfinitePlace F) :
    |TR.pInf F (v i) w| ≤ ‖infPartPi v‖ := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  have e : (infPartPi v i).1 ⟨w, hw⟩ = TR.pInf F (v i) w := rfl
  calc |TR.pInf F (v i) w| = ‖(infPartPi v i).1 ⟨w, hw⟩‖ := by rw [e, Real.norm_eq_abs]
    _ ≤ ‖(infPartPi v i).1‖ := norm_le_pi_norm _ _
    _ ≤ ‖infPartPi v i‖ := norm_fst_le _
    _ ≤ ‖infPartPi v‖ := norm_le_pi_norm _ _

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg hU).2 fun i => ?_` and prove the remaining obligations. Rewrite using `[Prod.norm_def]`. Use `max_le ((pi_norm_le_iff_of_nonneg hU).2 fun w => ?_) ((pi_norm_le_iff_of_nonneg hU).2 fun w => ?_)` and prove the remaining obligations. Establish `e : (infPartPi v i).1 w = TR.pInf F (v i) w.1` using `rfl`. Rewrite using `[e, Real.norm_eq_abs]`.

Conclude with `h i w.1`. Conclude with `absurd w.2 (InfinitePlace.not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1))`.
-/
private theorem norm_inf_le (v : V4 F) {U : ℝ} (hU : 0 ≤ U)
    (h : ∀ i w, |TR.pInf F (v i) w| ≤ U) : ‖infPartPi v‖ ≤ U := by
  refine (pi_norm_le_iff_of_nonneg hU).2 fun i => ?_
  rw [Prod.norm_def]
  refine max_le ((pi_norm_le_iff_of_nonneg hU).2 fun w => ?_) ((pi_norm_le_iff_of_nonneg hU).2 fun w => ?_)
  · have e : (infPartPi v i).1 w = TR.pInf F (v i) w.1 := rfl
    rw [e, Real.norm_eq_abs]
    exact h i w.1
  · exact absurd w.2 (InfinitePlace.not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1))

/- English proof (translation)
Establish `hs' : 0 < ‖s‖` using `norm_pos_iff.2 hs`. Establish `e00 : Hm s w x 0 0 = (x 1 w : ℂ)` using `by simp [Hm]`. Establish `e11 : Hm s w x 1 1 = (x 0 w : ℂ)` using `by simp [Hm]`. Establish `e01 : Hm s w x 0 1 = (x 2 w : ℂ) + s * (x 3 w : ℂ)` using `by simp [Hm]`. Establish `e10 : Hm s w x 1 0 = (x 2 w : ℂ) - s * (x 3 w : ℂ)` using `by simp [Hm]`.

Establish `h0 : |x 0 w| ≤ B` using `by simpa [e11] using h 1 1`. Establish `h1 : |x 1 w| ≤ B` using `by simpa [e00] using h 0 0`. Establish `h2 : |x 2 w| ≤ B`. Establish `e : ((2 * x 2 w : ℝ) : ℂ) = Hm s w x 0 1 + Hm s w x 1 0`. Rewrite using `[e01, e10]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `: ‖((2 * x 2 w : ℝ) : ℂ)‖ ≤ B + B`. Rewrite using `[e]`. Conclude with `(norm_add_le _ _).trans (add_le_add (h _ _) (h _ _))`.

Rewrite `this` using `[Complex.norm_real, Real.norm_eq_abs, abs_mul]`. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : |x 3 w| ≤ ‖s‖⁻¹ * B`. Establish `e : s * ((2 * x 3 w : ℝ) : ℂ) = Hm s w x 0 1 - Hm s w x 1 0`.

Rewrite using `[e01, e10]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `: ‖s * ((2 * x 3 w : ℝ) : ℂ)‖ ≤ B + B`. Rewrite using `[e]`.

Conclude with `(norm_sub_le _ _).trans (add_le_add (h _ _) (h _ _))`. Rewrite `this` using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]`. Evaluate the numerical expressions using `at this`. Rewrite using `[inv_mul_eq_div, le_div_iff₀ hs']`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hp : 0 ≤ ‖s‖⁻¹ * B` using `by positivity`. Use `fin_cases i`. Express the relevant statement in the definitionally equal form `|x 0 w| ≤ _`. Use the polynomial consequences of the given equalities and inequalities. Express the relevant statement in the definitionally equal form `|x 1 w| ≤ _`.

Use the polynomial consequences of the given equalities and inequalities. Express the relevant statement in the definitionally equal form `|x 2 w| ≤ _`. Use the polynomial consequences of the given equalities and inequalities. Express the relevant statement in the definitionally equal form `|x 3 w| ≤ _`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem co_le_Hm {s : ℂ} (hs : s ≠ 0) (w : InfinitePlace F) (x : Fin 4 → TR.Rinf F) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ i j, ‖Hm s w x i j‖ ≤ B) (i : Fin 4) : |x i w| ≤ (1 + ‖s‖⁻¹) * B := by
  have hs' : 0 < ‖s‖ := norm_pos_iff.2 hs
  have e00 : Hm s w x 0 0 = (x 1 w : ℂ) := by simp [Hm]
  have e11 : Hm s w x 1 1 = (x 0 w : ℂ) := by simp [Hm]
  have e01 : Hm s w x 0 1 = (x 2 w : ℂ) + s * (x 3 w : ℂ) := by simp [Hm]
  have e10 : Hm s w x 1 0 = (x 2 w : ℂ) - s * (x 3 w : ℂ) := by simp [Hm]
  have h0 : |x 0 w| ≤ B := by simpa [e11] using h 1 1
  have h1 : |x 1 w| ≤ B := by simpa [e00] using h 0 0
  have h2 : |x 2 w| ≤ B := by
    have e : ((2 * x 2 w : ℝ) : ℂ) = Hm s w x 0 1 + Hm s w x 1 0 := by
      rw [e01, e10]; push_cast; ring
    have : ‖((2 * x 2 w : ℝ) : ℂ)‖ ≤ B + B := by
      rw [e]; exact (norm_add_le _ _).trans (add_le_add (h _ _) (h _ _))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul] at this
    norm_num at this
    linarith
  have h3 : |x 3 w| ≤ ‖s‖⁻¹ * B := by
    have e : s * ((2 * x 3 w : ℝ) : ℂ) = Hm s w x 0 1 - Hm s w x 1 0 := by
      rw [e01, e10]; push_cast; ring
    have : ‖s * ((2 * x 3 w : ℝ) : ℂ)‖ ≤ B + B := by
      rw [e]; exact (norm_sub_le _ _).trans (add_le_add (h _ _) (h _ _))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul] at this
    norm_num at this
    rw [inv_mul_eq_div, le_div_iff₀ hs']
    nlinarith
  have hp : 0 ≤ ‖s‖⁻¹ * B := by positivity
  fin_cases i
  · change |x 0 w| ≤ _
    nlinarith
  · change |x 1 w| ≤ _
    nlinarith
  · change |x 2 w| ≤ _
    nlinarith
  · change |x 3 w| ≤ _
    nlinarith

/- English proof (translation)
Establish `hn : 0 ≤ ‖s‖ * U` using `by positivity`. Establish `hr : ∀ k, ‖(x k w : ℂ)‖ ≤ U` using `fun k => by`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs]`. Conclude with `h k`. Establish `hm : ‖s * (x 3 w : ℂ)‖ ≤ ‖s‖ * U`.

Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hr 3) (norm_nonneg _)`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Establish `e : Hm s w x 0 0 = (x 1 w : ℂ)` using `by simp [Hm]`. Express the relevant statement in the definitionally equal form `‖Hm s w x 0 0‖ ≤ _`.

Rewrite using `[e]`. Use polynomial arithmetic with `[hr 1]`. Establish `e : Hm s w x 0 1 = (x 2 w : ℂ) + s * (x 3 w : ℂ)` using `by simp [Hm]`. Express the relevant statement in the definitionally equal form `‖Hm s w x 0 1‖ ≤ _`. Rewrite using `[e]`.

Conclude with `(norm_add_le _ _).trans (by nlinarith [hr 2])`. Establish `e : Hm s w x 1 0 = (x 2 w : ℂ) - s * (x 3 w : ℂ)` using `by simp [Hm]`. Express the relevant statement in the definitionally equal form `‖Hm s w x 1 0‖ ≤ _`. Rewrite using `[e]`. Conclude with `(norm_sub_le _ _).trans (by nlinarith [hr 2])`.

Establish `e : Hm s w x 1 1 = (x 0 w : ℂ)` using `by simp [Hm]`. Express the relevant statement in the definitionally equal form `‖Hm s w x 1 1‖ ≤ _`. Rewrite using `[e]`. Use polynomial arithmetic with `[hr 0]`.
-/
private theorem Hm_le (s : ℂ) (w : InfinitePlace F) (x : Fin 4 → TR.Rinf F) {U : ℝ}
    (hU : 0 ≤ U) (h : ∀ i, |x i w| ≤ U) (i j : Fin 2) : ‖Hm s w x i j‖ ≤ (1 + ‖s‖) * U := by
  have hn : 0 ≤ ‖s‖ * U := by positivity
  have hr : ∀ k, ‖(x k w : ℂ)‖ ≤ U := fun k => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact h k
  have hm : ‖s * (x 3 w : ℂ)‖ ≤ ‖s‖ * U := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hr 3) (norm_nonneg _)
  fin_cases i <;> fin_cases j
  · have e : Hm s w x 0 0 = (x 1 w : ℂ) := by simp [Hm]
    change ‖Hm s w x 0 0‖ ≤ _
    rw [e]
    nlinarith [hr 1]
  · have e : Hm s w x 0 1 = (x 2 w : ℂ) + s * (x 3 w : ℂ) := by simp [Hm]
    change ‖Hm s w x 0 1‖ ≤ _
    rw [e]
    exact (norm_add_le _ _).trans (by nlinarith [hr 2])
  · have e : Hm s w x 1 0 = (x 2 w : ℂ) - s * (x 3 w : ℂ) := by simp [Hm]
    change ‖Hm s w x 1 0‖ ≤ _
    rw [e]
    exact (norm_sub_le _ _).trans (by nlinarith [hr 2])
  · have e : Hm s w x 1 1 = (x 0 w : ℂ) := by simp [Hm]
    change ‖Hm s w x 1 1‖ ≤ _
    rw [e]
    nlinarith [hr 0]

end

section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
The claim follows from `|x i w| ≤ (1 + ‖s‖⁻¹) * (4 * (1 + ‖s‖)) * (t ^ 2 * U) := by have e : Hm s w x = Y * Hm s w x' * Yᴴ := by calc Hm s w x = (Y * Z) * Hm s w x * (Y * Z)ᴴ := by rw [hZ]; simp _ = Y * Hm s w x' * Yᴴ := by rw [hx, Matrix.conjTranspose_mul] simp only [Matrix.mul_assoc] have hH : ∀ i j, …`.
-/
private theorem pt_bound {s : ℂ} (hs : s ≠ 0) (w : InfinitePlace F) (x x' : Fin 4 → TR.Rinf F)
    (Y Z : Matrix (Fin 2) (Fin 2) ℂ) (hZ : Y * Z = 1) (hx : Hm s w x' = Z * Hm s w x * Zᴴ)
    {t U : ℝ} (ht : 0 ≤ t) (hU : 0 ≤ U) (hY : ∀ i j, ‖Y i j‖ ≤ t) (h' : ∀ i, |x' i w| ≤ U) (i : Fin 4) :
    |x i w| ≤ (1 + ‖s‖⁻¹) * (4 * (1 + ‖s‖)) * (t ^ 2 * U) := by
  have e : Hm s w x = Y * Hm s w x' * Yᴴ := by
    calc Hm s w x = (Y * Z) * Hm s w x * (Y * Z)ᴴ := by rw [hZ]; simp
      _ = Y * Hm s w x' * Yᴴ := by
        rw [hx, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
  have hH : ∀ i j, ‖Hm s w x i j‖ ≤ 4 * t ^ 2 * ((1 + ‖s‖) * U) := fun i j => by
    rw [e]
    exact entry_le _ _ ht (by positivity) hY (Hm_le s w x' hU h') i j
  have := co_le_Hm hs w x (by positivity) hH i
  calc |x i w| ≤ _ := this
    _ = _ := by ring

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D`. Establish `hθ : ∀ τ : E →+* ℂ, τ D.θ ≠ 0` using `fun τ => (map_ne_zero τ).2 D.θ_ne_zero`. Take `⟨A, hA0, hterm⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∀ τ : E →+* ℂ, (1 + ‖τ D.θ‖⁻¹) * (4 * (1 + ‖τ D.θ‖)) ≤ A` from `⟨∑ τ : E →+* ℂ, (1 + ‖τ D.θ‖⁻¹) * (4 * (1 + ‖τ D.θ‖)), Finset.sum_nonneg fun _ _ => by positivity, fun τ => Finset.single_le_sum (f := fun τ : E →+* ℂ => (1 + ‖τ D.θ‖⁻¹) * (4 * (1 + ‖τ D.θ‖))) (fun _ _ => by positivity) (Finset.mem_univ τ)⟩`. Use `⟨A + 1, fun K N y v => ?_⟩` and prove the remaining obligations. Establish `hHt : 1 ≤ Ht y` using `((htLe E).2 y).1`.

Establish `hH2 : 1 ≤ Ht y ^ 2` using `one_le_pow₀ hHt`. Establish `hm1 : 1 ≤ (A + 1) * Ht y ^ 2` using `by nlinarith`. Rewrite using `[← map_inv]`. Establish `hact` using `actInf F E D y⁻¹ v`. Use `wt_le_of_norm hm1 hact.1 ?_` and prove the remaining obligations.

Establish `hU : 0 ≤ ‖infPartPi (D.act (infGL E 2 y⁻¹) v)‖` using `norm_nonneg _`. Use `norm_inf_le v (by positivity) fun i w => ?_` and prove the remaining obligations. Take `⟨τ, rfl⟩` from `exists_pl (E := E) w`. Establish `hZ : y.val.map (coord τ) * (y⁻¹).val.map (coord τ) = 1`. Express the relevant statement in the definitionally equal form `(coord τ).mapMatrix y.val * (coord τ).mapMatrix (y⁻¹).val = 1`.

Rewrite using `[← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]`. Establish `hY : ∀ i j, ‖y.val.map (coord τ) i j‖ ≤ Ht y` using `fun i j => by`. Establish `h1 : ‖coord τ (y.val i j)‖ = ‖y.val i j (InfinitePlace.mk τ)‖` using `GlobalTheory.IsoPull.norm_coord τ _`. Establish `h2 : ‖y.val i j (InfinitePlace.mk τ)‖ ≤ ‖toL y.val‖` using `(norm_le_pi_norm (y.val i j) _).trans ((norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i))`. Establish `h3 : 0 ≤ ‖toL (y⁻¹).val‖` using `norm_nonneg _`.

Rewrite using `[Matrix.map_apply, h1]`. Unfold `Ht`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key` using `pt_bound (hθ τ) (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) (fun i => TR.pInf F (v i)) (fun i => TR.pInf F (D.act (infGL E 2 y⁻¹) v i)) _ _ hZ (hact.2 τ) (by linarith) hU hY (fun i => abs_pInf_le _ i _) i`. Use `key.trans ?_` and prove the remaining obligations.

Establish `hp : 0 ≤ Ht y ^ 2 * ‖infPartPi (D.act (infGL E 2 y⁻¹) v)‖` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.wtAct :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), WtAct D := by
  intro F E _ _ _ _ _ _ _ D
  have hθ : ∀ τ : E →+* ℂ, τ D.θ ≠ 0 := fun τ => (map_ne_zero τ).2 D.θ_ne_zero
  obtain ⟨A, hA0, hterm⟩ : ∃ A : ℝ, 0 ≤ A ∧
      ∀ τ : E →+* ℂ, (1 + ‖τ D.θ‖⁻¹) * (4 * (1 + ‖τ D.θ‖)) ≤ A :=
    ⟨∑ τ : E →+* ℂ, (1 + ‖τ D.θ‖⁻¹) * (4 * (1 + ‖τ D.θ‖)),
      Finset.sum_nonneg fun _ _ => by positivity, fun τ =>
        Finset.single_le_sum (f := fun τ : E →+* ℂ => (1 + ‖τ D.θ‖⁻¹) * (4 * (1 + ‖τ D.θ‖)))
          (fun _ _ => by positivity) (Finset.mem_univ τ)⟩
  refine ⟨A + 1, fun K N y v => ?_⟩
  have hHt : 1 ≤ Ht y := ((htLe E).2 y).1
  have hH2 : 1 ≤ Ht y ^ 2 := one_le_pow₀ hHt
  have hm1 : 1 ≤ (A + 1) * Ht y ^ 2 := by nlinarith
  rw [← map_inv]
  have hact := actInf F E D y⁻¹ v
  refine wt_le_of_norm hm1 hact.1 ?_
  have hU : 0 ≤ ‖infPartPi (D.act (infGL E 2 y⁻¹) v)‖ := norm_nonneg _
  refine norm_inf_le v (by positivity) fun i w => ?_
  obtain ⟨τ, rfl⟩ := exists_pl (E := E) w
  have hZ : y.val.map (coord τ) * (y⁻¹).val.map (coord τ) = 1 := by
    change (coord τ).mapMatrix y.val * (coord τ).mapMatrix (y⁻¹).val = 1
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hY : ∀ i j, ‖y.val.map (coord τ) i j‖ ≤ Ht y := fun i j => by
    have h1 : ‖coord τ (y.val i j)‖ = ‖y.val i j (InfinitePlace.mk τ)‖ := GlobalTheory.IsoPull.norm_coord τ _
    have h2 : ‖y.val i j (InfinitePlace.mk τ)‖ ≤ ‖toL y.val‖ :=
      (norm_le_pi_norm (y.val i j) _).trans
        ((norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i))
    have h3 : 0 ≤ ‖toL (y⁻¹).val‖ := norm_nonneg _
    rw [Matrix.map_apply, h1]
    unfold Ht
    linarith
  have key := pt_bound (hθ τ) (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) (fun i => TR.pInf F (v i))
    (fun i => TR.pInf F (D.act (infGL E 2 y⁻¹) v i)) _ _ hZ (hact.2 τ) (by linarith) hU hY
    (fun i => abs_pInf_le _ i _) i
  refine key.trans ?_
  have hp : 0 ≤ Ht y ^ 2 * ‖infPartPi (D.act (infGL E 2 y⁻¹) v)‖ := by positivity
  calc _ ≤ A * (Ht y ^ 2 * ‖infPartPi (D.act (infGL E 2 y⁻¹) v)‖) :=
        mul_le_mul_of_nonneg_right (hterm τ) hp
    _ ≤ (A + 1) * Ht y ^ 2 * ‖infPartPi (D.act (infGL E 2 y⁻¹) v)‖ := by nlinarith
