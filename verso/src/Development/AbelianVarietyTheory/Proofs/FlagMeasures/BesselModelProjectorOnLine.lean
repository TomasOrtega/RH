import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalStandardSideStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormIdentityBesselCoefficientQuotientStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.ProjLine

/- English proof (translation)
Simplify using `only [GG, UH, Set.mem_setOf_eq] at hs ⊢`. Establish `e : (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * (sᴴ * Hpk k r * s) * x`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[e, hs]`.
-/
theorem mul_mem_GG_iff {k r : ℕ} {s x : Mat k r} (hs : s ∈ GG k r) : s * x ∈ GG k r ↔ x ∈ GG k r := by
  simp only [GG, UH, Set.mem_setOf_eq] at hs ⊢
  have e : (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * (sᴴ * Hpk k r * s) * x := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hs]

/- English proof (translation)
Introduce and unpack `s ⟨h, hh, m, hm, rfl⟩`. Conclude with `(mul_mem_GG_iff hh.1).2 hm.1`.
-/
theorem Sset_subset_GG {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) : Sset k r z ⊆ GG k r := by
  rintro s ⟨h, hh, m, hm, rfl⟩
  exact (mul_mem_GG_iff hh.1).2 hm.1

/- English proof (translation)
Establish `hc : Continuous fun x : Mat k r => xᴴ * Hpk k r * x` using `((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id`. Conclude with `isClosed_eq (X := Mt k r) hc continuous_const`.
-/
theorem isClosed_GG (k r : ℕ) : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} := by
  have hc : Continuous fun x : Mat k r => xᴴ * Hpk k r * x :=
    ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq (X := Mt k r) hc continuous_const

/- English proof (translation)
Rewrite using `[rankOneInnerOperator_apply, inner_self_eq_norm_sq_to_K]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem rankOneInnerOperator_self_apply {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (x y : Wp) :
    rk1 y x x = ((‖x‖ ^ 2 : ℝ) : ℂ) • y := by
  rw [rankOneInnerOperator_apply, inner_self_eq_norm_sq_to_K]; push_cast; rfl

/- English proof (translation)
Rewrite using `[rankOneInnerOperator_self_apply, inner_smul_right, inner_self_eq_norm_sq_to_K]`. Establish `e : ((‖x‖ : ℝ) : ℂ) = (RCLike.ofReal ‖x‖ : ℂ)` using `rfl`. Use `push_cast`. Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_rankOneInnerOperator_self {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (x : Wp) :
    ⟪x, rk1 x x x⟫_ℂ = (((‖x‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
  rw [rankOneInnerOperator_self_apply, inner_smul_right, inner_self_eq_norm_sq_to_K]
  have e : ((‖x‖ : ℝ) : ℂ) = (RCLike.ofReal ‖x‖ : ℂ) := rfl
  push_cast
  rw [← e]; ring

/- English proof (translation)
Use `set B : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∉ GG k r} with hBdef`. Establish `hB : MeasurableSet B` using `(isClosed_GG k r).measurableSet.compl`. Establish `h0` using `hq (B.indicator 1) (measurable_one.indicator hB)`. Rewrite `h0` using `[lintegral_indicator_one hB, hG.2.2.1]`. Establish `hc : μS Set.univ ≠ 0`.

Introduce `h`. Conclude with `hS.2.1 (Measure.measure_univ_eq_zero.1 h)`. Establish `hle : ∀ x, B.indicator (fun _ => μS Set.univ) x ≤ ∫⁻ s, B.indicator 1 (fun i j => (Matrix.of s * Matrix.of x : Mat k r) i j) ∂μS`. Introduce `x`. Distinguish the cases in `hx : x ∈ B`.

Rewrite using `[Set.indicator_of_mem hx]`. Combine the equalities or inequalities in the displayed calculation. Apply `lintegral_mono_ae` to reduce the goal to its premises. Establish `hnull : ∀ᵐ s ∂μS, (Matrix.of s : Mat k r) ∈ Sset k r z`. Rewrite using `[ae_iff]`.

Simplify using `using hS.2.2.1`. Use `filter_upwards [hnull] with s hs`. Establish `hmem : (fun i j => (Matrix.of s * Matrix.of x : Mat k r) i j) ∈ B` using `by show ¬ ((Matrix.of s * Matrix.of x : Mat k r) ∈ GG k r)`. Introduce `h`. Conclude with `hx ((mul_mem_GG_iff (Sset_subset_GG z hs)).1 h)`.

Rewrite using `[Set.indicator_of_mem hmem]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hx]`. Conclude with `zero_le`. Establish `hmul : μS Set.univ * ν B = 0`.

Rewrite using `[← lintegral_indicator_const hB]`. Conclude with `le_antisymm ((lintegral_mono hle).trans h0.symm.le) (zero_le)`. Establish `hνB : ν B = 0` using `(mul_eq_zero.1 hmul).resolve_left hc`. Rewrite using `[ae_iff]`. Simplify `hνB` using `[hBdef]`.
-/
theorem ae_mem_GG {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {μG μS ν : Measure (Mt k r)}
    (hG : IsHaarOn (GG k r) μG) (hS : IsHaarOn (Sset k r z) μS) (hq : IsQuotMeas μG μS ν) :
    ∀ᵐ x ∂ν, (Matrix.of x : Mat k r) ∈ GG k r := by
  set B : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∉ GG k r} with hBdef
  have hB : MeasurableSet B := (isClosed_GG k r).measurableSet.compl
  have h0 := hq (B.indicator 1) (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, hG.2.2.1] at h0
  have hc : μS Set.univ ≠ 0 := by
    intro h; exact hS.2.1 (Measure.measure_univ_eq_zero.1 h)
  have hle : ∀ x, B.indicator (fun _ => μS Set.univ) x ≤
      ∫⁻ s, B.indicator 1 (fun i j => (Matrix.of s * Matrix.of x : Mat k r) i j) ∂μS := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      calc μS Set.univ = ∫⁻ _, 1 ∂μS := (lintegral_one).symm
        _ ≤ _ := by
          apply lintegral_mono_ae
          have hnull : ∀ᵐ s ∂μS, (Matrix.of s : Mat k r) ∈ Sset k r z := by
            rw [ae_iff]; simpa using hS.2.2.1
          filter_upwards [hnull] with s hs
          have hmem : (fun i j => (Matrix.of s * Matrix.of x : Mat k r) i j) ∈ B := by
            show ¬ ((Matrix.of s * Matrix.of x : Mat k r) ∈ GG k r)
            intro h; exact hx ((mul_mem_GG_iff (Sset_subset_GG z hs)).1 h)
          rw [Set.indicator_of_mem hmem]; rfl
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  have hmul : μS Set.univ * ν B = 0 := by
    rw [← lintegral_indicator_const hB]
    exact le_antisymm ((lintegral_mono hle).trans h0.symm.le) (zero_le)
  have hνB : ν B = 0 := (mul_eq_zero.1 hmul).resolve_left hc
  rw [ae_iff]; simpa [hBdef] using hνB

/- English proof (translation)
Introduce `k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hq l hl`. Establish `hG : IsHaarOn (GG k r) μG` using `hStd.2.2.2.2.1`. Establish `hU : IsURepOn (GG k r) σ` using `hStd.2.1`. Establish `hd : 0 < d` using `hStd.2.2.2.2.2.1.1`. Establish `hS : IsHaarOn (Sset k r z) μS` using `hSide.2.2.2.1`.

Establish `hae` using `ae_mem_GG hG hS hq`. Establish `hstab` using `(GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hU).1`. Take `⟨_, ⟨v0, hv0, hlv0⟩, hbe⟩` from `hl`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu`.

Take `⟨_, _, hmem, heq, _, _⟩` from `GlobalTheory.T.norm_identity_besselCoefficient_quotient k r σ w a μG d z c π μS hStd hSide ν hq u hu u hu v0 hv0 (l v0)`. Use `set A : Mt k r → Wp := fun x => Afun (psiGen k r z c) π μS σ u v0 (l v0) (Matrix.of x) with hAdef`. Use `set L : Mt k r → Wp := fun x => l (σ (Matrix.of x) u) with hLdef`. Use `set N : ℝ := ‖l v0‖ ^ 2 with hNdef`. Establish `hN : 0 < N` using `by positivity`.

Establish `hAL : ∀ᵐ x ∂ν, A x = (N : ℂ) • L x` using `by filter_upwards [hae] with x hx`. Simplify using `only [hAdef, hLdef, Afun]`. Rewrite using `[hbe _ (hstab _ hx _ hu) _ hv0, rankOneInnerOperator_apply, inner_self_eq_norm_sq_to_K]`. Simplify using `[hNdef]`. Establish `hnA : ∀ᵐ x ∂ν, ‖A x‖ ^ 2 = N ^ 2 * ‖L x‖ ^ 2` using `by filter_upwards [hAL] with x hx`.

Rewrite using `[hx, norm_smul, Complex.norm_real, Real.norm_of_nonneg hN.le, mul_pow]`. Establish `hIA : Integrable (fun x => ‖A x‖ ^ 2) ν` using `hmem.integrable_norm_pow two_ne_zero`. Establish `hIL : Integrable (fun x => ‖L x‖ ^ 2) ν`. Establish `: (fun x => ‖L x‖ ^ 2) =ᵐ[ν] fun x => (N ^ 2)⁻¹ * ‖A x‖ ^ 2` using `by filter_upwards [hnA] with x hx`. Rewrite using `[hx, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]`.

Conclude with `(hIA.const_mul _).congr this.symm`. Establish `hbevv : ⟪l v0, be (psiGen k r z c) π μS σ v0 v0 (l v0)⟫_ℂ = ((N ^ 2 : ℝ) : ℂ)`. Rewrite using `[hbe _ hv0 _ hv0, inner_rankOneInnerOperator_self]`. Establish `hintA : ∫ x, ‖A x‖ ^ 2 ∂ν = N ^ 2 * (‖u‖ ^ 2 / d)`. Establish `h1 : ∫ x, ⟪A x, A x⟫_ℂ ∂ν = ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ)`.

Rewrite using `[← integral_complex_ofReal]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [inner_self_eq_norm_sq_to_K]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `h2` using `heq`. Rewrite `h2` using `[hbevv, inner_self_eq_norm_sq_to_K u]`. Establish `h3 : ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) = ((N ^ 2 * (‖u‖ ^ 2 / d) : ℝ) : ℂ)`. Rewrite using `[← h1]`. Use `h2.trans ?_` and prove the remaining obligations.

Establish `e : ((‖u‖ : ℝ) : ℂ) = (RCLike.ofReal ‖u‖ : ℂ)` using `rfl`. Use `push_cast`. Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `h3` after adjusting the coercions.

Establish `hintL : ∫ x, ‖L x‖ ^ 2 ∂ν = ‖u‖ ^ 2 / d`. Establish `: ∫ x, ‖A x‖ ^ 2 ∂ν = N ^ 2 * ∫ x, ‖L x‖ ^ 2 ∂ν`. Rewrite using `[← integral_const_mul]`. Conclude with `integral_congr_ae hnA`. Rewrite `hintA` using `[this]`.

Conclude with `mul_left_cancel₀ (by positivity) hintA`. Unfold `l2SG`. Rewrite using `[← hintL, ofReal_integral_eq_lintegral_ofReal hIL (Filter.Eventually.of_forall fun x => by positivity)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`.

Both sides reduce to the same expression. Introduce `v hv ξ x hx`. Simplify using `only [Afun]`. Rewrite using `[hbe _ (mem_DD σ w hx) _ hv, rankOneInnerOperator_apply]`. Introduce `W hW1 hW2 hEq hL2 y hy`.

Take `⟨_, hconv⟩` from `GlobalTheory.T.bessel_functional_standard_side k r σ w a μG d z c π μS hStd hSide ν hq W hW1 hW2 hEq hL2 y hy`. Rewrite using `[hconv]`. Establish `h : ∀ᵐ g ∂ν, be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g)) = ⟪l (σ (Matrix.of g) w), W (Matrix.of g)⟫_ℂ • l (σ y w)` using `by filter_upwards [hae] with g hg`. Rewrite using `[hbe _ (mem_DD σ w hy) _ (mem_DD σ w hg), rankOneInnerOperator_apply]`. Rewrite using `[integral_congr_ae h, integral_smul_const, smul_smul]`.
-/
theorem projector_line : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ w) l → (∀ u ∈ DD σ w, l2SG ν (fun x => l (σ x u)) = ENNReal.ofReal (‖u‖ ^ 2 / d)) ∧ (∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ x ∈ GG k r, Afun (psiGen k r z c) π μS σ w v ξ x = ⟪l v, ξ⟫_ℂ • l (σ x w)) ∧ ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, rconv μG (eFun μG σ w) W y = ((d : ℂ) * ∫ g, ⟪l (σ (Matrix.of g) w), W (Matrix.of g)⟫_ℂ ∂ν) • l (σ y w) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hq l hl
  have hG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hU : IsURepOn (GG k r) σ := hStd.2.1
  have hd : 0 < d := hStd.2.2.2.2.2.1.1
  have hS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  have hae := ae_mem_GG hG hS hq
  have hstab := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hU).1
  obtain ⟨_, ⟨v0, hv0, hlv0⟩, hbe⟩ := hl
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨_, _, hmem, heq, _, _⟩ :=
      GlobalTheory.T.norm_identity_besselCoefficient_quotient k r σ w a μG d z c π μS hStd hSide ν hq u hu u hu v0 hv0 (l v0)
    set A : Mt k r → Wp := fun x => Afun (psiGen k r z c) π μS σ u v0 (l v0) (Matrix.of x) with hAdef
    set L : Mt k r → Wp := fun x => l (σ (Matrix.of x) u) with hLdef
    set N : ℝ := ‖l v0‖ ^ 2 with hNdef
    have hN : 0 < N := by positivity
    have hAL : ∀ᵐ x ∂ν, A x = (N : ℂ) • L x := by
      filter_upwards [hae] with x hx
      simp only [hAdef, hLdef, Afun]
      rw [hbe _ (hstab _ hx _ hu) _ hv0, rankOneInnerOperator_apply, inner_self_eq_norm_sq_to_K]
      simp [hNdef]
    have hnA : ∀ᵐ x ∂ν, ‖A x‖ ^ 2 = N ^ 2 * ‖L x‖ ^ 2 := by
      filter_upwards [hAL] with x hx
      rw [hx, norm_smul, Complex.norm_real, Real.norm_of_nonneg hN.le, mul_pow]
    have hIA : Integrable (fun x => ‖A x‖ ^ 2) ν := hmem.integrable_norm_pow two_ne_zero
    have hIL : Integrable (fun x => ‖L x‖ ^ 2) ν := by
      have : (fun x => ‖L x‖ ^ 2) =ᵐ[ν] fun x => (N ^ 2)⁻¹ * ‖A x‖ ^ 2 := by
        filter_upwards [hnA] with x hx
        rw [hx, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
      exact (hIA.const_mul _).congr this.symm
    have hbevv : ⟪l v0, be (psiGen k r z c) π μS σ v0 v0 (l v0)⟫_ℂ = ((N ^ 2 : ℝ) : ℂ) := by
      rw [hbe _ hv0 _ hv0, inner_rankOneInnerOperator_self]
    have hintA : ∫ x, ‖A x‖ ^ 2 ∂ν = N ^ 2 * (‖u‖ ^ 2 / d) := by
      have h1 : ∫ x, ⟪A x, A x⟫_ℂ ∂ν = ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [inner_self_eq_norm_sq_to_K]; push_cast; rfl
      have h2 := heq
      rw [hbevv, inner_self_eq_norm_sq_to_K u] at h2
      have h3 : ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) = ((N ^ 2 * (‖u‖ ^ 2 / d) : ℝ) : ℂ) := by
        rw [← h1]; refine h2.trans ?_
        have e : ((‖u‖ : ℝ) : ℂ) = (RCLike.ofReal ‖u‖ : ℂ) := rfl
        push_cast
        rw [← e]; ring
      exact_mod_cast h3
    have hintL : ∫ x, ‖L x‖ ^ 2 ∂ν = ‖u‖ ^ 2 / d := by
      have : ∫ x, ‖A x‖ ^ 2 ∂ν = N ^ 2 * ∫ x, ‖L x‖ ^ 2 ∂ν := by
        rw [← integral_const_mul]; exact integral_congr_ae hnA
      rw [this] at hintA
      exact mul_left_cancel₀ (by positivity) hintA
    unfold l2SG
    rw [← hintL, ofReal_integral_eq_lintegral_ofReal hIL (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  · intro v hv ξ x hx
    simp only [Afun]
    rw [hbe _ (mem_DD σ w hx) _ hv, rankOneInnerOperator_apply]
  · intro W hW1 hW2 hEq hL2 y hy
    obtain ⟨_, hconv⟩ := GlobalTheory.T.bessel_functional_standard_side k r σ w a μG d z c π μS hStd hSide ν hq W hW1 hW2 hEq hL2 y hy
    rw [hconv]
    have h : ∀ᵐ g ∂ν, be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g)) =
        ⟪l (σ (Matrix.of g) w), W (Matrix.of g)⟫_ℂ • l (σ y w) := by
      filter_upwards [hae] with g hg
      rw [hbe _ (mem_DD σ w hy) _ (mem_DD σ w hg), rankOneInnerOperator_apply]
    rw [integral_congr_ae h, integral_smul_const, smul_smul]

end GlobalTheory.SgInf.ProjLine
