import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementC

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace FourierIntegralBound

open Real

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.OneAddPowLeTwoPowMul.main t ht N`.
-/
lemma one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) :=
  _root_.UpperTheory.Reformulated.B.OneAddPowLeTwoPowMul.main t ht N

/- English proof (translation)
Establish `hs : 0 ≤ ∑ i, |z i| ^ N` using `Finset.sum_nonneg (fun i _ => by positivity)`. Break down `isEmpty_or_nonempty (Fin d) with h | h` into its components or cases. Establish `: ‖z‖ ≤ 1` using `(pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => isEmptyElim i)`. Establish `h0 : ‖z‖ ^ N ≤ 1` using `pow_le_one₀ (norm_nonneg _) this`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨i0, -, hi0⟩` from `Finset.exists_max_image Finset.univ (fun i => |z i|) Finset.univ_nonempty`. Establish `h1 : ‖z‖ ≤ |z i0|` using `(pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 (fun i => by`. Rewrite using `[Real.norm_eq_abs]`. Conclude with `hi0 i (Finset.mem_univ _))`. Establish `h2 : ‖z‖ ^ N ≤ |z i0| ^ N` using `pow_le_pow_left₀ (norm_nonneg _) h1 N`.

Establish `h3 : |z i0| ^ N ≤ ∑ i, |z i| ^ N` using `Finset.single_le_sum (f := fun i => |z i| ^ N) (fun i _ => by positivity) (Finset.mem_univ i0)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma pi_pow_le {d : ℕ} (z : Fin d → ℝ) (N : ℕ) : ‖z‖ ^ N ≤ 1 + ∑ i, |z i| ^ N := by
  have hs : 0 ≤ ∑ i, |z i| ^ N := Finset.sum_nonneg (fun i _ => by positivity)
  rcases isEmpty_or_nonempty (Fin d) with h | h
  · have : ‖z‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => isEmptyElim i)
    have h0 : ‖z‖ ^ N ≤ 1 := pow_le_one₀ (norm_nonneg _) this
    linarith
  · obtain ⟨i0, -, hi0⟩ :=
      Finset.exists_max_image Finset.univ (fun i => |z i|) Finset.univ_nonempty
    have h1 : ‖z‖ ≤ |z i0| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 (fun i => by
      rw [Real.norm_eq_abs]; exact hi0 i (Finset.mem_univ _))
    have h2 : ‖z‖ ^ N ≤ |z i0| ^ N := pow_le_pow_left₀ (norm_nonneg _) h1 N
    have h3 : |z i0| ^ N ≤ ∑ i, |z i| ^ N :=
      Finset.single_le_sum (f := fun i => |z i| ^ N) (fun i _ => by positivity) (Finset.mem_univ i0)
    linarith

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def sc (β : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V →L[ℝ] ℝ := (2 * π)⁻¹ • β

/- English proof (translation)
Simplify using `[sc]`.
-/
lemma sc_apply (β : V →L[ℝ] V →L[ℝ] ℝ) (x y : V) : sc β x y = (2 * π)⁻¹ * β x y := by
  simp [sc]

/- English proof (translation)
Use extensionality with `y`. Unfold `FT VectorFourier.fourierIntegral`. Use `congr 1`. Use extensionality with `x`. Rewrite using `[Circle.smul_def, Real.fourierChar_apply]`.

Use `congr 2`. Rewrite using `[show (sc β).toLinearMap₁₂ x y = sc β x y from rfl, sc_apply]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
lemma FT_eq [MeasurableSpace V] {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (μ : Measure V) (β : V →L[ℝ] V →L[ℝ] ℝ) (F : V → X) :
    FT μ β F = VectorFourier.fourierIntegral Real.fourierChar μ (sc β).toLinearMap₁₂ F := by
  ext y
  unfold FT VectorFourier.fourierIntegral
  congr 1
  ext x
  rw [Circle.smul_def, Real.fourierChar_apply]
  congr 2
  rw [show (sc β).toLinearMap₁₂ x y = sc β x y from rfl, sc_apply]
  push_cast
  field_simp

/- English proof (translation)
Set `b` to `Module.finBasis ℝ V`. Set `T : V →ₗ[ℝ] (Fin (Module.finrank ℝ V) → ℝ)` to `LinearMap.pi (fun i => ((β (b i) : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ))`. Establish `hT : ∀ y, T y = fun i => β (b i) y` using `fun y => rfl`. Establish `hker : LinearMap.ker T = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`.

Introduce `y hy`. Apply `hβ y` to reduce the goal to its premises. Establish `h1 : ∀ i, β (b i) y = 0` using `fun i => by`. Use `congrFun hy i` as an intermediate fact. Rewrite `this` using `[hT]`.

Simplify using `using this`. Establish `h2 : ((β.flip y : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ) = 0` using `b.ext (fun i => by simpa using h1 i)`. Introduce `x`. Use `LinearMap.congr_fun h2 x` as an intermediate fact. Simplify using `using this`.

Take `⟨K, -, hK⟩` from `T.exists_antilipschitzWith hker`. Use `⟨_, b, K, K.2, fun y => ?_⟩` and prove the remaining obligations. Use `hK.le_mul_dist y 0` as an intermediate fact. Rewrite `this` using `[map_zero, dist_zero_right, dist_zero_right]`. Conclude with `this`.
-/
lemma exists_strictHenselian_absolutely_closed_local_ring [FiniteDimensional ℝ V] (β : V →L[ℝ] V →L[ℝ] ℝ)
    (hβ : ∀ y, (∀ x, β x y = 0) → y = 0) :
    ∃ (d : ℕ) (b : Fin d → V) (K : ℝ), 0 ≤ K ∧
      ∀ y, ‖y‖ ≤ K * ‖(fun i => β (b i) y : Fin d → ℝ)‖ := by
  let b := Module.finBasis ℝ V
  let T : V →ₗ[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
    LinearMap.pi (fun i => ((β (b i) : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ))
  have hT : ∀ y, T y = fun i => β (b i) y := fun y => rfl
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    apply hβ y
    have h1 : ∀ i, β (b i) y = 0 := fun i => by
      have := congrFun hy i
      rw [hT] at this
      simpa using this
    have h2 : ((β.flip y : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ) = 0 :=
      b.ext (fun i => by simpa using h1 i)
    intro x
    have := LinearMap.congr_fun h2 x
    simpa using this
  obtain ⟨K, -, hK⟩ := T.exists_antilipschitzWith hker
  refine ⟨_, b, K, K.2, fun y => ?_⟩
  have := hK.le_mul_dist y 0
  rw [map_zero, dist_zero_right, dist_zero_right] at this
  exact this

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

omit [FiniteDimensional ℝ V] in
/- English proof (translation)
Apply `Continuous.integrable_of_hasCompactSupport` to reduce the goal to its premises. Conclude with `(continuous_norm.pow k).mul (hF.continuous_iteratedFDeriv (mod_cast le_top)).norm`. Conclude with `(hc.iteratedFDeriv n).norm.mul_left`.
-/
lemma integ {F : V → X} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (μ : Measure V)
    [IsFiniteMeasureOnCompacts μ] (k n : ℕ) :
    Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n F v‖) μ := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_norm.pow k).mul (hF.continuous_iteratedFDeriv (mod_cast le_top)).norm
  · exact (hc.iteratedFDeriv n).norm.mul_left

/- English proof (translation)
Use `⟨(2 * π) ^ n * ((2 * π * ‖sc β‖) ^ 0 * (2 * ((0 : ℕ) : ℝ) + 2) ^ n * ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1), ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 F v‖ ∂μ), fun v y => ?_⟩` and prove the remaining obligations. Establish `H` using `VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (L := sc β) (μ := μ) (K := ⊤) (N := ⊤) hF (fun k n _ _ => integ hF hc μ k n) (k := 0) (n := n) le_top le_top v y`. Rewrite `H` using `[norm_iteratedFDeriv_zero, ← FT_eq]`. Establish `e : |β v y| = 2 * π * |sc β v y|`. Rewrite using `[sc_apply, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹)]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e, mul_pow, mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma pw_bd (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →L[ℝ] V →L[ℝ] ℝ) {F : V → X}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (n : ℕ) :
    ∃ B : ℝ, ∀ v y, |β v y| ^ n * ‖FT μ β F y‖ ≤ ‖v‖ ^ n * B := by
  refine ⟨(2 * π) ^ n * ((2 * π * ‖sc β‖) ^ 0 * (2 * ((0 : ℕ) : ℝ) + 2) ^ n *
      ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 F v‖ ∂μ), fun v y => ?_⟩
  have H := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (L := sc β) (μ := μ)
    (K := ⊤) (N := ⊤) hF (fun k n _ _ => integ hF hc μ k n) (k := 0) (n := n) le_top le_top v y
  rw [norm_iteratedFDeriv_zero, ← FT_eq] at H
  have e : |β v y| = 2 * π * |sc β v y| := by
    rw [sc_apply, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹)]
    field_simp
  rw [e, mul_pow, mul_assoc]
  calc (2 * π) ^ n * (|sc β v y| ^ n * ‖FT μ β F y‖)
      ≤ (2 * π) ^ n * (‖v‖ ^ n * (2 * π * ‖sc β‖) ^ 0 * (2 * ((0 : ℕ) : ℝ) + 2) ^ n *
          ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
            ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 F v‖ ∂μ) := by gcongr
    _ = _ := by ring

end FourierIntegralBound

open FourierIntegralBound in
/- English proof (translation)
Unfold `S4 ForV`. Introduce `V _ _ _ _ _ μ _ β hβ X _ _ _ F hF hc`. Use `⟨?_, fun N => ?_⟩` and prove the remaining obligations. Rewrite using `[FT_eq]`. Conclude with `VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by apply (sc β).continuous₂) (hF.continuous.integrable_of_hasCompactSupport hc)`.

Take `⟨d, b, K, hK0, hK⟩` from `exists_strictHenselian_absolutely_closed_local_ring β hβ`. Take `⟨A, hA⟩` from `pw_bd μ β hF hc 0`. Take `⟨B, hB⟩` from `pw_bd μ β hF hc N`. Use `⟨2 ^ N * (A + K ^ N * (A + ∑ i, ‖b i‖ ^ N * B)), fun y => ?_⟩` and prove the remaining obligations. Establish `hA' : ‖FT μ β F y‖ ≤ A` using `by simpa using hA 0 y`.

Establish `hy` using `pi_pow_le (fun i => β (b i) y) N`. Establish `h1 : ‖y‖ ^ N ≤ K ^ N * (1 + ∑ i, |β (b i) y| ^ N)`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : (1 + ∑ i, |β (b i) y| ^ N) * ‖FT μ β F y‖ ≤ A + ∑ i, ‖b i‖ ^ N * B`. Rewrite using `[add_mul, Finset.sum_mul, one_mul]`.

Conclude with `add_le_add hA' (Finset.sum_le_sum fun i _ => hB (b i) y)`. Establish `hFn` using `norm_nonneg (FT μ β F y)`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left (add_le_add hA' ?_) (by positivity)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem valuation_bound_of_three : S4 := by
  unfold S4 ForV
  intro V _ _ _ _ _ μ _ β hβ X _ _ _ F hF hc
  refine ⟨?_, fun N => ?_⟩
  · rw [FT_eq]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by apply (sc β).continuous₂) (hF.continuous.integrable_of_hasCompactSupport hc)
  · obtain ⟨d, b, K, hK0, hK⟩ := exists_strictHenselian_absolutely_closed_local_ring β hβ
    obtain ⟨A, hA⟩ := pw_bd μ β hF hc 0
    obtain ⟨B, hB⟩ := pw_bd μ β hF hc N
    refine ⟨2 ^ N * (A + K ^ N * (A + ∑ i, ‖b i‖ ^ N * B)), fun y => ?_⟩
    have hA' : ‖FT μ β F y‖ ≤ A := by simpa using hA 0 y
    have hy := pi_pow_le (fun i => β (b i) y) N
    have h1 : ‖y‖ ^ N ≤ K ^ N * (1 + ∑ i, |β (b i) y| ^ N) := by
      calc ‖y‖ ^ N ≤ (K * ‖(fun i => β (b i) y : Fin d → ℝ)‖) ^ N :=
            pow_le_pow_left₀ (norm_nonneg _) (hK y) N
        _ = K ^ N * ‖(fun i => β (b i) y : Fin d → ℝ)‖ ^ N := mul_pow _ _ _
        _ ≤ _ := by gcongr
    have h3 : (1 + ∑ i, |β (b i) y| ^ N) * ‖FT μ β F y‖ ≤ A + ∑ i, ‖b i‖ ^ N * B := by
      rw [add_mul, Finset.sum_mul, one_mul]
      exact add_le_add hA' (Finset.sum_le_sum fun i _ => hB (b i) y)
    have hFn := norm_nonneg (FT μ β F y)
    calc (1 + ‖y‖) ^ N * ‖FT μ β F y‖ ≤ 2 ^ N * (1 + ‖y‖ ^ N) * ‖FT μ β F y‖ := by
          gcongr; exact one_add_pow_le _ (norm_nonneg _) N
      _ = 2 ^ N * (‖FT μ β F y‖ + ‖y‖ ^ N * ‖FT μ β F y‖) := by ring
      _ ≤ 2 ^ N * (A + K ^ N * (A + ∑ i, ‖b i‖ ^ N * B)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hA' ?_) (by positivity)
          calc ‖y‖ ^ N * ‖FT μ β F y‖
              ≤ K ^ N * (1 + ∑ i, |β (b i) y| ^ N) * ‖FT μ β F y‖ := by gcongr
            _ = K ^ N * ((1 + ∑ i, |β (b i) y| ^ N) * ‖FT μ β F y‖) := by ring
            _ ≤ _ := by gcongr

end PositivityTheory.jumpWindows

end
