import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
import Development.AbelianVarietyTheory.Proofs.HeightProofs.L2normLeIntegralKernelMulTranslateDiffStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalLowerDegreeKernelTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSpanningLieAlgebraCoefSqBoundStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryRightDerivRealLinearDirectionStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolyTranslationL2BoundStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactUnitaryKernelConcentratedNearOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

/- English proof (translation)
Introduce `a b h`. Conclude with `Subtype.ext (Subtype.ext (Units.ext h))`.
-/
theorem toMK_injective_of_gap {n : ℕ} (ε : Fin n → Bool) : Function.Injective (fun k : KG ε => toMK k) := by
  intro a b h
  exact Subtype.ext (Subtype.ext (Units.ext h))

/- English proof (translation)
The claim follows from `hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)`.
-/
theorem integrable_real_of_continuousK {n : ℕ} {ε : Fin n → Bool} {f : KG ε → ℝ} (hf : Continuous f) :
    Integrable f (muK ε) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/- English proof (translation)
Take `⟨Y, hY, hexp, hhs⟩` from `compact_exponential_surjective n ε (toMK k) k.2`. Establish `hk : expK ε Y 1 = k`. Apply `toMK_injective_of_gap ε` to reduce the goal to its premises. Use `show toMK (expK ε Y 1) = toMK k`. Rewrite using `[toMK_expK hY, Complex.ofReal_one, one_smul, hexp]`.

Take `⟨c, rfl, hc⟩` from `hcoef Y hY`. Establish `h1` using `GlobalTheory.T.poly_translation_l2_bound ε d p hp _ hY`. Rewrite `h1` using `[hk, GlobalTheory.T.compactUnitaryRightDeriv_real_linear_direction ε d p hp X c hX]`. Establish `hcont : ∀ j, Continuous (rder ε [X j] p)` using `fun j => continuous_of_mem (rder_mem_and_hasDerivAt ε d p hp (X j) (hX j)).1`. Establish `hpt : ∀ x, ‖(∑ j, (c j : ℂ) • rder ε [X j] p) x‖ ^ 2 ≤ (∑ j, c j ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2`.

Introduce `x`. Rewrite using `[Finset.sum_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `(norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))` and prove the remaining obligations. Simplify using `[norm_smul, Complex.norm_real]`.

Use `_ ≤ (∑ j, |c j| ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _`. Use `_ = (∑ j, c j ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2 := by simp [sq_abs]`. Establish `hint : ∀ j, Integrable (fun x => ‖rder ε [X j] p x‖ ^ 2) (muK ε)` using `fun j => integrable_real_of_continuousK ((hcont j).norm.pow 2)`. Establish `h2 : ∫ x, ‖(∑ j, (c j : ℂ) • rder ε [X j] p) x‖ ^ 2 ∂(muK ε) ≤ (∑ j, c j ^ 2) * ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε)`. Rewrite using `[← integral_finset_sum _ fun j _ => hint j, ← integral_const_mul]`.

Conclude with `integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) ((integrable_finset_sum _ fun j _ => hint j).const_mul _) (Filter.Eventually.of_forall hpt)`. Establish `hE : 0 ≤ ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε)` using `Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left hhs hC` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sq_dist_right_translate_le {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n) (hX : ∀ j, inK ε (X j))
    (C : ℝ) (hC : 0 ≤ C)
    (hcoef : ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j ∧ ∑ j, c j ^ 2 ≤ C * Formalism.REAL.hs Y)
    {d : ℕ} {p : KG ε → ℂ} (hp : p ∈ polyV ε d) (k : KG ε) :
    ∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε) ≤
      3 * C * Formalism.REAL.hs (toMK k - 1) * ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) := by
  obtain ⟨Y, hY, hexp, hhs⟩ := compact_exponential_surjective n ε (toMK k) k.2
  have hk : expK ε Y 1 = k := by
    apply toMK_injective_of_gap ε
    show toMK (expK ε Y 1) = toMK k
    rw [toMK_expK hY, Complex.ofReal_one, one_smul, hexp]
  obtain ⟨c, rfl, hc⟩ := hcoef Y hY
  have h1 := GlobalTheory.T.poly_translation_l2_bound ε d p hp _ hY
  rw [hk, GlobalTheory.T.compactUnitaryRightDeriv_real_linear_direction ε d p hp X c hX] at h1
  have hcont : ∀ j, Continuous (rder ε [X j] p) := fun j =>
    continuous_of_mem (rder_mem_and_hasDerivAt ε d p hp (X j) (hX j)).1
  have hpt : ∀ x, ‖(∑ j, (c j : ℂ) • rder ε [X j] p) x‖ ^ 2 ≤
      (∑ j, c j ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2 := by
    intro x
    rw [Finset.sum_apply]
    calc ‖∑ j, ((c j : ℂ) • rder ε [X j] p) x‖ ^ 2 ≤ (∑ j, |c j| * ‖rder ε [X j] p x‖) ^ 2 := by
          gcongr
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
          simp [norm_smul, Complex.norm_real]
      _ ≤ (∑ j, |c j| ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ j, c j ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2 := by simp [sq_abs]
  have hint : ∀ j, Integrable (fun x => ‖rder ε [X j] p x‖ ^ 2) (muK ε) := fun j =>
    integrable_real_of_continuousK ((hcont j).norm.pow 2)
  have h2 : ∫ x, ‖(∑ j, (c j : ℂ) • rder ε [X j] p) x‖ ^ 2 ∂(muK ε) ≤
      (∑ j, c j ^ 2) * ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) := by
    rw [← integral_finset_sum _ fun j _ => hint j, ← integral_const_mul]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
      ((integrable_finset_sum _ fun j _ => hint j).const_mul _) (Filter.Eventually.of_forall hpt)
  have hE : 0 ≤ ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ C * Formalism.REAL.hs (∑ j, (c j : ℂ) • X j) * ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) :=
        mul_le_mul_of_nonneg_right hc hE
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hhs hC
        nlinarith

/- English proof (translation)
Introduce `n ε r X hX hspan`. Take `⟨C3, hC3, hcoef⟩` from `GlobalTheory.T.exists_spanning_lieAlgebra_coef_sq_bound ε X hspan`. Take `⟨C4, hC4, hker⟩` from `GlobalTheory.T.exists_compactUnitaryKernel_concentrated_near_one ε`. Use `set A : ℝ := 3 * C3 * C4 ^ 2 with hA`. Establish `hA0 : 0 ≤ A` using `by positivity`.

Use `⟨1 / (A + 1), 1 / 2, by positivity, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `i hi p hp horth`. Use `set E := ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε) with hEdef`. Establish `hE : 0 ≤ E` using `Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity`. Take `⟨m, rfl⟩ : ∃ m, i = m + 1` from `⟨i - 1, by omega⟩`.

Take `⟨κ, hκc, hκ0, hκ1, hκmem, hκb⟩` from `hker m`. Establish `hpc : Continuous p` using `continuous_of_mem hp`. Establish `horth'` using `GlobalTheory.T.orthogonal_lowerDegree_kernel_translates ε (m + 1) p (fun k => (κ k : ℂ)) hκmem horth`. Establish `h1` using `GlobalTheory.T.sqrt_integral_norm_sq_le_integral_kernel_mul_translate ε p κ hpc hκc hκ0 hκ1 horth'`. Use `set P := ∫ x, ‖p x‖ ^ 2 ∂(muK ε) with hPdef`.

Establish `hP : 0 ≤ P` using `integral_nonneg fun x => by positivity`. Establish `hint : Integrable (fun k => κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1))) (muK ε)`. Use `integrable_real_of_continuousK ?_` and prove the remaining obligations. Use `(hκc.mul continuous_const).mul (Real.continuous_sqrt.comp ?_)` and prove the remaining obligations. Unfold `Formalism.REAL.hs`.

Use `fun_prop`. Establish `h2 : ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) ≤ ∫ k, κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε)`. Use `integral_mono_of_nonneg (Filter.Eventually.of_forall fun k => mul_nonneg (hκ0 k) (Real.sqrt_nonneg _)) hint (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[mul_assoc]`.

Use `mul_le_mul_of_nonneg_left ?_ (hκ0 k)` and prove the remaining obligations. Rewrite using `[← Real.sqrt_mul (by positivity)]`. Use `Real.sqrt_le_sqrt ?_` and prove the remaining obligations. Use `sq_dist_right_translate_le ε X hX C3 hC3 hcoef hp k` as an intermediate fact. Use polynomial arithmetic with `[show 0 ≤ Formalism.REAL.hs (toMK k - 1) from by unfold Formalism.REAL.hs; positivity]`.

Establish `h3 : ∫ k, κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) = Real.sqrt (3 * C3 * E) * ∫ k, κ k * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε)`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmi : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ)` using `by push_cast; ring`. Rewrite `hκb` using `[hmi]`. Use `set I : ℝ := ((m + 1 : ℕ) : ℝ) with hIdef`. Establish `hI : 1 ≤ I` using `by rw [hIdef]; exact_mod_cast Nat.succ_pos m`. Establish `hsq : Real.sqrt P ≤ Real.sqrt (3 * C3 * E) * (C4 * I ^ (-(1 / 4 : ℝ)))`.

Combine the equalities or inequalities in the displayed calculation. Establish `hq : 0 ≤ I ^ (-(1 / 4 : ℝ))` using `Real.rpow_nonneg (by linarith) _`. Establish `hPle : P ≤ 3 * C3 * E * C4 ^ 2 * (I ^ (-(1 / 4 : ℝ))) ^ 2`. Establish `h` using `pow_le_pow_left₀ (Real.sqrt_nonneg P) hsq 2`. Rewrite `h` using `[Real.sq_sqrt hP, mul_pow, Real.sq_sqrt (by positivity), mul_pow]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpow : (I ^ (-(1 / 4 : ℝ))) ^ 2 * I ^ (1 / 2 : ℝ) = 1`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_add (by linarith)]`. Evaluate the numerical expressions. Establish `hIp : 0 ≤ I ^ (1 / 2 : ℝ)` using `Real.rpow_nonneg (by linarith) _`.

Establish `key : I ^ (1 / 2 : ℝ) * P ≤ A * E`. Combine the equalities or inequalities in the displayed calculation. Establish `hA1 : 0 < A + 1` using `by linarith`. Rewrite using `[div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_iff₀ hA1]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem spectral_gap_rder : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) →
    (∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j) → ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
    ∀ i : ℕ, 1 ≤ i → ∀ p ∈ polyV ε i, (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) →
    c * (i : ℝ) ^ α * ∫ k, ‖p k‖ ^ 2 ∂(muK ε) ≤ ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε) := by
  intro n ε r X hX hspan
  obtain ⟨C3, hC3, hcoef⟩ := GlobalTheory.T.exists_spanning_lieAlgebra_coef_sq_bound ε X hspan
  obtain ⟨C4, hC4, hker⟩ := GlobalTheory.T.exists_compactUnitaryKernel_concentrated_near_one ε
  set A : ℝ := 3 * C3 * C4 ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨1 / (A + 1), 1 / 2, by positivity, by norm_num, ?_⟩
  intro i hi p hp horth
  set E := ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε) with hEdef
  have hE : 0 ≤ E := Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  obtain ⟨κ, hκc, hκ0, hκ1, hκmem, hκb⟩ := hker m
  have hpc : Continuous p := continuous_of_mem hp
  have horth' := GlobalTheory.T.orthogonal_lowerDegree_kernel_translates ε (m + 1) p (fun k => (κ k : ℂ)) hκmem horth
  have h1 := GlobalTheory.T.sqrt_integral_norm_sq_le_integral_kernel_mul_translate ε p κ hpc hκc hκ0 hκ1 horth'
  set P := ∫ x, ‖p x‖ ^ 2 ∂(muK ε) with hPdef
  have hP : 0 ≤ P := integral_nonneg fun x => by positivity
  have hint : Integrable (fun k => κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1))) (muK ε) := by
    refine integrable_real_of_continuousK ?_
    refine (hκc.mul continuous_const).mul (Real.continuous_sqrt.comp ?_)
    unfold Formalism.REAL.hs
    fun_prop
  have h2 : ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) ≤
      ∫ k, κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun k => mul_nonneg (hκ0 k) (Real.sqrt_nonneg _))
      hint (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hκ0 k)
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have := sq_dist_right_translate_le ε X hX C3 hC3 hcoef hp k
    nlinarith [show 0 ≤ Formalism.REAL.hs (toMK k - 1) from by unfold Formalism.REAL.hs; positivity]
  have h3 : ∫ k, κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) =
      Real.sqrt (3 * C3 * E) * ∫ k, κ k * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) := by
    rw [← integral_const_mul]; congr 1; funext k; ring
  have hmi : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hmi] at hκb
  set I : ℝ := ((m + 1 : ℕ) : ℝ) with hIdef
  have hI : 1 ≤ I := by rw [hIdef]; exact_mod_cast Nat.succ_pos m
  have hsq : Real.sqrt P ≤ Real.sqrt (3 * C3 * E) * (C4 * I ^ (-(1 / 4 : ℝ))) := by
    calc Real.sqrt P ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_left hκb (Real.sqrt_nonneg _)
  have hq : 0 ≤ I ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hPle : P ≤ 3 * C3 * E * C4 ^ 2 * (I ^ (-(1 / 4 : ℝ))) ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg P) hsq 2
    rw [Real.sq_sqrt hP, mul_pow, Real.sq_sqrt (by positivity), mul_pow] at h
    linarith
  have hpow : (I ^ (-(1 / 4 : ℝ))) ^ 2 * I ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_add (by linarith)]
    norm_num
  have hIp : 0 ≤ I ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have key : I ^ (1 / 2 : ℝ) * P ≤ A * E := by
    calc I ^ (1 / 2 : ℝ) * P ≤ I ^ (1 / 2 : ℝ) * (3 * C3 * E * C4 ^ 2 * (I ^ (-(1 / 4 : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_left hPle hIp
      _ = A * E * ((I ^ (-(1 / 4 : ℝ))) ^ 2 * I ^ (1 / 2 : ℝ)) := by rw [hA]; ring
      _ = A * E := by rw [hpow, mul_one]
  have hA1 : 0 < A + 1 := by linarith
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_iff₀ hA1]
  nlinarith

end GlobalTheory.KFourier

end
