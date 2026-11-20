import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

/- English proof (translation)
Introduce `hL n _ _ μ _ E ι ι' _ _ c c' ks ks' k k' hks hks' hk hk' x hx`. Use `haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V`. Establish `hval : ∀ y : G n, y.val ∈ GLs n` using `fun y => by`. Use `(Matrix.isUnit_iff_isUnit_det _).1 y.isUnit` as an intermediate fact. Conclude with `this.ne_zero`.

Establish `hcv : Continuous (fun y : G n => y.val)` using `Units.continuous_val`. Establish `hcinv : Continuous (fun y : G n => (y⁻¹ : G n).val)` using `Units.continuous_val.comp continuous_inv`. Establish `hmem : ∀ y : G n, (y⁻¹ : G n).val * x ∈ GLs n`. Introduce `y`. Establish `h1 : ((y⁻¹ : G n).val).det ≠ 0` using `hval _`.

Express the relevant statement in the definitionally equal form `((y⁻¹ : G n).val * x).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero h1 hx`. Establish `hint : ∀ i j, Integrable (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) μ`. Introduce `i j`.

Take `⟨hc, R, hR⟩` from `hks i`. Establish `hcont : Continuous (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x))`. Establish `h1 : Continuous (fun y : G n => ks i y.val)` using `hc.comp_continuous hcv hval`. Establish `h2 : Continuous (fun y : G n => ks' j ((y⁻¹ : G n).val * x))` using `(hks' j).1.comp_continuous (hcinv.mul continuous_const) hmem`. Conclude with `h1.mul h2`.

Establish `hsupp : HasCompactSupport (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x))`. Use `HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hy' : R < lg y.val` using `not_le.1 hy`. Simplify using `[hR y.val (hval y) hy']`.

Conclude with `hcont.integrable_of_hasCompactSupport hsupp`. Establish `hpt : (fun y : G n => k y.val * k' ((y⁻¹ : G n).val * x)) = fun y : G n => ∑ i, ∑ j, (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x))`. Use function extensionality and compare the values at `y`. Rewrite using `[hk y.val (hval y), hk' _ (hmem y), Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_smul_comm]`. Establish `hi : ∀ i ∈ (Finset.univ : Finset ι), Integrable (fun y : G n => ∑ j, (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x))) μ` using `fun i _ => integrable_finset_sum _ fun j _ => (hint i j).smul (c i * c' j)`. Unfold `conv`.

Rewrite using `[hpt, integral_finset_sum _ hi]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hj : ∀ j ∈ (Finset.univ : Finset ι'), Integrable (fun y : G n => (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x))) μ` using `fun j _ => (hint i j).smul (c i * c' j)`. Rewrite using `[integral_finset_sum _ hj]`. Conclude with `Finset.sum_congr rfl fun j _ => integral_smul (c i * c' j) _`.
-/
theorem conv_eq_sum_of_kernels : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) {ι ι' : Type} [Fintype ι] [Fintype ι'] (c : ι → ℂ) (c' : ι' → ℂ) (ks : ι → Mat n → (E.V →L[ℂ] E.V)) (ks' : ι' → Mat n → (E.V →L[ℂ] E.V)) (k k' : Mat n → (E.V →L[ℂ] E.V)), (∀ i, KReg (ks i)) → (∀ j, KReg (ks' j)) → (∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) → (∀ y ∈ GLs n, k' y = ∑ j, c' j • ks' j y) → ∀ x ∈ GLs n, conv μ E k k' x = ∑ i, ∑ j, (c i * c' j) • conv μ E (ks i) (ks' j) x := by
  intro hL n _ _ μ _ E ι ι' _ _ c c' ks ks' k k' hks hks' hk hk' x hx
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
  have hcinv : Continuous (fun y : G n => (y⁻¹ : G n).val) := Units.continuous_val.comp continuous_inv
  have hmem : ∀ y : G n, (y⁻¹ : G n).val * x ∈ GLs n := by
    intro y
    have h1 : ((y⁻¹ : G n).val).det ≠ 0 := hval _
    change ((y⁻¹ : G n).val * x).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 hx
  have hint : ∀ i j, Integrable (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) μ := by
    intro i j
    obtain ⟨hc, R, hR⟩ := hks i
    have hcont : Continuous (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
      have h1 : Continuous (fun y : G n => ks i y.val) := hc.comp_continuous hcv hval
      have h2 : Continuous (fun y : G n => ks' j ((y⁻¹ : G n).val * x)) :=
        (hks' j).1.comp_continuous (hcinv.mul continuous_const) hmem
      exact h1.mul h2
    have hsupp : HasCompactSupport (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
      refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_
      intro y hy
      have hy' : R < lg y.val := not_le.1 hy
      simp [hR y.val (hval y) hy']
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hpt : (fun y : G n => k y.val * k' ((y⁻¹ : G n).val * x))
      = fun y : G n => ∑ i, ∑ j, (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
    funext y
    rw [hk y.val (hval y), hk' _ (hmem y), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  have hi : ∀ i ∈ (Finset.univ : Finset ι), Integrable
      (fun y : G n => ∑ j, (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x))) μ :=
    fun i _ => integrable_finset_sum _ fun j _ => (hint i j).smul (c i * c' j)
  unfold conv
  rw [hpt, integral_finset_sum _ hi]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hj : ∀ j ∈ (Finset.univ : Finset ι'), Integrable
      (fun y : G n => (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x))) μ :=
    fun j _ => (hint i j).smul (c i * c' j)
  rw [integral_finset_sum _ hj]
  exact Finset.sum_congr rfl fun j _ => integral_smul (c i * c' j) _

end GlobalTheory.CompanionTheory.WaveMult
