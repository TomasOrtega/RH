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
Introduce `hL n _ _ μ _ E ι _ c ks k f hks hk hf x hx`. Use `haveI := FiniteDimensional.complete ℂ E.V`. Establish `hval : ∀ y : G n, y.val ∈ GLs n` using `fun y => by`. Use `(Matrix.isUnit_iff_isUnit_det _).1 y.isUnit` as an intermediate fact. Conclude with `this.ne_zero`.

Establish `hcv : Continuous (fun y : G n => y.val)` using `Units.continuous_val`. Establish `hmul : ∀ y : G n, x * y.val ∈ GLs n` using `fun y => by`. Establish `h1 : x.det ≠ 0` using `hx`. Establish `h2 : y.val.det ≠ 0` using `hval y`. Express the relevant statement in the definitionally equal form `(x * y.val).det ≠ 0`.

Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero h1 h2`. Establish `hint : ∀ i, Integrable (fun y : G n => ks i y.val (f (x * y.val))) μ`. Introduce `i`. Take `⟨hc, R, hR⟩` from `hks i`.

Establish `hcont : Continuous (fun y : G n => ks i y.val (f (x * y.val)))`. Establish `h1 : Continuous (fun y : G n => ks i y.val)` using `hc.comp_continuous hcv hval`. Establish `h2 : Continuous (fun y : G n => f (x * y.val))` using `hf.comp_continuous (continuous_const.mul hcv) hmul`. Conclude with `h1.clm_apply h2`. Establish `hsupp : HasCompactSupport (fun y : G n => ks i y.val (f (x * y.val)))`.

Use `HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hy' : R < lg y.val` using `not_le.1 hy`. Simplify using `[hR y.val (hval y) hy']`. Conclude with `hcont.integrable_of_hasCompactSupport hsupp`.

Unfold `act`. Establish `hpt : (fun y : G n => k y.val (f (x * y.val))) = fun y : G n => ∑ i, c i • ks i y.val (f (x * y.val))`. Use function extensionality and compare the values at `y`. Rewrite using `[hk y.val (hval y)]`. Simplify using `[ContinuousLinearMap.sum_apply]`.

Establish `hi : ∀ i ∈ (Finset.univ : Finset ι), Integrable (fun y : G n => c i • ks i y.val (f (x * y.val))) μ` using `fun i _ => (hint i).smul (c i)`. Rewrite using `[hpt, integral_finset_sum _ hi]`. Conclude with `Finset.sum_congr rfl (fun i _ => integral_smul (c i) _)`.
-/
theorem act_eq_sum_of_kernel : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) {ι : Type} [Fintype ι] (c : ι → ℂ) (ks : ι → Mat n → (E.V →L[ℂ] E.V)) (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), (∀ i, KReg (ks i)) → (∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) → ContinuousOn f (GLs n) → ∀ x ∈ GLs n, act μ E k f x = ∑ i, c i • act μ E (ks i) f x := by
  intro hL n _ _ μ _ E ι _ c ks k f hks hk hf x hx
  haveI := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
  have hmul : ∀ y : G n, x * y.val ∈ GLs n := fun y => by
    have h1 : x.det ≠ 0 := hx
    have h2 : y.val.det ≠ 0 := hval y
    change (x * y.val).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 h2
  have hint : ∀ i, Integrable (fun y : G n => ks i y.val (f (x * y.val))) μ := by
    intro i
    obtain ⟨hc, R, hR⟩ := hks i
    have hcont : Continuous (fun y : G n => ks i y.val (f (x * y.val))) := by
      have h1 : Continuous (fun y : G n => ks i y.val) :=
        hc.comp_continuous hcv hval
      have h2 : Continuous (fun y : G n => f (x * y.val)) :=
        hf.comp_continuous (continuous_const.mul hcv) hmul
      exact h1.clm_apply h2
    have hsupp : HasCompactSupport (fun y : G n => ks i y.val (f (x * y.val))) := by
      refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_
      intro y hy
      have hy' : R < lg y.val := not_le.1 hy
      simp [hR y.val (hval y) hy']
    exact hcont.integrable_of_hasCompactSupport hsupp
  unfold act
  have hpt : (fun y : G n => k y.val (f (x * y.val)))
      = fun y : G n => ∑ i, c i • ks i y.val (f (x * y.val)) := by
    funext y
    rw [hk y.val (hval y)]
    simp [ContinuousLinearMap.sum_apply]
  have hi : ∀ i ∈ (Finset.univ : Finset ι),
      Integrable (fun y : G n => c i • ks i y.val (f (x * y.val))) μ :=
    fun i _ => (hint i).smul (c i)
  rw [hpt, integral_finset_sum _ hi]
  exact Finset.sum_congr rfl (fun i _ => integral_smul (c i) _)

end GlobalTheory.CompanionTheory.WaveMult
