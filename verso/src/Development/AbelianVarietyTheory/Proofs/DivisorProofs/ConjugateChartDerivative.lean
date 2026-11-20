import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
open Filter Topology
open GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexConjugate

namespace GlobalTheory.ConjDeriv

open GlobalTheory.ConjChart

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjCoord_apply (d : ℕ) (w : V d) (i : Fin d) : conjCoord d w i = conj (w i) := rfl

/- English proof (translation)
Use extensionality with `i`. Simplify using `[conjCoord_apply, mul_comm]`.
-/
theorem conjCoord_smul (d : ℕ) (c : ℂ) (w : V d) : conjCoord d (c • w) = conj c • conjCoord d w := by
  ext i
  simp [conjCoord_apply, mul_comm]

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [conjCoord_apply, GlobalTheory.GoodMetric.coordVec, EuclideanSpace.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem conjCoord_coordVec {d : ℕ} (b : Fin d) : conjCoord d (GlobalTheory.GoodMetric.coordVec b) = GlobalTheory.GoodMetric.coordVec b := by
  ext i
  simp only [conjCoord_apply, GlobalTheory.GoodMetric.coordVec, EuclideanSpace.single_apply]
  split_ifs <;> simp

noncomputable def conjLI (d : ℕ) : V d ≃ₗᵢ[ℝ] V d :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin d => Complex.conjLIE)

/- English proof (translation)
Use extensionality with `i`. Simplify using `[conjLI, conjCoord_apply]`.
-/
theorem conjLI_apply (d : ℕ) (w : V d) : conjLI d w = conjCoord d w := by
  ext i
  simp [conjLI, conjCoord_apply]

/- English proof (translation)
Use `set L := fderiv ℂ G (conjCoord n v)`. Set `R : V n →L[ℝ] V m` to `(conjLI m).toContinuousLinearEquiv.toContinuousLinearMap.comp ((L.restrictScalars ℝ).comp (conjLI n).toContinuousLinearEquiv.toContinuousLinearMap)`. Establish `hR : ∀ ξ, R ξ = conjCoord m (L (conjCoord n ξ))`. Introduce `ξ`. Simplify using `[R, conjLI_apply]`.

Set `L' : V n →L[ℂ] V m` to `{ toFun := R map_add' := R.map_add map_smul' := fun c ξ => by`. Simplify using `only [hR, conjCoord_smul, map_smul, RingHom.id_apply, Complex.conj_conj]`. Use `cont := R.continuous }`. Use `⟨L', ?_, fun ξ => hR ξ⟩` and prove the remaining obligations. Use `hasFDerivAt_of_restrictScalars ℝ (g' := R) ?_ (by ext ξ; rfl)` and prove the remaining obligations.

Establish `h1 : HasFDerivAt (conjLI n) ((conjLI n).toContinuousLinearEquiv.toContinuousLinearMap) v` using `(conjLI n).toContinuousLinearEquiv.hasFDerivAt`. Establish `h2 : HasFDerivAt G (L.restrictScalars ℝ) (conjLI n v)`. Rewrite using `[conjLI_apply]`. Conclude with `hG.hasFDerivAt.restrictScalars ℝ`. Establish `h3 : HasFDerivAt (conjLI m) ((conjLI m).toContinuousLinearEquiv.toContinuousLinearMap) (G (conjLI n v))` using `(conjLI m).toContinuousLinearEquiv.hasFDerivAt`.

Establish `h4` using `h3.comp v (h2.comp v h1)`. Establish `e : (fun w => conjCoord m (G (conjCoord n w))) = (conjLI m) ∘ G ∘ (conjLI n)`. Use function extensionality and compare the values at `w`. Simplify using `[conjLI_apply]`. Rewrite using `[e]`.

Conclude with `h4`.
-/
theorem hasFDerivAt_conj_conj {n m : ℕ} {G : V n → V m} {v : V n}
    (hG : DifferentiableAt ℂ G (conjCoord n v)) :
    ∃ L' : V n →L[ℂ] V m, HasFDerivAt (fun w => conjCoord m (G (conjCoord n w))) L' v ∧
      ∀ ξ, L' ξ = conjCoord m (fderiv ℂ G (conjCoord n v) (conjCoord n ξ)) := by
  set L := fderiv ℂ G (conjCoord n v)
  let R : V n →L[ℝ] V m := (conjLI m).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((L.restrictScalars ℝ).comp (conjLI n).toContinuousLinearEquiv.toContinuousLinearMap)
  have hR : ∀ ξ, R ξ = conjCoord m (L (conjCoord n ξ)) := by
    intro ξ
    simp [R, conjLI_apply]
  let L' : V n →L[ℂ] V m :=
    { toFun := R
      map_add' := R.map_add
      map_smul' := fun c ξ => by
        simp only [hR, conjCoord_smul, map_smul, RingHom.id_apply, Complex.conj_conj]
      cont := R.continuous }
  refine ⟨L', ?_, fun ξ => hR ξ⟩
  refine hasFDerivAt_of_restrictScalars ℝ (g' := R) ?_ (by ext ξ; rfl)
  have h1 : HasFDerivAt (conjLI n) ((conjLI n).toContinuousLinearEquiv.toContinuousLinearMap) v :=
    (conjLI n).toContinuousLinearEquiv.hasFDerivAt
  have h2 : HasFDerivAt G (L.restrictScalars ℝ) (conjLI n v) := by
    rw [conjLI_apply]
    exact hG.hasFDerivAt.restrictScalars ℝ
  have h3 : HasFDerivAt (conjLI m) ((conjLI m).toContinuousLinearEquiv.toContinuousLinearMap) (G (conjLI n v)) :=
    (conjLI m).toContinuousLinearEquiv.hasFDerivAt
  have h4 := h3.comp v (h2.comp v h1)
  have e : (fun w => conjCoord m (G (conjCoord n w))) = (conjLI m) ∘ G ∘ (conjLI n) := by
    funext w
    simp [conjLI_apply]
  rw [e]
  exact h4

end GlobalTheory.ConjDeriv

/- English proof (translation)
Introduce `n m G G' v hG hG' b a`. Take `⟨L', hL', hv⟩` from `GlobalTheory.ConjDeriv.hasFDerivAt_conj_conj hG`. Rewrite using `[hG'.fderiv_eq, hL'.fderiv, hv, GlobalTheory.ConjDeriv.conjCoord_coordVec, GlobalTheory.ConjDeriv.conjCoord_apply]`.
-/
theorem GlobalTheory.ConjDeriv.fderiv_conj_conj_coordVec : ∀ (n m : ℕ) (G G' : V n → V m) (v : V n), DifferentiableAt ℂ G (GlobalTheory.ConjChart.conjCoord n v) → (G' =ᶠ[𝓝 v] fun w => GlobalTheory.ConjChart.conjCoord m (G (GlobalTheory.ConjChart.conjCoord n w))) → ∀ (b : Fin n) (a : Fin m), fderiv ℂ G' v (GlobalTheory.GoodMetric.coordVec b) a = conj (fderiv ℂ G (GlobalTheory.ConjChart.conjCoord n v) (GlobalTheory.GoodMetric.coordVec b) a) := by
  intro n m G G' v hG hG' b a
  obtain ⟨L', hL', hv⟩ := GlobalTheory.ConjDeriv.hasFDerivAt_conj_conj hG
  rw [hG'.fderiv_eq, hL'.fderiv, hv, GlobalTheory.ConjDeriv.conjCoord_coordVec, GlobalTheory.ConjDeriv.conjCoord_apply]
