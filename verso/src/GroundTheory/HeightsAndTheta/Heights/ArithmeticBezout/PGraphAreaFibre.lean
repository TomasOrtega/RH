import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGraphAreaFibre
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGraphAreaIntegral
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTangentJacComp
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaMultiplicityWeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set

open scoped ENNReal

noncomputable section

/- English proof (translation)
Rewrite using `[differentiableAt_piLp]`. Introduce `j`. Use `show DifferentiableAt ℂ (fun y => Sum.elim (fun i => y i) (fun i => Φ y i) (e j)) x`. Break down `e j with i | i` into its components or cases. Conclude with `(differentiableAt_piLp 2).1 differentiableAt_id i`.

Conclude with `(differentiableAt_piLp 2).1 hΦ i`.
-/
theorem GraphAreaFibre.differentiableAt_graphPt {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {Φ : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hΦ : DifferentiableAt ℂ Φ x) : DifferentiableAt ℂ (graphPt e Φ) x := by
  rw [differentiableAt_piLp]
  intro j
  show DifferentiableAt ℂ (fun y => Sum.elim (fun i => y i) (fun i => Φ y i) (e j)) x
  rcases e j with i | i
  · exact (differentiableAt_piLp 2).1 differentiableAt_id i
  · exact (differentiableAt_piLp 2).1 hΦ i

/- English proof (translation)
Unfold `graphBase`. Use `fun_prop`.
-/
theorem GraphAreaFibre.continuous_graphBase {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k) :
    Continuous (graphBase e : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin d)) := by
  unfold graphBase
  fun_prop

/- English proof (translation)
Introduce `d k n e Ω Φ hΩ hΦ P hPΩ hPm T hT π`. Use `set G : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin n) := graphPt e Φ with hGdef`. Use `set μ : Measure (EuclideanSpace ℂ (Fin d)) := Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) with hμdef`. Establish `hdim : ((2 * d : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin d)) : ℝ)`. Rewrite using `[finrank_real_of_complex, finrank_euclideanSpace_fin]`.

Establish `: μ.IsAddHaarMeasure`. Rewrite using `[hμdef, hdim]`. Use `infer_instance`. Use `set A : Set (EuclideanSpace ℂ (Fin d)) := Ω ∩ G ⁻¹' P with hAdef`. Establish `hAΩ : A ⊆ Ω` using `inter_subset_left`.

Establish `hGA : G '' A = P`. Rewrite using `[hAdef, image_inter_preimage]`. Conclude with `inter_eq_right.2 hPΩ`. Establish `hAm : MeasurableSet A`. Establish `hAeq : A = graphBase e '' P`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, hxP⟩`. Conclude with `⟨G x, hxP, graphBase_graphPt e Φ x⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Take `⟨x, hx, rfl⟩` from `hPΩ hy`. Rewrite using `[graphBase_graphPt]`. Conclude with `⟨hx, hy⟩`. Rewrite using `[hAeq]`. Use `hPm.image_of_continuousOn_injOn (GraphAreaFibre.continuous_graphBase e).continuousOn ?_` and prove the remaining obligations.

Introduce `y hy y' hy' h`. Take `⟨x, -, rfl⟩` from `hPΩ hy`. Take `⟨x', -, rfl⟩` from `hPΩ hy'`. Rewrite `h` using `[hGdef, graphBase_graphPt, graphBase_graphPt]`. Rewrite using `[h]`.

Establish `hGd : ∀ x ∈ Ω, DifferentiableAt ℂ G x` using `fun x hx => GraphAreaFibre.differentiableAt_graphPt e ((hΦ x hx).differentiableAt (hΩ.mem_nhds hx))`. Set `Lπ : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin d)` to `LinearMap.toContinuousLinearMap (linProjₗ π)`. Use `set f : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin d) := fun x => linProj π (G x) with hfdef`. Establish `hfd : ∀ x ∈ Ω, HasFDerivAt f ((Lπ.comp (fderiv ℂ G x)).restrictScalars ℝ) x` using `fun x hx => (Lπ.hasFDerivAt.comp x (hGd x hx).hasFDerivAt).restrictScalars ℝ`. Establish `hf' : ∀ x ∈ A, HasFDerivWithinAt f (fderiv ℝ f x) A x` using `fun x hx => (hfd x (hAΩ hx)).differentiableAt.hasFDerivAt.hasFDerivWithinAt`.

Take `⟨hNm, hN⟩` from `hMult (EuclideanSpace ℂ (Fin d)) μ A f (fun x => fderiv ℝ f x) hAm hf'`. Establish `hcount : ∀ w, {y | y ∈ P ∧ linProj π y = w}.encard = {x ∈ A | f x = w}.encard`. Introduce `w`. Establish `hset : {y | y ∈ P ∧ linProj π y = w} = G '' {x ∈ A | f x = w}`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, hyw⟩`. Take `⟨x, hx, rfl⟩` from `hPΩ hy`. Conclude with `⟨x, ⟨⟨hx, hy⟩, hyw⟩, rfl⟩`. Introduce and unpack `⟨x, ⟨⟨-, hxP⟩, hxw⟩, rfl⟩`.

Conclude with `⟨hxP, hxw⟩`. Rewrite using `[hset, (graphPt_injective_of_graphBase e Φ).injOn.encard_image]`. Establish `hNfun : (fun w : EuclideanSpace ℂ (Fin d) => (({y | y ∈ P ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞)) = fun w => (({x ∈ A | f x = w}.encard : ℕ∞) : ℝ≥0∞)`. Use function extensionality and compare the values at `w`. Rewrite using `[hcount w]`.

Establish `hc : μ = μ.addHaarScalarFactor volume • volume` using `Measure.isAddLeftInvariant_eq_smul μ volume`. Use `⟨?_, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[hNfun]`. Conclude with `hNm.mono_ac (Measure.absolutelyContinuous_isAddHaarMeasure volume μ)`. Establish `h1 : ∫⁻ y in P, g (linProj π y) * ENNReal.ofReal (tangentJac π (T y)) ∂(Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ)) = ∫⁻ x in A, g (f x) * ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ`.

Rewrite using `[← hGA, hInt d k n e Ω Φ hΩ hΦ A hAΩ hAm]`. Use `setLIntegral_congr_fun hAm fun x hx => ?_` and prove the remaining obligations. Establish `hG' : fderiv ℝ G x = (fderiv ℂ G x).restrictScalars ℝ` using `((hGd x (hAΩ hx)).hasFDerivAt.restrictScalars ℝ).fderiv`. Establish `hf'x : fderiv ℝ f x = (Lπ.comp (fderiv ℂ G x)).restrictScalars ℝ` using `(hfd x (hAΩ hx)).fderiv`. Establish `hJ` using `hJac d n (fderiv ℂ G x : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) π`.

Establish `hTx : T (G x) = LinearMap.range (fderiv ℂ G x : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))` using `hT x (hAΩ hx) hx.2`. Establish `hnn : 0 ≤ tangentJac π (T (G x))`. Unfold `tangentJac`. Check the signs of the components of the expression. Rewrite using `[mul_assoc, ← ENNReal.ofReal_mul hnn, hTx, hG', hf'x]`.

Use `congr 2`. Rewrite using `[h1, hN g hg]`. Repeatedly rewrite using `[hcount]`. Rewrite using `[hc, Measure.smul_apply, lintegral_smul_measure]`. Simplify using `only [ENNReal.smul_def, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem GraphAreaFibre.proof (hInt : GraphAreaIntegral.Statement) (hJac : TangentJacComp.Statement)
    (hMult : AreaMultiplicityWeight.Statement) : GraphAreaFibre.Statement := by
  intro d k n e Ω Φ hΩ hΦ P hPΩ hPm T hT π
  set G : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin n) := graphPt e Φ with hGdef
  set μ : Measure (EuclideanSpace ℂ (Fin d)) := Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) with hμdef
  have hdim : ((2 * d : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin d)) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have : μ.IsAddHaarMeasure := by
    rw [hμdef, hdim]
    infer_instance

  set A : Set (EuclideanSpace ℂ (Fin d)) := Ω ∩ G ⁻¹' P with hAdef
  have hAΩ : A ⊆ Ω := inter_subset_left
  have hGA : G '' A = P := by
    rw [hAdef, image_inter_preimage]
    exact inter_eq_right.2 hPΩ
  have hAm : MeasurableSet A := by
    have hAeq : A = graphBase e '' P := by
      ext x
      constructor
      · rintro ⟨-, hxP⟩
        exact ⟨G x, hxP, graphBase_graphPt e Φ x⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨x, hx, rfl⟩ := hPΩ hy
        rw [graphBase_graphPt]
        exact ⟨hx, hy⟩
    rw [hAeq]
    refine hPm.image_of_continuousOn_injOn (GraphAreaFibre.continuous_graphBase e).continuousOn ?_
    intro y hy y' hy' h
    obtain ⟨x, -, rfl⟩ := hPΩ hy
    obtain ⟨x', -, rfl⟩ := hPΩ hy'
    rw [hGdef, graphBase_graphPt, graphBase_graphPt] at h
    rw [h]

  have hGd : ∀ x ∈ Ω, DifferentiableAt ℂ G x := fun x hx =>
    GraphAreaFibre.differentiableAt_graphPt e ((hΦ x hx).differentiableAt (hΩ.mem_nhds hx))
  let Lπ : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
    LinearMap.toContinuousLinearMap (linProjₗ π)
  set f : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin d) := fun x => linProj π (G x) with hfdef
  have hfd : ∀ x ∈ Ω, HasFDerivAt f ((Lπ.comp (fderiv ℂ G x)).restrictScalars ℝ) x := fun x hx =>
    (Lπ.hasFDerivAt.comp x (hGd x hx).hasFDerivAt).restrictScalars ℝ
  have hf' : ∀ x ∈ A, HasFDerivWithinAt f (fderiv ℝ f x) A x := fun x hx =>
    (hfd x (hAΩ hx)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  obtain ⟨hNm, hN⟩ := hMult (EuclideanSpace ℂ (Fin d)) μ A f (fun x => fderiv ℝ f x) hAm hf'

  have hcount : ∀ w, {y | y ∈ P ∧ linProj π y = w}.encard = {x ∈ A | f x = w}.encard := by
    intro w
    have hset : {y | y ∈ P ∧ linProj π y = w} = G '' {x ∈ A | f x = w} := by
      ext y
      constructor
      · rintro ⟨hy, hyw⟩
        obtain ⟨x, hx, rfl⟩ := hPΩ hy
        exact ⟨x, ⟨⟨hx, hy⟩, hyw⟩, rfl⟩
      · rintro ⟨x, ⟨⟨-, hxP⟩, hxw⟩, rfl⟩
        exact ⟨hxP, hxw⟩
    rw [hset, (graphPt_injective_of_graphBase e Φ).injOn.encard_image]
  have hNfun : (fun w : EuclideanSpace ℂ (Fin d) =>
      (({y | y ∈ P ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞)) =
      fun w => (({x ∈ A | f x = w}.encard : ℕ∞) : ℝ≥0∞) := by
    funext w
    rw [hcount w]

  have hc : μ = μ.addHaarScalarFactor volume • volume := Measure.isAddLeftInvariant_eq_smul μ volume
  refine ⟨?_, fun g hg => ?_⟩
  · rw [hNfun]
    exact hNm.mono_ac (Measure.absolutelyContinuous_isAddHaarMeasure volume μ)

  have h1 : ∫⁻ y in P, g (linProj π y) * ENNReal.ofReal (tangentJac π (T y))
      ∂(Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ)) =
      ∫⁻ x in A, g (f x) * ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ := by
    rw [← hGA, hInt d k n e Ω Φ hΩ hΦ A hAΩ hAm]
    refine setLIntegral_congr_fun hAm fun x hx => ?_
    have hG' : fderiv ℝ G x = (fderiv ℂ G x).restrictScalars ℝ :=
      ((hGd x (hAΩ hx)).hasFDerivAt.restrictScalars ℝ).fderiv
    have hf'x : fderiv ℝ f x = (Lπ.comp (fderiv ℂ G x)).restrictScalars ℝ := (hfd x (hAΩ hx)).fderiv
    have hJ := hJac d n (fderiv ℂ G x : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) π
    have hTx : T (G x) = LinearMap.range (fderiv ℂ G x :
        EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := hT x (hAΩ hx) hx.2
    have hnn : 0 ≤ tangentJac π (T (G x)) := by
      unfold tangentJac
      positivity
    rw [mul_assoc, ← ENNReal.ofReal_mul hnn, hTx, hG', hf'x]
    congr 2
  rw [h1, hN g hg]
  simp_rw [hcount]
  rw [hc, Measure.smul_apply, lintegral_smul_measure]
  simp only [ENNReal.smul_def, smul_eq_mul]
  ring

end

end GroundTheory.Heights₂.Heights
