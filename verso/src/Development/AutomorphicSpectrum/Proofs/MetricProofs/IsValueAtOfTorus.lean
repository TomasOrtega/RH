import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

noncomputable def scaleT (c : K → ℂ) : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ :=
  aeval fun k => C (c k) * X k

omit [Fintype K] in
/- English proof (translation)
Establish `h : (scaleT (fun k => (c k)⁻¹)).comp (scaleT c) = AlgHom.id ℂ _`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `k`. Simplify using `only [scaleT, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]`. Rewrite using `[← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]`.

Conclude with `DFunLike.congr_fun h f`.
-/
theorem scaleT_inv_scaleT (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (f : MvPolynomial K ℂ) :
    scaleT (fun k => (c k)⁻¹) (scaleT c f) = f := by
  have h : (scaleT (fun k => (c k)⁻¹)).comp (scaleT c) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [scaleT, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact DFunLike.congr_fun h f

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `h : mConeMap (fun q : Σ k, ι k => c q.1 * z q) = ((scaleT c).restrictScalars ℤ).comp (mConeMap z)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`. Simplify using `only [mConeMap, scaleT, AlgHom.comp_apply, aeval_X, AlgHom.restrictScalars_apply, map_mul, algHom_C, algebraMap_eq, mul_assoc]`. Rewrite using `[mul_left_comm]`.

Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem mConeMap_torus (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    mConeMap (fun q : Σ k, ι k => c q.1 * z q) f = scaleT c (mConeMap z f) := by
  have h : mConeMap (fun q : Σ k, ι k => c q.1 * z q) =
      ((scaleT c).restrictScalars ℤ).comp (mConeMap z) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [mConeMap, scaleT, AlgHom.comp_apply, aeval_X, AlgHom.restrictScalars_apply, map_mul,
      algHom_C, algebraMap_eq, mul_assoc]
    rw [mul_left_comm]
  rw [h]
  rfl

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use extensionality with `f`. Rewrite using `[mCoordIdeal, mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, mConeMap_torus]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg (scaleT fun k => (c k)⁻¹) h` as an intermediate fact.

Rewrite `this` using `[scaleT_inv_scaleT c hc, map_zero]`. Then use the resulting hypothesis. Introduce `h`. Rewrite using `[h, map_zero]`.
-/
theorem mCoordIdeal_torus (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    mCoordIdeal (fun q : Σ k, ι k => c q.1 * z q) = mCoordIdeal z := by
  ext f
  rw [mCoordIdeal, mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, mConeMap_torus]
  constructor
  · intro h
    have := congrArg (scaleT fun k => (c k)⁻¹) h
    rwa [scaleT_inv_scaleT c hc, map_zero] at this
  · intro h
    rw [h, map_zero]

/- English proof (translation)
Take `⟨d, g, h, hg, hh, hy, he, h0, rfl⟩` from `hv`. Establish `hu : (∏ k, c k ^ d k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)`. Use `⟨d, g, h, hg, hh, hy, he, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eval_smul_homog h d hh]`. Conclude with `mul_ne_zero hu h0`.

Rewrite using `[eval_smul_homog g d hg, eval_smul_homog h d hh, mul_div_mul_left _ _ hu]`.
-/
theorem isValueAt_torus {x : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) (hv : IsValueAt x s z v) :
    IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v := by
  obtain ⟨d, g, h, hg, hh, hy, he, h0, rfl⟩ := hv
  have hu : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, hy, he, ?_, ?_⟩
  · rw [eval_smul_homog h d hh]
    exact mul_ne_zero hu h0
  · rw [eval_smul_homog g d hg, eval_smul_homog h d hh, mul_div_mul_left _ _ hu]

/- English proof (translation)
Establish `h` using `isValueAt_torus (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hv`. Establish `e : (fun q : Σ k, ι k => (c q.1)⁻¹ * (c q.1 * z q)) = z`. Use function extensionality and compare the values at `q`. Conclude with `inv_mul_cancel_left₀ (hc q.1) _`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem isValueAt_of_torus {x : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) (hv : IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v) :
    IsValueAt x s z v := by
  have h := isValueAt_torus (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hv
  have e : (fun q : Σ k, ι k => (c q.1)⁻¹ * (c q.1 * z q)) = z := by
    funext q
    exact inv_mul_cancel_left₀ (hc q.1) _
  rwa [e] at h

/- English proof (translation)
Distinguish the cases in `h : ∃ v, IsValueAt x s z v`. Take `⟨v, hv⟩` from `h`. Rewrite using `[valAt_eq hz hv, valAt_eq hcz (isValueAt_torus c hc hv)]`. Establish `h' : ¬ ∃ v, IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v` using `fun ⟨v, hv⟩ => h ⟨v, isValueAt_of_torus c hc hv⟩`. Rewrite using `[valAt, valAt, dif_neg h, dif_neg h']`.
-/
theorem valAt_torus {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (hz : z ∈ mcPts (mCoordIdeal x))
    (hcz : (fun q : Σ k, ι k => c q.1 * z q) ∈ mcPts (mCoordIdeal x)) (s : Ω) :
    valAt x s (fun q : Σ k, ι k => c q.1 * z q) = valAt x s z := by
  by_cases h : ∃ v, IsValueAt x s z v
  · obtain ⟨v, hv⟩ := h
    rw [valAt_eq hz hv, valAt_eq hcz (isValueAt_torus c hc hv)]
  · have h' : ¬ ∃ v, IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v :=
      fun ⟨v, hv⟩ => h ⟨v, isValueAt_of_torus c hc hv⟩
    rw [valAt, valAt, dif_neg h, dif_neg h']

/- English proof (translation)
Introduce `K _ ι _ Ω _ x z c hc`. Use `⟨mCoordIdeal_torus c hc z, fun hz => ?_⟩` and prove the remaining obligations. Establish `hcz` using `mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal x) c hc hz`. Conclude with `⟨hcz, valAt_torus c hc hz hcz⟩`.
-/
theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (c : K → ℂ), (∀ k, c k ≠ 0) →
    mCoordIdeal (fun q : Σ k, ι k => c q.1 * z q) = mCoordIdeal z ∧
      (z ∈ mcPts (mCoordIdeal x) → (fun q : Σ k, ι k => c q.1 * z q) ∈ mcPts (mCoordIdeal x) ∧
        ∀ s : Ω, valAt x s (fun q : Σ k, ι k => c q.1 * z q) = valAt x s z) := by
  intro K _ ι _ Ω _ x z c hc
  refine ⟨mCoordIdeal_torus c hc z, fun hz => ?_⟩
  have hcz := mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal x) c hc hz
  exact ⟨hcz, valAt_torus c hc hz hcz⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct
