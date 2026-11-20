import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIsotropicFlagSelfAdjointLeviIffBlock
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingWithDensity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarComplexGLMatricesConjAndSingularNull

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

/- English proof (translation)
Establish `hc : Continuous fun g : Formalism.REAL.UJ ε => uMat g` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hc' : Continuous fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ` using `hc.matrix_conjTranspose`. Establish `hset : flagM ε W = ⋂ i, ⋂ y ∈ W i, ((fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) ∩ (fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)))`. Use extensionality with `g`. Simplify using `[flagM]`.

Rewrite using `[hset]`. Use `isClosed_iInter fun i => isClosed_biInter fun y _ => ?_` and prove the remaining obligations. Establish `hW : IsClosed (W i : Set (Fin n → ℂ))` using `(W i).closed_of_finiteDimensional`. Conclude with `(hW.preimage (hc.matrix_mulVec continuous_const)).inter (hW.preimage (hc'.matrix_mulVec continuous_const))`.
-/
theorem isClosed_flagM {n a : ℕ} (ε : Fin n → Bool) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) :
    IsClosed (flagM ε W) := by
  have hc : Continuous fun g : Formalism.REAL.UJ ε => uMat g := Units.continuous_val.comp continuous_subtype_val
  have hc' : Continuous fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ := hc.matrix_conjTranspose
  have hset : flagM ε W = ⋂ i, ⋂ y ∈ W i,
      ((fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) ∩
        (fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ))) := by
    ext g
    simp [flagM]
  rw [hset]
  refine isClosed_iInter fun i => isClosed_biInter fun y _ => ?_
  have hW : IsClosed (W i : Set (Fin n → ℂ)) := (W i).closed_of_finiteDimensional
  exact (hW.preimage (hc.matrix_mulVec continuous_const)).inter (hW.preimage (hc'.matrix_mulVec continuous_const))

/- English proof (translation)
Establish `h1 : ∀ᵐ x ∂(Measure.pi fun i => ENNReal.ofReal (d i) • haarLoc (j i)), ∀ i, (Matrix.of (x i)).det ≠ 0`. Rewrite using `[ae_all_iff]`. Introduce `i`. Establish `h0 : ∀ᵐ y ∂(ENNReal.ofReal (d i) • haarLoc (j i)), (Matrix.of y).det ≠ 0`. Establish `hn` using `(haarLoc_conj_and_null (j i)).2`.

Rewrite using `[ae_iff, Measure.smul_apply]`. Simplify using `[hn]`. Conclude with `(Measure.tendsto_eval_ae_ae (μ := fun i => ENNReal.ofReal (d i) • haarLoc (j i)) (i := i)).eventually (p := fun y => (Matrix.of y).det ≠ 0) h0`. Conclude with `Measure.quasiMeasurePreserving_fst.ae h1`.
-/
theorem ae_det_ne_zero {a : ℕ} (j : Fin a → ℕ) (d : Fin a → ℝ) {Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    [SFinite ν] :
    ∀ᵐ z ∂((Measure.pi fun i => ENNReal.ofReal (d i) • haarLoc (j i)).prod ν), ∀ i, (Matrix.of (z.1 i)).det ≠ 0 := by
  have h1 : ∀ᵐ x ∂(Measure.pi fun i => ENNReal.ofReal (d i) • haarLoc (j i)), ∀ i, (Matrix.of (x i)).det ≠ 0 := by
    rw [ae_all_iff]
    intro i
    have h0 : ∀ᵐ y ∂(ENNReal.ofReal (d i) • haarLoc (j i)), (Matrix.of y).det ≠ 0 := by
      have hn := (haarLoc_conj_and_null (j i)).2
      rw [ae_iff, Measure.smul_apply]
      simp [hn]
    exact (Measure.tendsto_eval_ae_ae (μ := fun i => ENNReal.ofReal (d i) • haarLoc (j i)) (i := i)).eventually
      (p := fun y => (Matrix.of y).det ≠ 0) h0
  exact Measure.quasiMeasurePreserving_fst.ae h1

/- English proof (translation)
Assemble the required witnesses or components as `⟨hf.measurable, by rw [Measure.map_smul, hf.map_eq]⟩`.
-/
private theorem measurePreserving_smul_measure {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : MeasurePreserving f μ μ) (c : ENNReal) : MeasurePreserving f (c • μ) (c • μ) :=
  ⟨hf.measurable, by rw [Measure.map_smul, hf.map_eq]⟩

/- English proof (translation)
Introduce `n n₀ a j ε ε₀ B B₀ hB W hW θ hθ hθl c`. Use `set P := Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i) with hP`. Use `set ν := ENNReal.ofReal c • Formalism.REAL.muG ε₀ with hν`. Establish `hdet : ∀ᵐ z ∂(P.prod ν), ∀ i, (Matrix.of (z.1 i)).det ≠ 0` using `ae_det_ne_zero j (fun i => 2 ^ (j i ^ 2)) ν`. Establish `hmem : ∀ z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → θ z ∈ flagM ε W` using `fun z hz => (Range.mem_flagM_iff n n₀ a j ε ε₀ B B₀ hB W hW (θ z)).2 ⟨fun i => Matrix.of (z.1 i), z.2, hz, hθl z hz⟩`.

Establish `hM : MeasurableSet (flagM ε W)` using `(isClosed_flagM ε W).measurableSet`. Use `⟨?_, fun s hs => ?_⟩` and prove the remaining obligations. Establish `h : ∀ᵐ m ∂((P.prod ν).map θ), m ∈ flagM ε W` using `(ae_map_iff hθ.aemeasurable hM).2 (hdet.mono hmem)`. Conclude with `measure_mono_null (fun m hm => hm) (ae_iff.1 h)`. Take `⟨x, g, hx, hs'⟩` from `(Range.mem_flagM_iff n n₀ a j ε ε₀ B B₀ hB W hW s).1 hs`.

Set `T : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀` to `Prod.map (fun (y : ∀ i, Fin (j i) → Fin (j i) → ℂ) (i : Fin a) (r t : Fin (j i)) => (x i * Matrix.of (y i) * (1 : Matrix (Fin (j i)) (Fin (j i)) ℂ)) r t) (fun u => g * u)`. Establish `hT : MeasurePreserving T (P.prod ν) (P.prod ν)`. Use `MeasurePreserving.prod ?_ ?_` and prove the remaining obligations. Conclude with `measurePreserving_pi _ _ fun i => measurePreserving_smul_measure (GlobalTheory.HaarMul.measurePreserving_mul_mul (j i) (x i) 1 (hx i) (by simp)) _`. Conclude with `measurePreserving_smul_measure (measurePreserving_mul_left (Formalism.REAL.muG ε₀) g) _`.

Establish `hcomm : ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → s * θ z = θ (T z)`. Introduce `z hz`. Establish `hz' : ∀ i, (Matrix.of ((T z).1 i)).det ≠ 0`. Introduce `i`. Establish `: Matrix.of ((T z).1 i) = x i * Matrix.of (z.1 i)`.

Use extensionality with `r t`. Simplify using `[T]`. Rewrite using `[this, Matrix.det_mul]`. Conclude with `mul_ne_zero (hx i) (hz i)`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `uMat s * uMat (θ z) = uMat (θ (T z))`. Rewrite using `[hs', hθl z hz, hθl (T z) hz', ← hB.lev_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Use extensionality with `r t`. Simplify using `[T]`. Establish `hmul : Measurable fun m : Formalism.REAL.UJ ε => s * m` using `measurable_const_mul s`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem map_chart_carried_and_invariant : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ), SpansFlag B W → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (flagM ε W)ᶜ = 0 ∧ ∀ s ∈ flagM ε W, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ).map (fun g => s * g) = (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) := by
  intro n n₀ a j ε ε₀ B B₀ hB W hW θ hθ hθl c
  set P := Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i) with hP
  set ν := ENNReal.ofReal c • Formalism.REAL.muG ε₀ with hν
  have hdet : ∀ᵐ z ∂(P.prod ν), ∀ i, (Matrix.of (z.1 i)).det ≠ 0 :=
    ae_det_ne_zero j (fun i => 2 ^ (j i ^ 2)) ν
  have hmem : ∀ z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀,
      (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → θ z ∈ flagM ε W := fun z hz =>
    (Range.mem_flagM_iff n n₀ a j ε ε₀ B B₀ hB W hW (θ z)).2 ⟨fun i => Matrix.of (z.1 i), z.2, hz, hθl z hz⟩
  have hM : MeasurableSet (flagM ε W) := (isClosed_flagM ε W).measurableSet
  refine ⟨?_, fun s hs => ?_⟩
  · have h : ∀ᵐ m ∂((P.prod ν).map θ), m ∈ flagM ε W :=
      (ae_map_iff hθ.aemeasurable hM).2 (hdet.mono hmem)
    exact measure_mono_null (fun m hm => hm) (ae_iff.1 h)
  · obtain ⟨x, g, hx, hs'⟩ := (Range.mem_flagM_iff n n₀ a j ε ε₀ B B₀ hB W hW s).1 hs
    let T : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ :=
      Prod.map (fun (y : ∀ i, Fin (j i) → Fin (j i) → ℂ) (i : Fin a) (r t : Fin (j i)) =>
        (x i * Matrix.of (y i) * (1 : Matrix (Fin (j i)) (Fin (j i)) ℂ)) r t) (fun u => g * u)
    have hT : MeasurePreserving T (P.prod ν) (P.prod ν) := by
      refine MeasurePreserving.prod ?_ ?_
      · exact measurePreserving_pi _ _ fun i =>
          measurePreserving_smul_measure (GlobalTheory.HaarMul.measurePreserving_mul_mul (j i) (x i) 1 (hx i) (by simp)) _
      · exact measurePreserving_smul_measure (measurePreserving_mul_left (Formalism.REAL.muG ε₀) g) _
    have hcomm : ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → s * θ z = θ (T z) := by
      intro z hz
      have hz' : ∀ i, (Matrix.of ((T z).1 i)).det ≠ 0 := by
        intro i
        have : Matrix.of ((T z).1 i) = x i * Matrix.of (z.1 i) := by
          ext r t
          simp [T]
        rw [this, Matrix.det_mul]
        exact mul_ne_zero (hx i) (hz i)
      apply Subtype.ext
      apply Units.ext
      change uMat s * uMat (θ z) = uMat (θ (T z))
      rw [hs', hθl z hz, hθl (T z) hz', ← hB.lev_mul]
      congr 1
      · funext i
        ext r t
        simp [T]
    have hmul : Measurable fun m : Formalism.REAL.UJ ε => s * m := measurable_const_mul s
    calc ((P.prod ν).map θ).map (fun m => s * m)
        = (P.prod ν).map (fun z => s * θ z) := by rw [Measure.map_map hmul hθ]; rfl
      _ = (P.prod ν).map (fun z => θ (T z)) := Measure.map_congr (hdet.mono fun z hz => hcomm z hz)
      _ = ((P.prod ν).map T).map θ := by rw [Measure.map_map hθ hT.measurable]; rfl
      _ = (P.prod ν).map θ := by rw [hT.map_eq]

end GlobalTheory.LeviIso
