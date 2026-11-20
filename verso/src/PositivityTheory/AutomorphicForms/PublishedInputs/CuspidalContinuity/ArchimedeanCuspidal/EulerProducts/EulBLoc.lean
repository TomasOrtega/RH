import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel NNReal

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace Ad3.GP

section Mat

variable {R : Type*} [CommRing R]

end Mat

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def kU (U : Fˣ) : GL (Fin 3) F :=
  ⟨!![0, 1, 0; 1, 0, 0; ((U⁻¹ : Fˣ) : F), 0, 1], !![0, 1, 0; 1, 0, 0; 0, -((U⁻¹ : Fˣ) : F), 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

variable {ψ : AddChar F Circle} {ν : Fˣ →* ℂˣ} {V : Submodule ℂ (GL (Fin 3) F → ℂ)}

end Loc

section Real

/- English proof (translation)
Use `⟨fun _ _ h => Units.ext h, comap_measurable _, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨B, hB, rfl⟩`. Establish `: Units.val '' (Units.val ⁻¹' B : Set ℝˣ) = B ∩ {0}ᶜ`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `⟨hu, by simp⟩`. Introduce and unpack `⟨hx, hx0⟩`. Conclude with `⟨Units.mk0 x hx0, hx, rfl⟩`. Rewrite using `[this]`.

Conclude with `hB.inter (measurableSet_singleton _).compl`.
-/
theorem val_measurableEmbedding_eulB : MeasurableEmbedding (Units.val : ℝˣ → ℝ) := by
  refine ⟨fun _ _ h => Units.ext h, comap_measurable _, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  have : Units.val '' (Units.val ⁻¹' B : Set ℝˣ) = B ∩ {0}ᶜ := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, by simp⟩
    · rintro ⟨hx, hx0⟩
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [this]
  exact hB.inter (measurableSet_singleton _).compl

/- English proof (translation)
Establish `h` using `val_measurableEmbedding_eulB.map_comap (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹)`. Establish `hr : Set.range (Units.val : ℝˣ → ℝ) = {0}ᶜ`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`.

Simplify using the standard rewrite rules. Introduce `hx`. Conclude with `⟨Units.mk0 x hx, rfl⟩`. Establish `hac : (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹) ≪ volume` using `withDensity_absolutelyContinuous _ _`. Establish `h0 : (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹) {0} = 0` using `hac (by simp)`.

Establish `: (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹).restrict ({0}ᶜ : Set ℝ) = volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹` using `Measure.restrict_eq_self_of_ae_mem (by`. Rewrite using `[ae_iff]`. Simplify using `using h0)`. Rewrite `h` using `[hr, this]`. Conclude with `h`.
-/
theorem map_val_mulR_eulB : Measure.map (Units.val : ℝˣ → ℝ) mulR =
    volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹ := by
  have h := val_measurableEmbedding_eulB.map_comap (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹)
  have hr : Set.range (Units.val : ℝˣ → ℝ) = {0}ᶜ := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      simp
    · intro hx
      exact ⟨Units.mk0 x hx, rfl⟩
  have hac : (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹) ≪ volume :=
    withDensity_absolutelyContinuous _ _
  have h0 : (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹) {0} = 0 := hac (by simp)
  have : (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹).restrict ({0}ᶜ : Set ℝ) =
      volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹ :=
    Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]
      simpa using h0)
  rw [hr, this] at h
  exact h

instance sigmaFinite_mulR_eulB : SigmaFinite mulR := by
  refine SigmaFinite.of_map _ val_measurableEmbedding_eulB.measurable.aemeasurable ?_
  rw [map_val_mulR_eulB]
  exact SigmaFinite.withDensity_ofReal _

end Real

end Ad3.GP
