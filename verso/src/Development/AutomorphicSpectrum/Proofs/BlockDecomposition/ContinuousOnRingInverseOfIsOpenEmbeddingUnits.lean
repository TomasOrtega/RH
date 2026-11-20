import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GLOpen

/- English proof (translation)
Introduce and unpack `_ ⟨u, rfl⟩`. Use `ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations. Rewrite using `[← hA.continuousAt_iff]`. Establish `h : (Ring.inverse ∘ Units.val : Aˣ → A) = fun v => ((v⁻¹ : Aˣ) : A)`. Use function extensionality and compare the values at `v`.

Conclude with `Ring.inverse_unit v`. Rewrite using `[h]`. Conclude with `Units.continuous_coe_inv.continuousAt`.
-/
theorem continuousOn_ringInverse_of_isOpenEmbedding_units
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (hA : IsOpenEmbedding (Units.val : Aˣ → A)) :
    ContinuousOn (Ring.inverse : A → A) {x | IsUnit x} := by
  rintro _ ⟨u, rfl⟩
  refine ContinuousAt.continuousWithinAt ?_
  rw [← hA.continuousAt_iff]
  have h : (Ring.inverse ∘ Units.val : Aˣ → A) = fun v => ((v⁻¹ : Aˣ) : A) := by
    funext v
    exact Ring.inverse_unit v
  rw [h]
  exact Units.continuous_coe_inv.continuousAt

/- English proof (translation)
Establish `hdet : Continuous (fun M : Matrix (Fin n) (Fin n) A => M.det)` using `continuous_id.matrix_det`. Establish `hunit : ∀ M : Matrix (Fin n) (Fin n) A, IsUnit M ↔ IsUnit M.det` using `fun M => Matrix.isUnit_iff_isUnit_det M`. Establish `hadj : Continuous (fun M : Matrix (Fin n) (Fin n) A => M.adjugate)` using `continuous_id.matrix_adjugate`. Establish `hopen : IsOpen {x : A | IsUnit x}` using `hA.isOpen_range`. Use `⟨Units.isEmbedding_val_mk' (f := fun M : Matrix (Fin n) (Fin n) A => M⁻¹) ?_ fun u => (Matrix.coe_units_inv u).symm, ?_⟩` and prove the remaining obligations.

Establish `hinv : ContinuousOn (fun M : Matrix (Fin n) (Fin n) A => Ring.inverse M.det • M.adjugate) {M | IsUnit M}`. Establish `hri : ContinuousOn (fun M : Matrix (Fin n) (Fin n) A => Ring.inverse M.det) {M | IsUnit M}` using `(GlobalTheory.CompanionTheory.SW.GLOpen.continuousOn_ringInverse_of_isOpenEmbedding_units A hA).comp hdet.continuousOn fun M hM => (hunit M).mp hM`. Conclude with `hri.smul hadj.continuousOn`. Conclude with `hinv.congr fun M _ => Matrix.inv_def M`. Establish `h : Set.range (Units.val : GL (Fin n) A → Matrix (Fin n) (Fin n) A) = (fun M : Matrix (Fin n) (Fin n) A => M.det) ⁻¹' {x | IsUnit x}`.

Use extensionality with `M`. Conclude with `hunit M`. Rewrite using `[h]`. Conclude with `hopen.preimage hdet`.
-/
theorem isOpenEmbedding_val_GL
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (hA : IsOpenEmbedding (Units.val : Aˣ → A)) (n : ℕ) :
    IsOpenEmbedding (Units.val : GL (Fin n) A → Matrix (Fin n) (Fin n) A) := by
  have hdet : Continuous (fun M : Matrix (Fin n) (Fin n) A => M.det) :=
    continuous_id.matrix_det
  have hunit : ∀ M : Matrix (Fin n) (Fin n) A, IsUnit M ↔ IsUnit M.det :=
    fun M => Matrix.isUnit_iff_isUnit_det M
  have hadj : Continuous (fun M : Matrix (Fin n) (Fin n) A => M.adjugate) :=
    continuous_id.matrix_adjugate
  have hopen : IsOpen {x : A | IsUnit x} := hA.isOpen_range
  refine ⟨Units.isEmbedding_val_mk' (f := fun M : Matrix (Fin n) (Fin n) A => M⁻¹) ?_
    fun u => (Matrix.coe_units_inv u).symm, ?_⟩
  · have hinv : ContinuousOn
        (fun M : Matrix (Fin n) (Fin n) A => Ring.inverse M.det • M.adjugate) {M | IsUnit M} := by
      have hri : ContinuousOn (fun M : Matrix (Fin n) (Fin n) A => Ring.inverse M.det)
          {M | IsUnit M} :=
        (GlobalTheory.CompanionTheory.SW.GLOpen.continuousOn_ringInverse_of_isOpenEmbedding_units A hA).comp hdet.continuousOn
          fun M hM => (hunit M).mp hM
      exact hri.smul hadj.continuousOn
    exact hinv.congr fun M _ => Matrix.inv_def M
  · have h : Set.range (Units.val : GL (Fin n) A → Matrix (Fin n) (Fin n) A) =
        (fun M : Matrix (Fin n) (Fin n) A => M.det) ⁻¹' {x | IsUnit x} := by
      ext M
      exact hunit M
    rw [h]
    exact hopen.preimage hdet

end GlobalTheory.CompanionTheory.SW.GLOpen
