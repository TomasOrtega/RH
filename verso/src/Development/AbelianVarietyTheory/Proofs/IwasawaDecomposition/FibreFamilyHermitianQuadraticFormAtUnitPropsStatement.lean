import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreFamilyHermitianQuadraticFormAtUnitProps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GaugeEx.FibBasic.fibAt_basic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFibreFamilyHermitianQuadraticFormAtUnitProps.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), ν.IsAddHaarMeasure → IsUnit β → FibAt R σ J μ ν β m → m {X | qR R σ J (X 0) ≠ β} = 0 ∧ IsFiniteMeasureOnCompacts m ∧ ∀ m', FibAt R σ J μ ν β m' → m' = m := by
  first | exact @GlobalTheory.GaugeEx.FibBasic.fibAt_basic | exact GlobalTheory.GaugeEx.FibBasic.fibAt_basic | (intros; apply GlobalTheory.GaugeEx.FibBasic.fibAt_basic <;> assumption)
