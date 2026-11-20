import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasuresTransportUnitarySimilitude
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFibreMeasuresTransportUnitarySimilitude.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.fibreMeasures_transport_unitary_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J J₂ : Matrix (Fin M) (Fin M) E) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (β c : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsUnit g.det → IsUnit c → (∀ z, qR R σ J₂ (g.mulVec z) = c * qR R σ J z) → FibAt R σ J (tupMeas lam 1 M) ν β m → FibAt R σ J₂ (tupMeas lam 1 M) ν (c * β) ((modu (R ⊗[F] E) g.det * (modu R c)⁻¹) • m.map (lrAct g 1)) := by
  first | exact @GlobalTheory.GaugeEx.fibAt_similitude | exact GlobalTheory.GaugeEx.fibAt_similitude | (intros; apply GlobalTheory.GaugeEx.fibAt_similitude <;> assumption)
