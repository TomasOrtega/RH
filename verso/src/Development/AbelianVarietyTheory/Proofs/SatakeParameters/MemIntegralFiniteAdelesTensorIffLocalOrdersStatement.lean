import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralFiniteAdelesTensorIffLocalOrders
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FMemIntegralFiniteAdelesTensorIffLocalOrders.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.mem_integralFiniteAdelesTensor_iff_localOrders : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (z : Af F ⊗[F] E), z ∈ intA F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), evF E v z ∈ ordAt E v := by
  first | exact @GlobalTheory.PlaceComp.IntLocal.mem_intA_iff | exact GlobalTheory.PlaceComp.IntLocal.mem_intA_iff | (intros; apply GlobalTheory.PlaceComp.IntLocal.mem_intA_iff <;> assumption)
