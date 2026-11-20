import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalVectorNotInBorelJacquetKernel
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSphericalVectorNotInBorelJacquetKernel.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.spherical_vector_not_in_borel_jacquet_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ v ∈ twKer π (unipB k (Fin n)) 1, (∀ g ∈ KO k (Fin n), π g v = v) → v = 0 := by
  first | exact @GlobalTheory.PsType.eq_zero_of_fixed_KO_twKer_unipB | exact GlobalTheory.PsType.eq_zero_of_fixed_KO_twKer_unipB | (intros; apply GlobalTheory.PsType.eq_zero_of_fixed_KO_twKer_unipB <;> assumption)
