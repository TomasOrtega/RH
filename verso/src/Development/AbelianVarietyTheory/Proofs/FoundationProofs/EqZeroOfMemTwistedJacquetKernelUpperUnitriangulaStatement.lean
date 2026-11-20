import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfMemTwistedJacquetKernelUpperUnitriangula
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PsType.eq_zero_of_mem_twKer_unipB` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FEqZeroOfMemTwistedJacquetKernelUpperUnitriangula.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_mem_twistedJacquetKernel_upperUnitriangular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp ψ) (theta ψ) v → v = 0 := by
  first | exact @GlobalTheory.PsType.eq_zero_of_mem_twKer_unipB | exact GlobalTheory.PsType.eq_zero_of_mem_twKer_unipB | (intros; apply GlobalTheory.PsType.eq_zero_of_mem_twKer_unipB <;> assumption)
