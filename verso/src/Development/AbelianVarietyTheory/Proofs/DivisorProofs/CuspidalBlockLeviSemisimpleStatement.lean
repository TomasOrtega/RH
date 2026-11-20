import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalBlockLeviSemisimple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationOfISupRangeEquivariant
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspBlock
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspBlock.isSemisimple_restrict_mid` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCuspidalBlockLeviSemisimple.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.cuspidal_block_levi_semisimple : GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (l n N : ℕ)
    (Z : Type) [AddCommGroup Z] [Module ℂ Z]
    (τ : Representation ℂ (GlobalTheory.SmGL.Levi k (fun j : Fin 3 => Fin (GlobalTheory.CuspBlock.tripSizes l n N j))) Z),
    GlobalTheory.PRep.IsSmooth τ → τ.IsIrreducible →
      Representation.IsSemisimpleRepresentation (τ.comp (GlobalTheory.CuspBlock.midHom k l n N)) := by
  first | exact @GlobalTheory.CuspBlock.isSemisimple_restrict_mid | exact GlobalTheory.CuspBlock.isSemisimple_restrict_mid | (intros; apply GlobalTheory.CuspBlock.isSemisimple_restrict_mid <;> assumption)
