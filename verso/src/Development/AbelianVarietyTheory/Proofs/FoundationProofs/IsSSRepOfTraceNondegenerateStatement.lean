import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepOfTraceNondegenerate
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TraceSemisimple.isSSRep_of_trace_nondegenerate` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIsSSRepOfTraceNondegenerate.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.isSSRep_of_trace_nondegenerate' : ∀ (Γ K : Type) [Group Γ] [Field K] (a : ℕ) (ρ : Γ →* GL (Fin a) K), (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) → IsSSRep ρ := by
  first | exact @GlobalTheory.TraceSemisimple.isSSRep_of_trace_nondegenerate | exact GlobalTheory.TraceSemisimple.isSSRep_of_trace_nondegenerate | (intros; apply GlobalTheory.TraceSemisimple.isSSRep_of_trace_nondegenerate <;> assumption)
