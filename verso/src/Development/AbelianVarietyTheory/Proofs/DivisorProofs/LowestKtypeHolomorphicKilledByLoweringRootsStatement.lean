import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKtypeHolomorphicKilledByLoweringRoots
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLowestKtypeHolomorphicKilledByLoweringRoots.lean&line=338#L338)
-/
theorem _root_.GlobalTheory.T.lowest_Ktype_holomorphic_killed_by_lowering_roots : ∀ (n p : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mt n → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → (∀ a, ε a = decide ((a : ℕ) < p)) → IsDS ε lam σ → ∀ v ∈ lowKSub ε lam σ, SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v → ∀ a c : Fin n, ε a = true → ε c = false → dRepC (Formalism.REAL.Jm ε) σ (Matrix.single c a 1) v = 0 := by
  first | exact @GlobalTheory.HolDict.Lowering.lowK_killed | exact GlobalTheory.HolDict.Lowering.lowK_killed | (intros; apply GlobalTheory.HolDict.Lowering.lowK_killed <;> assumption)
