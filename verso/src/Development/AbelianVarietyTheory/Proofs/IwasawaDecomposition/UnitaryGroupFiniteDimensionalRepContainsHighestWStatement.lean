import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupFiniteDimensionalRepContainsHighestW
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FUnitaryGroupFiniteDimensionalRepContainsHighestW.lean&line=317#L317)
-/
theorem _root_.GlobalTheory.T.unitaryGroup_finiteDimensionalRep_contains_highestWeightRep : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V), (∀ (l : Module.Dual ℂ V) (v : V), Continuous fun u => l (ρ u v)) → ∃ (lam : DomWeight n) (f : (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam).IntertwiningMap ρ), f ≠ 0 := by
  first | exact @GlobalTheory.UnitaryContainsType.exists_smallRep_intertwining | exact GlobalTheory.UnitaryContainsType.exists_smallRep_intertwining | (intros; apply GlobalTheory.UnitaryContainsType.exists_smallRep_intertwining <;> assumption)
