import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopMulDescendedSubmoduleOfUnitCocycleEqTop
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DescTop.top_mul_descMod_eq_top` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTopMulDescendedSubmoduleOfUnitCocycleEqTop.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.top_mul_descendedSubmoduleOfUnitCocycle_eq_top : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] (u : (B ⊗[A] B)ˣ), UCoc A B u → (⊤ : Submodule A B) * descMod A B u = ⊤ := by
  first | exact @GlobalTheory.DescTop.top_mul_descMod_eq_top | exact GlobalTheory.DescTop.top_mul_descMod_eq_top | (intros; apply GlobalTheory.DescTop.top_mul_descMod_eq_top; all_goals assumption)
