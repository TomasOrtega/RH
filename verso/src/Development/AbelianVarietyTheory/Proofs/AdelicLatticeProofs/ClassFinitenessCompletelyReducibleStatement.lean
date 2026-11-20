import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassFinitenessCompletelyReducible
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FClassFinitenessCompletelyReducible.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.classFiniteness_completelyReducible : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → SS Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  first | exact @GlobalTheory.ClassFin.cf_of_ss | exact GlobalTheory.ClassFin.cf_of_ss | (intros; apply GlobalTheory.ClassFin.cf_of_ss <;> assumption)
