import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemisimplificationMatrixRepSameCharpoly
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SemisimplificationExists.exists_semisimplification` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsSemisimplificationMatrixRepSameCharpoly.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_semisimplification_matrix_rep_same_charpoly : ∀ {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k), ∃ ρ' : Γ →* GL (Fin a) k, IsSSRep ρ' ∧ ρ.ker ≤ ρ'.ker ∧ ∀ g, (ρ' g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly := by
  first | exact @GlobalTheory.SemisimplificationExists.exists_semisimplification | exact GlobalTheory.SemisimplificationExists.exists_semisimplification | (intros; apply GlobalTheory.SemisimplificationExists.exists_semisimplification <;> assumption)
