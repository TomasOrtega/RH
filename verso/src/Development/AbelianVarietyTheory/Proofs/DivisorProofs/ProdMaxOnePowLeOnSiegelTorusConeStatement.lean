import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMaxOnePowLeOnSiegelTorusCone
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConeMax.prod_max_le_prod` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProdMaxOnePowLeOnSiegelTorusCone.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.prod_max_one_pow_le_on_siegelTorusCone : ∀ (r m e : ℕ) (c : ℝ), 0 < c → ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∏ k : Fin r ⊕ Fin r ⊕ Fin m, max 1 (Sum.elim t (Sum.elim (fun i => (t i)⁻¹) (fun _ => (1 : ℝ))) k) ^ e ≤ C * ∏ i, t i ^ e := by
  first | exact @GlobalTheory.ConeMax.prod_max_le_prod | exact GlobalTheory.ConeMax.prod_max_le_prod | (intros; apply GlobalTheory.ConeMax.prod_max_le_prod <;> assumption)
