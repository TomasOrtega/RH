import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FlatZetaIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.MajFrame

/- English proof (translation)
Introduce `D θ A sA hθ hs`. Take `⟨a, ha, -, hfs⟩` from `GlobalTheory.Doubling.exists_isMaj_frameInv_eq hθ hs`. Use `⟨a, ha, fun τ => ?_⟩` and prove the remaining obligations. Take `⟨ε, hε⟩` from `(GlobalTheory.Doubling.isMaj_iff hθ).1 ha τ`. Rewrite using `[← hfs τ, GlobalTheory.Doubling.frameInv]`.

Establish `: (compAt θ τ a.1)ᴴ * (gramAt D A τ * (compAt θ τ a.1 * (compAt θ τ a.1)ᴴ * gramAt D A τ)) * compAt θ τ a.1 = ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[this, hε, Matrix.diagonal_mul_diagonal]`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, Matrix.one_apply] <;> split_ifs <;> simp`.
-/
theorem exists_maj_cart : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → ∃ a : GL (Fin A.rank) (AE D), IsMaj A a ∧ ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1 := by
  intro D θ A sA hθ hs
  obtain ⟨a, ha, -, hfs⟩ := GlobalTheory.Doubling.exists_isMaj_frameInv_eq hθ hs
  refine ⟨a, ha, fun τ => ?_⟩
  obtain ⟨ε, hε⟩ := (GlobalTheory.Doubling.isMaj_iff hθ).1 ha τ
  rw [← hfs τ, GlobalTheory.Doubling.frameInv]
  have : (compAt θ τ a.1)ᴴ * (gramAt D A τ * (compAt θ τ a.1 * (compAt θ τ a.1)ᴴ * gramAt D A τ)) * compAt θ τ a.1 =
      ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) := by
    simp only [Matrix.mul_assoc]
  rw [this, hε, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, Matrix.one_apply] <;> split_ifs <;> simp

end GlobalTheory.Core.Rk.MajFrame
