import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ToMKExpKEqMatrixExpReal
import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FToMKExpKEqMatrixExpReal.lean&line=279#L279)
-/
theorem _root_.GlobalTheory.T.rightDeriv_norm_le_finite_words_bound : ∀ {n : ℕ} (ε : Fin n → Bool) (m : ℕ), ∃ (U : List (List (Mx n))) (C : ℝ), 0 ≤ C ∧ (∀ u ∈ U, ∀ X ∈ u, inK ε X) ∧ ∀ (d : ℕ) (φ : KG ε → ℂ), φ ∈ GlobalTheory.KFourier.polyV ε d → ∀ w : List (Mx n), w.length ≤ m → (∀ X ∈ w, inK ε X ∧ hs X ≤ 1) → ‖GlobalTheory.KFourier.rder ε w φ 1‖ ≤ C * (U.map fun u => ‖GlobalTheory.KFourier.rder ε u φ 1‖).sum := by
  first | exact @GlobalTheory.KFourier.rder_bound_basisWords | exact GlobalTheory.KFourier.rder_bound_basisWords | (intros; apply GlobalTheory.KFourier.rder_bound_basisWords <;> assumption)
