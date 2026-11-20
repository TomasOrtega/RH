import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapRealTranslateEqRightTranslation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurMultMultiplicitySpacesOfRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmoothTranslate.translate` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FMultiplicityMapRealTranslateEqRightTranslation.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.multiplicityMap_realTranslate_eq_rightTranslation : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : ∀ τ, Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ, ∃ P ∈ GinfC V, ∀ (v : M.Vec) (x : GA D V), T (fun τ => ⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ), GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩) x = T v (x * P) := by
  first | exact @GlobalTheory.SmoothTranslate.translate | exact GlobalTheory.SmoothTranslate.translate | (intros; apply GlobalTheory.SmoothTranslate.translate <;> assumption)
