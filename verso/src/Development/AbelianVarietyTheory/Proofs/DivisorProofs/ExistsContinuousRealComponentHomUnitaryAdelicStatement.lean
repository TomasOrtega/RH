import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsContinuousRealComponentHomUnitaryAdelic.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_continuous_realComponentHom_unitaryAdelic : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V), V.SigOK → IsInfFam θ → IsFrames V A → ∃ rp : GA D V →* (∀ ρ, Upq V ρ), Continuous rp ∧ IsRealPart V θ A rp := by
  first | exact @GlobalTheory.CovTop.VolUp.exists_realPart_hom | exact GlobalTheory.CovTop.VolUp.exists_realPart_hom | (intros; apply GlobalTheory.CovTop.VolUp.exists_realPart_hom <;> assumption)
