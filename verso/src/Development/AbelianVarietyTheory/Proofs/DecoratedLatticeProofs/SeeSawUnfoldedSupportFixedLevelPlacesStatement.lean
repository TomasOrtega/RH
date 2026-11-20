import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportFixedLevelPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSeeSawUnfoldedSupportFixedLevelPlaces.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.seeSaw_unfoldedSupport_fixedLevelPlaces : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → GlobalTheory.LocMod.GSupp1 D → GlobalTheory.LocMod.GSupp2 D → FlatLaw D → ∀ t : Tup c, t.Is → (∀ i, (G i).Chars t) → GSupp (t := t) v := by
  first | exact @GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local | exact GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local | (intros; apply GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local <;> assumption)
