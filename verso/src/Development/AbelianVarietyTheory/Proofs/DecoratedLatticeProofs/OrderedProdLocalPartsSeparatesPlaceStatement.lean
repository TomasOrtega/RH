import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrderedProdLocalPartsSeparatesPlace
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FOrderedProdLocalPartsSeparatesPlace.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.ordered_prod_local_parts_separates_place : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ) (xs : Fin n → GA D (c.V j')), (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) → ∀ (i : Fin n), ∃ y ∈ grpOff (c.V j') (· = (G i).q.v), (List.ofFn xs).prod = xs i * y := by
  first | exact @GlobalTheory.SeeSaw.SepProd.prod_sep | exact GlobalTheory.SeeSaw.SepProd.prod_sep | (intros; apply GlobalTheory.SeeSaw.SepProd.prod_sep <;> assumption)
