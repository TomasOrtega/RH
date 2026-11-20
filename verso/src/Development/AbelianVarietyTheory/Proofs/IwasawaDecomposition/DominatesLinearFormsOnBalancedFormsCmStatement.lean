import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominatesLinearFormsOnBalancedFormsCm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DomBal.dominates` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDominatesLinearFormsOnBalancedFormsCm.lean&line=456#L456)
-/
theorem _root_.GlobalTheory.T.dominatesLinearFormsOnBalancedForms_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X := by
  first | exact @GlobalTheory.DomBal.dominates | exact GlobalTheory.DomBal.dominates | (intros; apply GlobalTheory.DomBal.dominates <;> assumption)
