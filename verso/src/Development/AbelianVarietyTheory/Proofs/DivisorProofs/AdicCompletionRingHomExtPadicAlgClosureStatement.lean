import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionRingHomExtPadicAlgClosure
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdicCompletionRingHomExtPadicAlgClosure.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.adicCompletion_ringHom_ext_padicAlgClosure : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (p : ℕ) [Fact p.Prime] (f g : AdicCompletion (maximalIdeal O) O →+* OO p), IsLocalHom (f.comp (algebraMap O _)) → (∀ a, f (algebraMap O _ a) = g (algebraMap O _ a)) → f = g := by
  first | exact @GlobalTheory.AdicExt.completion_ringHom_ext | exact GlobalTheory.AdicExt.completion_ringHom_ext | (intros; apply GlobalTheory.AdicExt.completion_ringHom_ext <;> assumption)
