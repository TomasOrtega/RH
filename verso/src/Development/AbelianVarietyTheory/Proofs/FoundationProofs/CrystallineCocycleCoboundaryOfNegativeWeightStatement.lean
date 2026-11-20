import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleCoboundaryOfNegativeWeight
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCrystallineCocycleCoboundaryOfNegativeWeight.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.crystallineCocycle_coboundary_of_negative_weight : Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ), Continuous (fun σ => (κ σ : Qbar l)) → ∀ c : Coef l, (∀ σ, (κ σ : Qbar l) ∈ c.O) → ∀ w : ℤ, w < 0 → Loc.HasWeight (MonoidHom.id (GQ l)) κ w → ∀ f ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) (Loc.chRep κ), ∃ x, ∀ σ, f σ = (κ σ : Qbar l) * x - x := by
  first | exact @GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight | exact GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight | (intros; apply GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight <;> assumption)
