import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCocyclesLeCoboundariesAddSelmer
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LenCob
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLengthCocyclesLeCoboundariesAddSelmer.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.length_cocycles_le_coboundaries_add_selmer : ∀ (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) D.R.r)), C ≤ Z1 (WKG (WpO D.nd i ρ π)) → (∀ f ∈ C, IsFinL i (WpO D.nd i ρ π) f) → (∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i → resIne i C v = ⊥) → Module.length (D.nd.O i) ↥C ≤ lenCob i (WpO D.nd i ρ π) (C) + Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i ρ π) := by
  first | exact @GlobalTheory.Cut.SelClass.main | exact GlobalTheory.Cut.SelClass.main | (intros; apply GlobalTheory.Cut.SelClass.main <;> assumption)
