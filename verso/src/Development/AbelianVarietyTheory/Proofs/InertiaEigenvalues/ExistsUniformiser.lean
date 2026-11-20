import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLocUnif

/- English proof (translation)
Introduce `l _ LL`. Take `⟨hdvr, -⟩` from `GlobalTheory.FinExtIntegers.dvr_complete LL`. Conclude with `IsDiscreteValuationRing.exists_irreducible ↥(OL LL)`.
-/
theorem exists_uniformiser : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), ∃ lam : ↥(OL LL), Irreducible lam := by
  intro l _ LL
  obtain ⟨hdvr, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  exact IsDiscreteValuationRing.exists_irreducible ↥(OL LL)

end GlobalTheory.UseLocUnif
