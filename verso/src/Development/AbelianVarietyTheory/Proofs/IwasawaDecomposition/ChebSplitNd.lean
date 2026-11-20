import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ChebSplitDense

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Supply the required witnesses or components.
-/
theorem chebSplit (hC : GlobalTheory.Published.ChebotarevDegreeOne) {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    (N : NData R H what₂) : GlobalTheory.RowTie.ChebSplit N := by
  intro S
  obtain ⟨A, hA, hsp⟩ := GlobalTheory.FrobDense.exists_finite_split H
  refine (hC.dense (F := H.E) (Ω := N.Om) (hA.union S.finite_toSet)).mono ?_
  rintro σ ⟨v, hv, hd, B, hB, hσ⟩
  simp only [Set.mem_union, Finset.mem_coe, not_or] at hv
  exact ⟨v, hv.2, hsp v hv.1 hd, B, hB, hσ⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem chebSplit_nd : GlobalTheory.Published.ChebotarevDegreeOne → ∀ D : D7, GlobalTheory.RowTie.ChebSplit D.nd :=
  fun hC D => chebSplit hC D.nd

end GlobalTheory.ChebSplitDense
