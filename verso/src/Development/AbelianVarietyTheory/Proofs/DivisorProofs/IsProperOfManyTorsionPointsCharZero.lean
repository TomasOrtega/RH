import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSmConnOfIsProperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupOfManyTorsionCharPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismOpenAffineLineAbelianSchemeConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonconstantRationalCurveNonproperGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharPSpecialisationSmoothCommGroupCurveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ManyTorsionProper

/- English proof (translation)
Introduce `k _ _ _ G _ hG g hg m s hs hcard`. Assume the negation of the conclusion as `hnp`. Establish `hm : 1 ≤ m`. Break down `Nat.eq_zero_or_pos m with h | h` into its components or cases. Substitute `h` using the available equality.

Simplify using `at hcard`. Conclude with `h`. Take `⟨P, hP, u, a, b, hu, hab⟩` from `GlobalTheory.T.exists_nonconstant_rational_curve_nonproper_group k G hG hnp`. Take `⟨k', _, _, p, _, _, G', _, hG', hg', hm', ⟨s', hs', hc'⟩, P', hP', u', a', b', hu', hab'⟩` from `GlobalTheory.T.exists_charP_specialization_smooth_commGroup_curve k G hG g hg m hm s hs P hP u a b hu hab`. Establish `hpr : IsProper G'.hom` using `GlobalTheory.T.isProper_smoothConnGroup_of_many_torsion_charP k' p G' hG' g hg' m hm' s' hs' (by rw [hc']; exact hcard)`.

Conclude with `hab' (GlobalTheory.T.morphism_open_affine_line_abelianScheme_const k' G' (GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' _ G' hG' hpr) P' hP' u' a' b' hu')`.
-/
theorem isProper_of_many_torsion_charZero : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  intro k _ _ _ G _ hG g hg m s hs hcard
  by_contra hnp
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at hcard
    · exact h
  obtain ⟨P, hP, u, a, b, hu, hab⟩ := GlobalTheory.T.exists_nonconstant_rational_curve_nonproper_group k G hG hnp
  obtain ⟨k', _, _, p, _, _, G', _, hG', hg', hm', ⟨s', hs', hc'⟩, P', hP', u', a', b', hu', hab'⟩ :=
    GlobalTheory.T.exists_charP_specialization_smooth_commGroup_curve k G hG g hg m hm s hs P hP u a b hu hab
  have hpr : IsProper G'.hom :=
    GlobalTheory.T.isProper_smoothConnGroup_of_many_torsion_charP k' p G' hG' g hg' m hm' s' hs' (by rw [hc']; exact hcard)
  exact hab' (GlobalTheory.T.morphism_open_affine_line_abelianScheme_const k' G' (GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' _ G' hG' hpr) P' hP' u' a' b' hu')

end GlobalTheory.ManyTorsionProper
