import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecVectorFieldOfDualNumberSection
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSpecVectorFieldOfDualNumberSection.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.exists_spec_vectorField_of_dualNumber_section : ∀ (A : Type) [CommRing A] (σ : A →+* DualNumber A), (∀ a, (σ a).fst = a) → ∃ d : ∀ O : (Sp A).Opens, Γ(Sp A, O) → Γ(Sp A, O), IsField ⊤ d ∧ ∀ a : A, d ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd := by
  first | exact @GlobalTheory.SpecField.exists_isField | exact GlobalTheory.SpecField.exists_isField | (intros; apply GlobalTheory.SpecField.exists_isField <;> assumption)
