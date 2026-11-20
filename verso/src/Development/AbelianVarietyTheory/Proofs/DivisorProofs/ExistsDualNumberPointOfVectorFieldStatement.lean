import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberPointOfVectorField
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EpsPoint.exists_epsPoint` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsDualNumberPointOfVectorField.lean&line=223#L223)
-/
theorem _root_.GlobalTheory.T.exists_dualNumberPoint_of_vectorField : ∀ (Z : Scheme.{0}) (W : Z.Opens) (e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W e → ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ Z), ⊤ ≤ g₀ ⁻¹ᵁ W → ∃ w : Sp (DualNumber S) ⟶ Z, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ ∧ ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (O : Z.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(Z, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = valR (spMap ρ ≫ g₀) O (e O f) := by
  first | exact @GlobalTheory.EpsPoint.exists_epsPoint | exact GlobalTheory.EpsPoint.exists_epsPoint | (intros; apply GlobalTheory.EpsPoint.exists_epsPoint <;> assumption)
