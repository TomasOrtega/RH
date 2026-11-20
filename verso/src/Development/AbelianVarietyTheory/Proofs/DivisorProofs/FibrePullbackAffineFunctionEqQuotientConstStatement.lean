import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePullbackAffineFunctionEqQuotientConst
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.fibre_restrict_scalar_compat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFibrePullbackAffineFunctionEqQuotientConst.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.fibre_pullback_affineFunction_eq_quotientConst : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), ι ≫ p = q ≫ spMap (Ideal.Quotient.mk m) ≫ chart U → ∀ (V : Z.Opens) (hV : V ≤ p ⁻¹ᵁ U.1) (V' : A.Opens) (hV' : V' ≤ ι ⁻¹ᵁ V) (r : Γ(X, U.1)), (ι.appLE V V' hV').hom ((p.appLE U.1 V hV).hom r) = (q.appLE ⊤ V' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m r)) := by
  first | exact @GlobalTheory.fibre_restrict_scalar_compat | exact GlobalTheory.fibre_restrict_scalar_compat | (intros; apply GlobalTheory.fibre_restrict_scalar_compat <;> assumption)
