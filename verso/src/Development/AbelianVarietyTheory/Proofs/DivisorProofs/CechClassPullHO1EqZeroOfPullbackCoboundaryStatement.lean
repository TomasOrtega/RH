import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassPullHO1EqZeroOfPullbackCoboundary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpOfIsCocycle
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CechCmp.pullHO1_cmp_eq_zero_of_coboundary` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCechClassPullHO1EqZeroOfPullbackCoboundary.lean&line=125#L125)
-/
theorem _root_.GlobalTheory.T.cechClass_pullHO1_eq_zero_of_pullback_coboundary : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) [Z.IsSeparated] (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ Z) (w : ι ≫ s = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) → GlobalTheory.CechDR.pullHO1 w (GlobalTheory.CechCmp.cmp s W hW c) = 0 := by
  first | exact @GlobalTheory.CechCmp.pullHO1_cmp_eq_zero_of_coboundary | exact GlobalTheory.CechCmp.pullHO1_cmp_eq_zero_of_coboundary | (intros; apply GlobalTheory.CechCmp.pullHO1_cmp_eq_zero_of_coboundary <;> assumption)
