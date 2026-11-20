import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLabellingTransportGaloisConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLabAlt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UPoinc.UGalTrans.isLab_conj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryLabellingTransportGaloisConjugate.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.unitary_labelling_transport_galois_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → (∀ x, a (D.lab x) = D.lab x) → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → UIsLab D.X (D.lift ct (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  first | exact @GlobalTheory.UPoinc.UGalTrans.isLab_conj | exact GlobalTheory.UPoinc.UGalTrans.isLab_conj | (intros; apply GlobalTheory.UPoinc.UGalTrans.isLab_conj <;> assumption)
