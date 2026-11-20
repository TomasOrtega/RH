import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section

namespace GlobalTheory.Poinc.IntTerm

/- English proof (translation)
Introduce `V _ _ D`. Take `⟨z⟩` from `GlobalTheory.UT.CoefBasic.exists_pt (R := V) (F := FractionRing V)`. Take `⟨J', hJ'⟩` from `GlobalTheory.UT.CoefBasic.exists_good' D.P.isLB z`. Take `⟨c, hc⟩` from `GlobalTheory.UT.CoefBasic.cstH_surj z ((@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J')).val * (rigV D (TF (R := V) (FractionRing V)).hom z J').val)`. Use `⟨c, fun h => ?_, fun z' J hJ => ?_⟩` and prove the remaining obligations.

Rewrite `hc` using `[h, map_zero]`. Rewrite `hc` using `[← Units.val_mul]`. Conclude with `Units.ne_zero _ hc.symm`. Take `rfl` from `GlobalTheory.UT.CoefBasic.pt_eq z z'`. Establish `a₁` using `GlobalTheory.UT.CoefBasic.val_tr (D.psi_gen 0) (jFK (R := V) (FractionRing V)) hJ hJ'`.

Establish `a₂ : rigV D (TF (R` using `V) (FractionRing V)).hom z J = GlobalTheory.UT.CoefBasic.trU D.P.L z J J' ((TF (R := V) (FractionRing V)).hom ≫ eSec D.P.A) * rigV D (TF (R := V) (FractionRing V)).hom z J' := by`. Use `(GlobalTheory.UT.CoefBasic.val_tr (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig_gen (TF (R := V) (FractionRing V)).hom hJ hJ').trans ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_unique, zpow_one]`. Both sides reduce to the same expression. Establish `e : jFK (R` using `V) (FractionRing V) ≫ ptK (D.c 0) = (TF (R := V) (FractionRing V)).hom ≫ eSec D.P.A := by`.

Rewrite using `[GlobalTheory.Poinc.ThetaOne.c_zero]`. Both sides reduce to the same expression. Simplify using `only [e] at a₁`. Rewrite using `[GlobalTheory.UT.CoefBasic.cst_eq, hc]`. Use `show (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J).val * _ = _`.

Rewrite using `[a₁, a₂, ← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Simplify using `only [Fintype.prod_unique, Finset.prod_const, Finset.card_univ, Fintype.card_unique, pow_one, zpow_neg, zpow_one, id]`. Rewrite using `[_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]`.
-/
theorem psi_zero_rig_const : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), ∃ c₀ : FractionRing V, c₀ ≠ 0 ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = GlobalTheory.UT.cst (FractionRing V) z c₀ := by
  intro V _ _ D
  obtain ⟨z⟩ := GlobalTheory.UT.CoefBasic.exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J', hJ'⟩ := GlobalTheory.UT.CoefBasic.exists_good' D.P.isLB z
  obtain ⟨c, hc⟩ := GlobalTheory.UT.CoefBasic.cstH_surj z
    ((@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J')).val * (rigV D (TF (R := V) (FractionRing V)).hom z J').val)
  refine ⟨c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    rw [← Units.val_mul] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl := GlobalTheory.UT.CoefBasic.pt_eq z z'
    have a₁ := GlobalTheory.UT.CoefBasic.val_tr (D.psi_gen 0) (jFK (R := V) (FractionRing V)) hJ hJ'
    have a₂ : rigV D (TF (R := V) (FractionRing V)).hom z J =
        GlobalTheory.UT.CoefBasic.trU D.P.L z J J' ((TF (R := V) (FractionRing V)).hom ≫ eSec D.P.A) *
        rigV D (TF (R := V) (FractionRing V)).hom z J' := by
      refine (GlobalTheory.UT.CoefBasic.val_tr (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig_gen
        (TF (R := V) (FractionRing V)).hom hJ hJ').trans ?_
      rw [Fintype.prod_unique, zpow_one]; rfl
    have e : jFK (R := V) (FractionRing V) ≫ ptK (D.c 0) = (TF (R := V) (FractionRing V)).hom ≫ eSec D.P.A := by
      rw [GlobalTheory.Poinc.ThetaOne.c_zero]
      rfl
    simp only [e] at a₁
    rw [GlobalTheory.UT.CoefBasic.cst_eq, hc]
    show (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J).val * _ = _
    rw [a₁, a₂, ← Units.val_mul, ← Units.val_mul]
    congr 1
    simp only [Fintype.prod_unique, Finset.prod_const, Finset.card_univ, Fintype.card_unique, pow_one, zpow_neg,
      zpow_one, id]
    rw [_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]

end GlobalTheory.Poinc.IntTerm

end
