import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RatioTrans
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TauBimultBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.TauBalBox

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem val_lhs {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {y : (TK R).left} {J} (hJ : Good D.P.L y J)
    (a a' b : D.X) :
    val (LB.mulGen D.P.L _ _ _ _ (D.tau (a + a') b)
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b))) (𝟙 _) y J =
      val (D.tau (a + a') b) (𝟙 _) y J * cubV D.cub y J (cP D (TK R) a) (cP D (TK R) a') (cP D (TK R) b) := by
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_)
  refine (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ a) (cP D _ a') (cP D _ b)).trans ?_
  rw [Category.id_comp, Category.id_comp, Category.id_comp]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Normalize the expressions using the abelian group laws. A detailed English derivation is pending.
-/
theorem tauBimult_pow : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j), D.TauBimult → D'.TauBimult := by
  intro hG R _ _ j D D' pD hB a a' b
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  have key : cubV D'.cub y J' (cP D' (TK R) a) (cP D' (TK R) a') (cP D' (TK R) b) *
      (om pD.w y J J' (cP D' (TK R) a * cP D' (TK R) a' * cP D' (TK R) b).left *
        (om pD.w y J J' (cP D' (TK R) a * cP D' (TK R) a').left)⁻¹ *
        (om pD.w y J J' (cP D' (TK R) a * cP D' (TK R) b).left)⁻¹ *
        (om pD.w y J J' (cP D' (TK R) a' * cP D' (TK R) b).left)⁻¹ *
        om pD.w y J J' (cP D' (TK R) a).left * om pD.w y J J' (cP D' (TK R) a').left *
        om pD.w y J J' (cP D' (TK R) b).left *
        (om pD.w y J J' (1 : TK R ⟶ D'.P.A).left)⁻¹) = _ :=
    GlobalTheory.CubBox.cubV_box hG R j D D' pD (TK R) y J J' hJ hJ' _ _ _
  have o : (1 : TK R ⟶ D'.P.A).left = 𝟙 _ ≫ (toUnit (TK R)).left ≫ eSec D'.P.A := (Category.id_comp _).symm
  rw [o] at key
  have t₁ := tau_box pD hJ hJ' (a + a') b
  have t₂ := tau_box pD hJ hJ' a b
  have t₃ := tau_box pD hJ hJ' a' b
  rw [cPoint_add] at t₁
  have e : ∀ i, val (D.tau (pD.xe (a + a') i) (pD.xe b i)) (𝟙 _) y J *
      cubV D.cub y J (cP D' (TK R) a ≫ pD.pw.pr i) (cP D' (TK R) a' ≫ pD.pw.pr i) (cP D' (TK R) b ≫ pD.pw.pr i) =
      val (D.tau (pD.xe a i) (pD.xe b i)) (𝟙 _) y J * val (D.tau (pD.xe a' i) (pD.xe b i)) (𝟙 _) y J := fun i => by
    have := (val_lhs D hJ _ _ _).symm.trans
      ((val_corr hJ (hB (pD.xe a i) (pD.xe a' i) (pD.xe b i)) (𝟙 _)).trans (val_mul hJ _ _ _))
    rw [show pD.xe (a + a') i = pD.xe a i + pD.xe a' i by rw [map_add]; rfl, cP, cP, cP, Category.assoc,
      Category.assoc, Category.assoc, pD.c_pr, pD.c_pr, pD.c_pr]
    exact this
  have E := (Finset.prod_mul_distrib).symm.trans ((Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) => e i).trans
    Finset.prod_mul_distrib)
  rw [← t₁, ← t₂, ← t₃, ← key] at E
  refine (val_lhs D' hJ' a a' b).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  have E' := congrArg Additive.ofMul E
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at E' ⊢
  rw [← sub_eq_zero] at E' ⊢
  refine Eq.trans ?_ E'
  abel

end GlobalTheory.TauBimultBox
