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
Use `(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_)` and prove the remaining obligations. Use `(val_cub D.cub (𝟙 (TK R)) hJ (cP D _ a) (cP D _ a') (cP D _ b)).trans ?_` and prove the remaining obligations. Rewrite using `[Category.id_comp, Category.id_comp, Category.id_comp]`.
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
Introduce `hG R _ _ j D D' pD hB a a' b`. Use `corr_of_val D'.P.isLB fun y J' hJ' => ?_` and prove the remaining obligations. Take `⟨J, hJ⟩` from `exists_good_at D.P.isLB y`. Establish `key : cubV D'.cub y J' (cP D' (TK R) a) (cP D' (TK R) a') (cP D' (TK R) b) * (om pD.w y J J' (cP D' (TK R) a * cP D' (TK R) a' * cP D' (TK R) b).left * (om pD.w y J J' (cP D' (TK R) a * cP D' (TK R) a').left)⁻¹ * (om pD.w y J J' (cP D' (TK R) a * cP D' (TK R) b).left)⁻¹ * (om pD. …` using `GlobalTheory.CubBox.cubV_box hG R j D D' pD (TK R) y J J' hJ hJ' _ _ _`. Establish `o : (1 : TK R ⟶ D'.P.A).left = 𝟙 _ ≫ (toUnit (TK R)).left ≫ eSec D'.P.A` using `(Category.id_comp _).symm`.

Rewrite `key` using `[o]`. Establish `t₁` using `tau_box pD hJ hJ' (a + a') b`. Establish `t₂` using `tau_box pD hJ hJ' a b`. Establish `t₃` using `tau_box pD hJ hJ' a' b`. Rewrite `t₁` using `[cPoint_add]`.

Establish `e : ∀ i, val (D.tau (pD.xe (a + a') i) (pD.xe b i)) (𝟙 _) y J * cubV D.cub y J (cP D' (TK R) a ≫ pD.pw.pr i) (cP D' (TK R) a' ≫ pD.pw.pr i) (cP D' (TK R) b ≫ pD.pw.pr i) = val (D.tau (pD.xe a i) (pD.xe b i)) (𝟙 _) y J * val (D.tau (pD.xe a' i) (pD.xe b i)) (𝟙 _) y J` using `fun i => by`. Use `(val_lhs D hJ _ _ _).symm.trans ((val_corr hJ (hB (pD.xe a i) (pD.xe a' i) (pD.xe b i)) (𝟙 _)).trans (val_mul hJ _ _ _))` as an intermediate fact. Rewrite using `[show pD.xe (a + a') i = pD.xe a i + pD.xe a' i by rw [map_add]; rfl, cP, cP, cP, Category.assoc, Category.assoc, Category.assoc, pD.c_pr, pD.c_pr, pD.c_pr]`. Conclude with `this`. Establish `E` using `(Finset.prod_mul_distrib).symm.trans ((Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) => e i).trans Finset.prod_mul_distrib)`.

Rewrite `E` using `[← t₁, ← t₂, ← t₃, ← key]`. Use `(val_lhs D' hJ' a a' b).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)` and prove the remaining obligations. Establish `E'` using `congrArg Additive.ofMul E`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv] at E' ⊢`.

Rewrite `E'`, the goal using `[← sub_eq_zero]`. Use `Eq.trans ?_ E'` and prove the remaining obligations. Normalize the expressions using the abelian group laws.
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
