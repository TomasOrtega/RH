import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData.ExpandPf

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

/- English proof (translation)
Set `f : D.X →+ Additive (T ⟶ D.P.A)` to `AddMonoidHom.mk' (fun a => Additive.ofMul (DVR.cP D T a)) (fun a b => by`. Rewrite using `[DVR.cPoint_add]`. Use the proof step `rfl)`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `e : Additive.ofMul (DVR.cP D T (∑ i, n i • b i)) = ∑ i, n i • f (b i)` using `(map_sum f (fun i => n i • b i) Finset.univ).trans (Finset.sum_congr rfl fun i _ => map_zsmul f _ _)`.

Rewrite using `[e, ofMul_prod]`. Simplify using `only [ofMul_zpow]`. Both sides reduce to the same expression.
-/
theorem cPoint_sum (T : Over (Sp R)) {K : Type} [Fintype K] (n : K → ℤ) (b : K → D.X) :
    DVR.cP D T (∑ i, n i • b i) = ∏ i, DVR.cP D T (b i) ^ n i := by
  let f : D.X →+ Additive (T ⟶ D.P.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (DVR.cP D T a)) (fun a b => by
      rw [DVR.cPoint_add]; rfl)
  apply Additive.ofMul.injective
  have e : Additive.ofMul (DVR.cP D T (∑ i, n i • b i)) = ∑ i, n i • f (b i) :=
    (map_sum f (fun i => n i • b i) Finset.univ).trans (Finset.sum_congr rfl fun i _ => map_zsmul f _ _)
  rw [e, ofMul_prod]
  simp only [ofMul_zpow]
  rfl

/- English proof (translation)
Establish `C : IsCub (DVR.th D (T` using `TK R) z J) := isCub_cubV D.cub hJ`. Establish `e` using `GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ hB 0 0 a`. Establish `c0 : DVR.cP D (TK R) 0 = 1`. Use `DVR.cPoint_add D (TK R) 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`.

Conclude with `mul_eq_left.1 this.symm`. Establish `s` using `GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a 0`. Simplify using `only [Over.id_left] at s e`. Rewrite `e` using `[add_zero, c0, C.face, _root_.mul_one]`. Rewrite using `[s]`.

Conclude with `mul_eq_left.1 e.symm`.
-/
theorem val_tau_zero_right (hB : D.TauBimult) (a : D.X) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) : val (D.tau a 0) (𝟙 _) z J = 1 := by
  have C : IsCub (DVR.th D (T := TK R) z J) := isCub_cubV D.cub hJ
  have e := GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ hB 0 0 a
  have c0 : DVR.cP D (TK R) 0 = 1 := by
    have := DVR.cPoint_add D (TK R) 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have s := GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a 0
  simp only [Over.id_left] at s e
  rw [add_zero, c0, C.face, _root_.mul_one] at e
  rw [s]
  exact mul_eq_left.1 e.symm

end GlobalTheory.Mum.PowData.ExpandPf

namespace GlobalTheory.Mum.PowData.ExpandPf

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {K : Type} [Fintype K] {T : Over (Sp R)}
  (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A))

/- English proof (translation)
Introduce `_ _` and use `(map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm`.
-/
theorem oneGen_isGen' : (LB.oneGen D.P.L (Y := T.left)).IsGen :=
  fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

/- English proof (translation)
Take `⟨κ, hκ, hv⟩` from `exists_gen D.P.isLB (φ' := Sum.elim (lamPts x (∏ i, y i ^ (0 : K → ℤ) i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2)) (ε' := Sum.elim Oε (fun k : K × Fin 4 => -((0 : K → ℤ) k.1 * Oε k.2))) (fun U _ h => by`. Simplify using `[Fintype.prod_sum_type, lamPts, Oε, Fin.prod_univ_four])`. Use the proof step `(LB.oneGen D.P.L (Y := T.left)) oneGen_isGen'`. Use `⟨κ, hκ, fun p a b hx hy z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[hv _ _ z J hJ, val_one]`.

Establish `e0 : (∑ i, (0 : K → ℤ) i • b i) = 0` using `by simp`. Establish `e1 : (∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ (0 : K → ℤ) i) = 1` using `by simp`. Rewrite using `[e0, e1, _root_.mul_one]`. Conclude with `val_tau_zero_right hB a hJ`.
-/
theorem expand_zero (hB : D.TauBimult) : Expand D (0 : K → ℤ) x y := by
  obtain ⟨κ, hκ, hv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (lamPts x (∏ i, y i ^ (0 : K → ℤ) i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2))
    (ε' := Sum.elim Oε (fun k : K × Fin 4 => -((0 : K → ℤ) k.1 * Oε k.2)))
    (fun U _ h => by
      simp [Fintype.prod_sum_type, lamPts, Oε, Fin.prod_univ_four])
    (LB.oneGen D.P.L (Y := T.left)) oneGen_isGen'
  refine ⟨κ, hκ, fun p a b hx hy z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_one]
  have e0 : (∑ i, (0 : K → ℤ) i • b i) = 0 := by simp
  have e1 : (∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ (0 : K → ℤ) i) = 1 := by simp
  rw [e0, e1, _root_.mul_one]
  exact val_tau_zero_right hB a hJ

end GlobalTheory.Mum.PowData.ExpandPf

namespace GlobalTheory.Mum.PowData.ExpandPf

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {K : Type} [Fintype K] {T : Over (Sp R)}
  (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A))

/- English proof (translation)
Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add, Pi.add_apply]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_exp_add {U : Type} [CommGroup U] (f : K × Fin 4 → U) (w w' : K → ℤ) :
    ∏ k, f k ^ (-((w + w') k.1 * Oε k.2)) = (∏ k, f k ^ (-(w k.1 * Oε k.2))) * ∏ k, f k ^ (-(w' k.1 * Oε k.2)) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add, Pi.add_apply]
  congr 1
  ring

/- English proof (translation)
Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, zpow_add]`.
-/
theorem prod_zpow_add (w w' : K → ℤ) : ∏ i, y i ^ (w + w') i = (∏ i, y i ^ w i) * ∏ i, y i ^ w' i := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, zpow_add]

/- English proof (translation)
Rewrite using `[prod_cub, Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[prod_exp_add (fun k => h (lamPts x (y k.1) k.2)) w w', prod_zpow_add y w w']`. Generalize the expression as in `(∏ k : K × Fin 4, h (lamPts x (y k.1) k.2) ^ (-(w k.1 * Oε k.2))) = P`. Generalize the expression as in `(∏ k : K × Fin 4, h (lamPts x (y k.1) k.2) ^ (-(w' k.1 * Oε k.2))) = P'`.

Generalize the expression as in `(∏ i, y i ^ w i) = Y`. Generalize the expression as in `(∏ i, y i ^ w' i) = Y'`. Establish `e1 : x * (Y * Y') = Y * Y' * x` using `mul_comm _ _`. Establish `e2 : x * Y = Y * x` using `mul_comm _ _`. Establish `e3 : x * Y' = Y' * x` using `mul_comm _ _`.

Simplify using `only [Fin.prod_univ_four, lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, e1, e2, e3]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow]`. Normalize the expressions using the abelian group laws.
-/
theorem formEq_add (w w' : K → ℤ) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    (∏ k, h (Sum.elim (lamPts x (∏ i, y i ^ (w + w') i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2) k) ^
        Sum.elim Oε (fun k : K × Fin 4 => -((w + w') k.1 * Oε k.2)) k) =
      (∏ k, h (Sum.elim (lamPts x (∏ i, y i ^ w i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2) k) ^
        Sum.elim Oε (fun k : K × Fin 4 => -(w k.1 * Oε k.2)) k) *
      (∏ k, h (Sum.elim (lamPts x (∏ i, y i ^ w' i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2) k) ^
        Sum.elim Oε (fun k : K × Fin 4 => -(w' k.1 * Oε k.2)) k) *
      ∏ I : thK, h ((lift (∏ i, y i ^ w i) (lift (∏ i, y i ^ w' i) x)).left ≫ thφ D.P.A (x3 D.P.A) I) ^ thε I := by
  rw [prod_cub, Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [prod_exp_add (fun k => h (lamPts x (y k.1) k.2)) w w', prod_zpow_add y w w']
  generalize (∏ k : K × Fin 4, h (lamPts x (y k.1) k.2) ^ (-(w k.1 * Oε k.2))) = P
  generalize (∏ k : K × Fin 4, h (lamPts x (y k.1) k.2) ^ (-(w' k.1 * Oε k.2))) = P'
  generalize (∏ i, y i ^ w i) = Y
  generalize (∏ i, y i ^ w' i) = Y'
  have e1 : x * (Y * Y') = Y * Y' * x := mul_comm _ _
  have e2 : x * Y = Y * x := mul_comm _ _
  have e3 : x * Y' = Y' * x := mul_comm _ _
  simp only [Fin.prod_univ_four, lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, e1, e2, e3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  abel

end GlobalTheory.Mum.PowData.ExpandPf

namespace GlobalTheory.Mum.PowData.ExpandPf

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {K : Type} [Fintype K] {T : Over (Sp R)}
  (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A))

/- English proof (translation)
Rewrite using `[comp_prod_zpow, cPoint_sum]`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [hy i]; rfl`.
-/
theorem comp_prod_cP {p : TK R ⟶ T} {b : K → D.X} (hy : ∀ i, p ≫ y i = toUnit _ ≫ D.c (b i)) (w : K → ℤ) :
    p ≫ ∏ i, y i ^ w i = DVR.cP D (TK R) (∑ i, w i • b i) := by
  rw [comp_prod_zpow, cPoint_sum]
  exact Finset.prod_congr rfl fun i _ => by rw [hy i]; rfl

/- English proof (translation)
Establish `e` using `GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ hB B B' a`. Establish `s1` using `GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a (B + B')`. Establish `s2` using `GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a B`. Establish `s3` using `GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a B'`. Simplify using `only [Over.id_left] at e s1 s2 s3`.

Rewrite using `[s1, s2, s3]`. Conclude with `e`.
-/
theorem val_tau_add_right (hB : D.TauBimult) (a B B' : D.X) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) :
    val (D.tau a (B + B')) (𝟙 _) z J * cubV D.cub z J (DVR.cP D (TK R) B) (DVR.cP D (TK R) B') (DVR.cP D (TK R) a) =
      val (D.tau a B) (𝟙 _) z J * val (D.tau a B') (𝟙 _) z J := by
  have e := GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ hB B B' a
  have s1 := GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a (B + B')
  have s2 := GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a B
  have s3 := GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a B'
  simp only [Over.id_left] at e s1 s2 s3
  rw [s1, s2, s3]
  exact e

/- English proof (translation)
Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, add_smul]`.
-/
theorem sum_add_smul (w w' : K → ℤ) (b : K → D.X) : ∑ i, (w + w') i • b i = ∑ i, w i • b i + ∑ i, w' i • b i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, add_smul]

/- English proof (translation)
Take `⟨κ, hκ, hv⟩` from `h₁`. Take `⟨κ', hκ', hv'⟩` from `h₂`. Take `⟨κ₂, hκ₂, hv₂⟩` from `exists_gen D.P.isLB (φ' := Sum.elim (lamPts x (∏ i, y i ^ (w + w') i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2)) (ε' := Sum.elim Oε (fun k : K × Fin 4 => -((w + w') k.1 * Oε k.2))) (fun U _ h => by`. Conclude with `((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (Fintype.prod_sum_type _) rfl)).trans (formEq_add x y w w' h).symm)`. Use the proof step `(LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ κ κ') (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (∏ i, y i ^ w i) (lift (∏ i, y i ^ w' i) x)).left))`.

Use the proof step `(DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hκ hκ') (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))`. Use `⟨κ₂, hκ₂, fun p a b hx hy z J hJ => ?_⟩` and prove the remaining obligations. Establish `c` using `val_cub D.cub p hJ (∏ i, y i ^ w i) (∏ i, y i ^ w' i) x`. Rewrite `c` using `[comp_prod_cP y hy w, comp_prod_cP y hy w', hx]`. Establish `e` using `val_tau_add_right hB a (∑ i, w i • b i) (∑ i, w' i • b i) hJ`.

Establish `e₁` using `hv p a b hx hy z J hJ`. Establish `e₂` using `hv' p a b hx hy z J hJ`. Establish `hm : val κ₂ p.left z J = val κ p.left z J * val κ' p.left z J * cubV D.cub z J (DVR.cP D (TK R) (∑ i, w i • b i)) (DVR.cP D (TK R) (∑ i, w' i • b i)) (DVR.cP D (TK R) a)` using `(hv₂ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) c))`. Rewrite using `[hm, sum_add_smul]`. Establish `hp : ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ (w + w') i = (∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w i) * ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w' i`.

Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, zpow_add]`. Rewrite using `[hp, ← e₁, ← e₂]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem expand_add (hB : D.TauBimult) {w w' : K → ℤ} (h₁ : Expand D w x y) (h₂ : Expand D w' x y) :
    Expand D (w + w') x y := by
  obtain ⟨κ, hκ, hv⟩ := h₁
  obtain ⟨κ', hκ', hv'⟩ := h₂
  obtain ⟨κ₂, hκ₂, hv₂⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (lamPts x (∏ i, y i ^ (w + w') i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2))
    (ε' := Sum.elim Oε (fun k : K × Fin 4 => -((w + w') k.1 * Oε k.2)))
    (fun U _ h => by
      exact ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (Fintype.prod_sum_type _) rfl)).trans
        (formEq_add x y w w' h).symm)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ κ κ')
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (∏ i, y i ^ w i) (lift (∏ i, y i ^ w' i) x)).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hκ hκ') (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
  refine ⟨κ₂, hκ₂, fun p a b hx hy z J hJ => ?_⟩
  have c := val_cub D.cub p hJ (∏ i, y i ^ w i) (∏ i, y i ^ w' i) x
  rw [comp_prod_cP y hy w, comp_prod_cP y hy w', hx] at c
  have e := val_tau_add_right hB a (∑ i, w i • b i) (∑ i, w' i • b i) hJ
  have e₁ := hv p a b hx hy z J hJ
  have e₂ := hv' p a b hx hy z J hJ
  have hm : val κ₂ p.left z J = val κ p.left z J * val κ' p.left z J *
      cubV D.cub z J (DVR.cP D (TK R) (∑ i, w i • b i)) (DVR.cP D (TK R) (∑ i, w' i • b i)) (DVR.cP D (TK R) a) :=
    (hv₂ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) c))
  rw [hm, sum_add_smul]
  have hp : ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ (w + w') i =
      (∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w i) * ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w' i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, zpow_add]
  rw [hp, ← e₁, ← e₂]
  calc _ = (val (D.tau a (∑ i, w i • b i + ∑ i, w' i • b i)) (𝟙 _) z J *
          cubV D.cub z J (DVR.cP D (TK R) (∑ i, w i • b i)) (DVR.cP D (TK R) (∑ i, w' i • b i)) (DVR.cP D (TK R) a)) *
          val κ p.left z J * val κ' p.left z J := by ac_rfl
    _ = _ := by rw [e]; ac_rfl

end GlobalTheory.Mum.PowData.ExpandPf

namespace GlobalTheory.Mum.PowData.ExpandPf

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {K : Type} [Fintype K] {T : Over (Sp R)}
  (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A))

/- English proof (translation)
Rewrite using `[formEq_add x y w w' h]`. Simplify using `only [zpow_neg, Finset.prod_inv_distrib]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem formEq_sub (w w' : K → ℤ) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    (∏ k, h (Sum.elim (lamPts x (∏ i, y i ^ (w + w') i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2) k) ^
        Sum.elim Oε (fun k : K × Fin 4 => -((w + w') k.1 * Oε k.2)) k) *
      (∏ k, h (Sum.elim (lamPts x (∏ i, y i ^ w i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2) k) ^
        (-Sum.elim Oε (fun k : K × Fin 4 => -(w k.1 * Oε k.2)) k)) *
      (∏ I : thK, h ((lift (∏ i, y i ^ w i) (lift (∏ i, y i ^ w' i) x)).left ≫ thφ D.P.A (x3 D.P.A) I) ^ (-thε I)) =
    ∏ k, h (Sum.elim (lamPts x (∏ i, y i ^ w' i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2) k) ^
        Sum.elim Oε (fun k : K × Fin 4 => -(w' k.1 * Oε k.2)) k := by
  rw [formEq_add x y w w' h]
  simp only [zpow_neg, Finset.prod_inv_distrib]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- English proof (translation)
Take `⟨κ, hκ, hv⟩` from `h₁`. Take `⟨κ₃, hκ₃, hv₃⟩` from `h₃`. Take `⟨κ₂, hκ₂, hv₂⟩` from `exists_gen D.P.isLB (φ' := Sum.elim (lamPts x (∏ i, y i ^ w' i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2)) (ε' := Sum.elim Oε (fun k : K × Fin 4 => -(w' k.1 * Oε k.2))) (fun U _ h => by`. Conclude with `((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (Fintype.prod_sum_type _) rfl)).trans (formEq_sub x y w w' h))`. Use the proof step `(LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ κ₃ (LB.invGen D.P.L _ _ κ)) (LB.invGen D.P.L _ _ (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (∏ i, y i ^ w i) (lift (∏ i, y i ^ w' i) x)).left)))`.

Use the proof step `(DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hκ₃ (DVR.invGen_isGen _ _ _ _ hκ)) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)))`. Use `⟨κ₂, hκ₂, fun p a b hx hy z J hJ => ?_⟩` and prove the remaining obligations. Establish `c` using `val_cub D.cub p hJ (∏ i, y i ^ w i) (∏ i, y i ^ w' i) x`. Rewrite `c` using `[comp_prod_cP y hy w, comp_prod_cP y hy w', hx]`. Establish `e` using `val_tau_add_right hB a (∑ i, w i • b i) (∑ i, w' i • b i) hJ`.

Establish `e₁` using `hv p a b hx hy z J hJ`. Establish `e₃` using `hv₃ p a b hx hy z J hJ`. Establish `hm : val κ₂ p.left z J = val κ₃ p.left z J * (val κ p.left z J)⁻¹ * (cubV D.cub z J (DVR.cP D (TK R) (∑ i, w i • b i)) (DVR.cP D (TK R) (∑ i, w' i • b i)) (DVR.cP D (TK R) a))⁻¹` using `(hv₂ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) ((val_inv _ _).trans (congrArg _ c))))`. Establish `hp : ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ (w + w') i = (∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w i) * ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w' i`. Rewrite using `[← Finset.prod_mul_distrib]`.

Conclude with `Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, zpow_add]`. Rewrite `e₃` using `[sum_add_smul, hp, ← e₁]`. Rewrite using `[hm]`. Generalize the expression as in `val (D.tau a (∑ i, w i • b i + ∑ i, w' i • b i)) (𝟙 _) z J = t₃ at e e₃`. Generalize the expression as in `val (D.tau a (∑ i, w i • b i)) (𝟙 _) z J = t₁ at e e₃`.

Generalize the expression as in `val (D.tau a (∑ i, w' i • b i)) (𝟙 _) z J = t₂ at e ⊢`. Generalize the expression as in `cubV D.cub z J (DVR.cP D (TK R) (∑ i, w i • b i)) (DVR.cP D (TK R) (∑ i, w' i • b i)) (DVR.cP D (TK R) a) = C at e ⊢`. Generalize the expression as in `val κ₃ p.left z J = k₃ at e₃ ⊢`. Generalize the expression as in `val κ p.left z J = k₁ at e₃ ⊢`. Generalize the expression as in `∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w' i = P at e₃ ⊢`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `a₁` using `congrArg Additive.ofMul e`. Establish `a₃` using `congrArg Additive.ofMul e₃`. Simplify using `only [ofMul_mul, ofMul_inv] at a₁ a₃ ⊢`. Take the linear combination `(norm := abel) a₃ - a₁`.
-/
theorem expand_sub (hB : D.TauBimult) {w w' : K → ℤ} (h₁ : Expand D w x y) (h₃ : Expand D (w + w') x y) :
    Expand D w' x y := by
  obtain ⟨κ, hκ, hv⟩ := h₁
  obtain ⟨κ₃, hκ₃, hv₃⟩ := h₃
  obtain ⟨κ₂, hκ₂, hv₂⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (lamPts x (∏ i, y i ^ w' i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2))
    (ε' := Sum.elim Oε (fun k : K × Fin 4 => -(w' k.1 * Oε k.2)))
    (fun U _ h => by
      exact ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (Fintype.prod_sum_type _) rfl)).trans
        (formEq_sub x y w w' h))
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ κ₃ (LB.invGen D.P.L _ _ κ))
      (LB.invGen D.P.L _ _
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (∏ i, y i ^ w i) (lift (∏ i, y i ^ w' i) x)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hκ₃ (DVR.invGen_isGen _ _ _ _ hκ))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)))
  refine ⟨κ₂, hκ₂, fun p a b hx hy z J hJ => ?_⟩
  have c := val_cub D.cub p hJ (∏ i, y i ^ w i) (∏ i, y i ^ w' i) x
  rw [comp_prod_cP y hy w, comp_prod_cP y hy w', hx] at c
  have e := val_tau_add_right hB a (∑ i, w i • b i) (∑ i, w' i • b i) hJ
  have e₁ := hv p a b hx hy z J hJ
  have e₃ := hv₃ p a b hx hy z J hJ
  have hm : val κ₂ p.left z J = val κ₃ p.left z J * (val κ p.left z J)⁻¹ *
      (cubV D.cub z J (DVR.cP D (TK R) (∑ i, w i • b i)) (DVR.cP D (TK R) (∑ i, w' i • b i)) (DVR.cP D (TK R) a))⁻¹ :=
    (hv₂ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) ((val_inv _ _).trans (congrArg _ c))))
  have hp : ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ (w + w') i =
      (∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w i) * ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w' i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, zpow_add]
  rw [sum_add_smul, hp, ← e₁] at e₃
  rw [hm]
  generalize val (D.tau a (∑ i, w i • b i + ∑ i, w' i • b i)) (𝟙 _) z J = t₃ at e e₃
  generalize val (D.tau a (∑ i, w i • b i)) (𝟙 _) z J = t₁ at e e₃
  generalize val (D.tau a (∑ i, w' i • b i)) (𝟙 _) z J = t₂ at e ⊢
  generalize cubV D.cub z J (DVR.cP D (TK R) (∑ i, w i • b i)) (DVR.cP D (TK R) (∑ i, w' i • b i))
    (DVR.cP D (TK R) a) = C at e ⊢
  generalize val κ₃ p.left z J = k₃ at e₃ ⊢
  generalize val κ p.left z J = k₁ at e₃ ⊢
  generalize ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w' i = P at e₃ ⊢
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e
  have a₃ := congrArg Additive.ofMul e₃
  simp only [ofMul_mul, ofMul_inv] at a₁ a₃ ⊢
  linear_combination (norm := abel) a₃ - a₁

end GlobalTheory.Mum.PowData.ExpandPf

namespace GlobalTheory.Mum.PowData.ExpandPf

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {K : Type} [Fintype K] {T : Over (Sp R)}
  (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A))

/- English proof (translation)
Establish `hY : ∏ i, y i ^ (Pi.single j (1 : ℤ) : K → ℤ) i = y j`. Rewrite using `[Fintype.prod_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]`. Simplify using the standard rewrite rules. Establish `hK : ∀ {U : Type} [CommGroup U] (f : K × Fin 4 → U), ∏ k, f k ^ (-((Pi.single j (1 : ℤ) : K → ℤ) k.1 * Oε k.2)) = ∏ m, f (j, m) ^ (-Oε m)`. Introduce `U _ f`.

Rewrite using `[Fintype.prod_prod_type, Fintype.prod_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]`. Simplify using the standard rewrite rules. Take `⟨κ, hκ, hv⟩` from `exists_gen D.P.isLB (φ' := Sum.elim (lamPts x (∏ i, y i ^ (Pi.single j (1 : ℤ) : K → ℤ) i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2)) (ε' := Sum.elim Oε (fun k : K × Fin 4 => -((Pi.single j (1 : ℤ) : K → ℤ) k.1 * Oε k.2))) (fun U _ h => by`. Use `(Fintype.prod_empty _).trans ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_sum_type]`.

Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[hK (fun k => h (lamPts x (y k.1) k.2)), hY]`. Simplify using `only [Fin.prod_univ_four, lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_prod]`.

Simplify using the standard rewrite rules. Use the proof step `abel)`. Use the proof step `(LB.oneGen D.P.L (Y := T.left)) oneGen_isGen'`. Use `⟨κ, hκ, fun p a b hx hy z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[hv _ _ z J hJ, val_one, _root_.mul_one]`.

Establish `e0 : (∑ i, (Pi.single j (1 : ℤ) : K → ℤ) i • b i) = b j`. Rewrite using `[Fintype.sum_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]`. Simplify using the standard rewrite rules. Establish `e1 : (∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ (Pi.single j (1 : ℤ) : K → ℤ) i) = val (D.tau a (b j)) (𝟙 _) z J`. Rewrite using `[Fintype.prod_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]`.

Simplify using the standard rewrite rules. Rewrite using `[e0, e1]`.
-/
theorem expand_single [DecidableEq K] (hB : D.TauBimult) (j : K) : Expand D (Pi.single j (1 : ℤ)) x y := by
  have hY : ∏ i, y i ^ (Pi.single j (1 : ℤ) : K → ℤ) i = y j := by
    rw [Fintype.prod_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]
    simp
  have hK : ∀ {U : Type} [CommGroup U] (f : K × Fin 4 → U),
      ∏ k, f k ^ (-((Pi.single j (1 : ℤ) : K → ℤ) k.1 * Oε k.2)) = ∏ m, f (j, m) ^ (-Oε m) := by
    intro U _ f
    rw [Fintype.prod_prod_type, Fintype.prod_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]
    simp
  obtain ⟨κ, hκ, hv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (lamPts x (∏ i, y i ^ (Pi.single j (1 : ℤ) : K → ℤ) i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2))
    (ε' := Sum.elim Oε (fun k : K × Fin 4 => -((Pi.single j (1 : ℤ) : K → ℤ) k.1 * Oε k.2)))
    (fun U _ h => by
      refine (Fintype.prod_empty _).trans ?_
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hK (fun k => h (lamPts x (y k.1) k.2)), hY]
      simp only [Fin.prod_univ_four, lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_prod]
      simp
      abel)
    (LB.oneGen D.P.L (Y := T.left)) oneGen_isGen'
  refine ⟨κ, hκ, fun p a b hx hy z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_one, _root_.mul_one]
  have e0 : (∑ i, (Pi.single j (1 : ℤ) : K → ℤ) i • b i) = b j := by
    rw [Fintype.sum_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]
    simp
  have e1 : (∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ (Pi.single j (1 : ℤ) : K → ℤ) i) = val (D.tau a (b j)) (𝟙 _) z J := by
    rw [Fintype.prod_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]
    simp
  rw [e0, e1]

/- English proof (translation)
Proceed by induction on `m using Int.induction_on with`. Consider the case `zero => rw [Pi.single_zero]`. Conclude with `expand_zero x y hB`. Consider the case `succ i ih`. Rewrite using `[Pi.single_add]`.

Conclude with `expand_add x y hB ih (expand_single x y hB j)`. Consider the case `pred i ih`. Use `expand_sub x y hB (expand_single x y hB j) ?_` and prove the remaining obligations. Rewrite using `[← Pi.single_add]`. Establish `e : (1 : ℤ) + (-(i : ℤ) - 1) = -(i : ℤ)` using `by ring`.

Rewrite using `[e]`. Conclude with `ih`.
-/
theorem expand_single_int [DecidableEq K] (hB : D.TauBimult) (j : K) (m : ℤ) : Expand D (Pi.single j m) x y := by
  induction m using Int.induction_on with
  | zero => rw [Pi.single_zero]; exact expand_zero x y hB
  | succ i ih =>
    rw [Pi.single_add]
    exact expand_add x y hB ih (expand_single x y hB j)
  | pred i ih =>
    refine expand_sub x y hB (expand_single x y hB j) ?_
    rw [← Pi.single_add]
    have e : (1 : ℤ) + (-(i : ℤ) - 1) = -(i : ℤ) := by ring
    rw [e]
    exact ih

/- English proof (translation)
Establish `key : ∀ s : Finset K, Expand D (∑ j ∈ s, Pi.single j (n j)) x y`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty]`. Conclude with `expand_zero x y hB`.

Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj]`. Conclude with `expand_add x y hB (expand_single_int x y hB j (n j)) ih`. Use `key Finset.univ` as an intermediate fact. Rewrite `this` using `[Finset.univ_sum_single]`. Then use the resulting hypothesis.
-/
theorem expand_all (hB : D.TauBimult) (n : K → ℤ) : Expand D n x y := by
  classical
  have key : ∀ s : Finset K, Expand D (∑ j ∈ s, Pi.single j (n j)) x y := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact expand_zero x y hB
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact expand_add x y hB (expand_single_int x y hB j (n j)) ih
  have := key Finset.univ
  rwa [Finset.univ_sum_single] at this

end GlobalTheory.Mum.PowData.ExpandPf

namespace GlobalTheory.Mum.PowData

/- English proof (translation)
Introduce `_ _ _ _ hB _ _ n _ x y` and use `ExpandPf.expand_all x y hB n`.
-/
theorem expand_of_tauBimult : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (K : Type) [Fintype K]
    (n : K → ℤ) (T : Over (Sp R)) (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A)), Expand D n x y :=
  fun _ _ _ _ hB _ _ n _ x y => ExpandPf.expand_all x y hB n

end GlobalTheory.Mum.PowData
