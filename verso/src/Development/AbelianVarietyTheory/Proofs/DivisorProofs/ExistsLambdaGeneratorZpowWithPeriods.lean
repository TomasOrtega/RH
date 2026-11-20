import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorNontrivial
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.TauTwist ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

/- English proof (translation)
Set `f : Multiplicative D.X →* (T ⟶ D.P.A)` to `{ toFun := fun x => cP D T x.toAdd map_one' := by simpa using cPoint_nsmul D T 0 0 map_mul' := fun x y => cPoint_add D T _ _ }`. Use `map_zpow f (Multiplicative.ofAdd b) n` as an intermediate fact. Simplify `this` using `[f]`.
-/
theorem degenerationPointOfLattice_zsmul (T : Over (Spec (CommRingCat.of R))) (n : ℤ) (b : D.X) : cP D T (n • b) = cP D T b ^ n := by
  let f : Multiplicative D.X →* (T ⟶ D.P.A) :=
    { toFun := fun x => cP D T x.toAdd
      map_one' := by simpa using cPoint_nsmul D T 0 0
      map_mul' := fun x y => cPoint_add D T _ _ }
  have := map_zpow f (Multiplicative.ofAdd b) n
  simpa [f] using this

/- English proof (translation)
Set `f : (T ⟶ D.P.A) →* (T' ⟶ D.P.A)` to `{ toFun := fun x => ρ ≫ x map_one' := MonObj.comp_one _ map_mul' := fun x y => MonObj.comp_mul _ _ _ }`. Conclude with `map_zpow f y n`.
-/
theorem overSpec_comp_zpow_grpObj {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (y : T ⟶ D.P.A) (n : ℤ) :
    ρ ≫ y ^ n = (ρ ≫ y) ^ n := by
  let f : (T ⟶ D.P.A) →* (T' ⟶ D.P.A) :=
    { toFun := fun x => ρ ≫ x
      map_one' := MonObj.comp_one _
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }
  exact map_zpow f y n

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [zero_nsmul, add_zero]`. Simplify using `[cubN]`. Consider the case `succ k ih`. Establish `e` using `val_tau_add (𝟙 (TK R)) hJ hB (a₀ + k • m) m v`.

Rewrite `e` using `[cPoint_add, cPoint_nsmul]`. Simplify using `only [Over.id_left] at e`. Rewrite using `[succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ]`. Simplify using `only [cubN] at ih`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Establish `e'` using `congrArg Additive.ofMul e`. Establish `ih'` using `congrArg Additive.ofMul ih`. Simplify using `only [ofMul_mul, ofMul_pow] at e' ih' ⊢`. Rewrite using `[succ_nsmul]`. Take the linear combination `(norm := abel) e' + ih'`.
-/
theorem value_tau_add_nsmul_mul_iteratedCube (hB : D.TauBimult) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) (a₀ m v : D.X) (k : ℕ) :
    val (D.tau (a₀ + k • m) v) (𝟙 (TK R).left) z J *
        cubN (th D z J) k (cP D (TK R) a₀) (cP D (TK R) m) (cP D (TK R) v) =
      val (D.tau a₀ v) (𝟙 (TK R).left) z J * val (D.tau m v) (𝟙 (TK R).left) z J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero]; simp [cubN]
  | succ k ih =>
    have e := val_tau_add (𝟙 (TK R)) hJ hB (a₀ + k • m) m v
    rw [cPoint_add, cPoint_nsmul] at e
    simp only [Over.id_left] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ]
    simp only [cubN] at ih
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    have ih' := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_pow] at e' ih' ⊢
    rw [succ_nsmul]
    linear_combination (norm := abel) e' + ih'

/- English proof (translation)
Introduce `R _ _ D hB n`. Establish `hL` using `D.P.isLB`. Take `⟨k, rfl | rfl⟩` from `Int.eq_nat_or_neg n`. Take `⟨t, ht, hv⟩` from `exists_cubN D.cub (1 : D.P.A ⊗ D.P.A ⟶ D.P.A) (snd D.P.A D.P.A) (fst D.P.A D.P.A) k`. Establish `hF : FormEq ![(1 * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A).left, (1 * snd D.P.A D.P.A ^ k).left, (1 * fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left, (snd D.P.A D.P.A * fst D.P.A D.P.A).left, (snd D.P.A D.P.A).left, (fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left …`.

Introduce `U _ h`. Establish `e1 : (1 * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A * snd D.P.A D.P.A ^ (k : ℤ)` using `by rw [_root_.one_mul, zpow_natCast, mul_comm]`. Establish `e2 : (1 * snd D.P.A D.P.A ^ k : D.P.A ⊗ D.P.A ⟶ D.P.A) = snd D.P.A D.P.A ^ (k : ℤ)`. Rewrite using `[_root_.one_mul, zpow_natCast]`. Establish `e3 : (1 * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A` using `_root_.one_mul _`.

Establish `e4 : (snd D.P.A D.P.A * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A * snd D.P.A D.P.A` using `mul_comm _ _`. Rewrite using `[e1, e2, e3, e4, Fintype.prod_sum_type]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `[Fin.prod_univ_succ, GlobalTheory.PolDeg.lamPts, Oε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]`. Normalize the expressions using the abelian group laws.

Take `⟨g, hg, hgv⟩` from `exists_gen hL hF t ht`. Use `⟨g, hg, fun a b z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[hgv _ _ z J hJ, hv (TK R) _ z J hJ, MonObj.comp_one, lift_fst, lift_snd]`. Establish `e` using `val_tau_nsmul (𝟙 (TK R)) hJ hB k b a`. Rewrite `e` using `[val_tau_symm _ hJ (k • b) a, val_tau_symm _ hJ b a]`.

Simplify using `only [Over.id_left] at e`. Rewrite using `[natCast_zsmul, zpow_natCast]`. Conclude with `e`. Take `⟨t, ht, hv⟩` from `exists_cubN D.cub (snd D.P.A D.P.A ^ (-(k : ℤ))) (snd D.P.A D.P.A) (fst D.P.A D.P.A) k`. Establish `hF : FormEq ![(snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A).left, (snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k).left, (snd D.P.A D.P.A ^ (-(k : ℤ)) * fst D.P.A D.P.A).left, (snd D.P.A D.P.A ^ (-(k : ℤ))).left, (snd D.P.A D.P.A * fst D.P.A D.P.A).le …`.

Introduce `U _ h`. Establish `e0 : (snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k : D.P.A ⊗ D.P.A ⟶ D.P.A) = 1`. Rewrite using `[zpow_neg, zpow_natCast, inv_mul_cancel]`. Establish `e4 : (snd D.P.A D.P.A * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A * snd D.P.A D.P.A` using `mul_comm _ _`. Establish `e5 : (snd D.P.A D.P.A ^ (-(k : ℤ)) * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A * snd D.P.A D.P.A ^ (-(k : ℤ))` using `mul_comm _ _`.

Rewrite using `[e0, _root_.one_mul, e4, e5, Fintype.prod_sum_type]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `[Fin.prod_univ_succ, GlobalTheory.PolDeg.lamPts, Oε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]`. Normalize the expressions using the abelian group laws. Take `⟨g, hg, hgv⟩` from `exists_gen hL hF (LB.invGen _ _ _ t) (DVR.invGen_isGen _ _ _ _ ht)`.

Use `⟨g, hg, fun a b z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[hgv _ _ z J hJ, val_inv, hv (TK R) _ z J hJ, overSpec_comp_zpow_grpObj, lift_fst, lift_snd]`. Establish `c1 : (toUnit (TK R) ≫ D.c b) ^ (-(k : ℤ)) = cP D (TK R) ((-(k : ℤ)) • b)` using `(degenerationPointOfLattice_zsmul _ _ _).symm`. Rewrite using `[c1]`. Establish `e` using `value_tau_add_nsmul_mul_iteratedCube hB hJ ((-(k : ℤ)) • b) b a k`.

Establish `z0` using `val_tau_nsmul (𝟙 (TK R)) hJ hB 0 b a`. Rewrite `z0` using `[zero_nsmul]`. Simplify using `only [Over.id_left, pow_zero, cubN, Finset.range_zero, Finset.prod_empty, _root_.mul_one] at z0`. Establish `s0 : (-(k : ℤ)) • b + k • b = 0` using `by rw [← natCast_zsmul, ← add_smul, neg_add_cancel, zero_smul]`. Rewrite `e` using `[s0, z0, _root_.one_mul]`.

Establish `s1` using `val_tau_symm (𝟙 (TK R)) hJ a ((-(k : ℤ)) • b)`. Establish `s2` using `val_tau_symm (𝟙 (TK R)) hJ a b`. Simplify using `only [Over.id_left] at s1 s2`. Rewrite using `[s1, s2]`. Rewrite using `[show cubN (th D z J) k (cP D (TK R) ((-(k : ℤ)) • b)) (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c a) = cubN (th D z J) k (cP D (TK R) ((-(k : ℤ)) • b)) (cP D (TK R) b) (cP D (TK R) a) from rfl, e, mul_inv_rev, zpow_neg, zpow_natCast, mul_comm (_ ^ k)⁻¹, ← _root_.mul_assoc, mul_ …`.
-/
theorem exists_lamGen_zpow : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (n : ℤ),
    ∃ g : LB.Gen (LB.LinComb D.P.L (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ n))
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A))) (Sum.elim Oε (fun l => -n * Oε l))), g.IsGen ∧
      ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (D.tau a (n • b)) (𝟙 _) z J *
          val g (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J = val (D.tau a b) (𝟙 _) z J ^ n := by
  intro R _ _ D hB n
  have hL := D.P.isLB
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · obtain ⟨t, ht, hv⟩ := exists_cubN D.cub (1 : D.P.A ⊗ D.P.A ⟶ D.P.A) (snd D.P.A D.P.A) (fst D.P.A D.P.A) k
    have hF : FormEq
        ![(1 * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A).left, (1 * snd D.P.A D.P.A ^ k).left,
          (1 * fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left, (snd D.P.A D.P.A * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A).left, (fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left]
        ![1, -1, -1, 1, -(k : ℤ), k, k, -(k : ℤ)]
        (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ (k : ℤ)))
          (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A)))
        (Sum.elim Oε (fun l => -(k : ℤ) * Oε l)) := by
      intro U _ h
      have e1 : (1 * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) =
          fst D.P.A D.P.A * snd D.P.A D.P.A ^ (k : ℤ) := by rw [_root_.one_mul, zpow_natCast, mul_comm]
      have e2 : (1 * snd D.P.A D.P.A ^ k : D.P.A ⊗ D.P.A ⟶ D.P.A) = snd D.P.A D.P.A ^ (k : ℤ) := by
        rw [_root_.one_mul, zpow_natCast]
      have e3 : (1 * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A := _root_.one_mul _
      have e4 : (snd D.P.A D.P.A * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A * snd D.P.A D.P.A :=
        mul_comm _ _
      rw [e1, e2, e3, e4, Fintype.prod_sum_type]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, GlobalTheory.PolDeg.lamPts, Oε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      abel
    obtain ⟨g, hg, hgv⟩ := exists_gen hL hF t ht
    refine ⟨g, hg, fun a b z J hJ => ?_⟩
    rw [hgv _ _ z J hJ, hv (TK R) _ z J hJ, MonObj.comp_one, lift_fst, lift_snd]
    have e := val_tau_nsmul (𝟙 (TK R)) hJ hB k b a
    rw [val_tau_symm _ hJ (k • b) a, val_tau_symm _ hJ b a] at e
    simp only [Over.id_left] at e
    rw [natCast_zsmul, zpow_natCast]
    exact e
  · obtain ⟨t, ht, hv⟩ := exists_cubN D.cub (snd D.P.A D.P.A ^ (-(k : ℤ))) (snd D.P.A D.P.A) (fst D.P.A D.P.A) k
    have hF : FormEq
        ![(snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k).left,
          (snd D.P.A D.P.A ^ (-(k : ℤ)) * fst D.P.A D.P.A).left, (snd D.P.A D.P.A ^ (-(k : ℤ))).left,
          (snd D.P.A D.P.A * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A).left, (fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left]
        (fun i => -(![1, -1, -1, 1, -(k : ℤ), k, k, -(k : ℤ)] : Fin 8 → ℤ) i)
        (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ (-(k : ℤ))))
          (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A)))
        (Sum.elim Oε (fun l => -(-(k : ℤ)) * Oε l)) := by
      intro U _ h
      have e0 : (snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k : D.P.A ⊗ D.P.A ⟶ D.P.A) = 1 := by
        rw [zpow_neg, zpow_natCast, inv_mul_cancel]
      have e4 : (snd D.P.A D.P.A * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A * snd D.P.A D.P.A :=
        mul_comm _ _
      have e5 : (snd D.P.A D.P.A ^ (-(k : ℤ)) * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) =
          fst D.P.A D.P.A * snd D.P.A D.P.A ^ (-(k : ℤ)) := mul_comm _ _
      rw [e0, _root_.one_mul, e4, e5, Fintype.prod_sum_type]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, GlobalTheory.PolDeg.lamPts, Oε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      abel
    obtain ⟨g, hg, hgv⟩ := exists_gen hL hF (LB.invGen _ _ _ t) (DVR.invGen_isGen _ _ _ _ ht)
    refine ⟨g, hg, fun a b z J hJ => ?_⟩
    rw [hgv _ _ z J hJ, val_inv, hv (TK R) _ z J hJ, overSpec_comp_zpow_grpObj, lift_fst, lift_snd]
    have c1 : (toUnit (TK R) ≫ D.c b) ^ (-(k : ℤ)) = cP D (TK R) ((-(k : ℤ)) • b) := (degenerationPointOfLattice_zsmul _ _ _).symm
    rw [c1]
    have e := value_tau_add_nsmul_mul_iteratedCube hB hJ ((-(k : ℤ)) • b) b a k
    have z0 := val_tau_nsmul (𝟙 (TK R)) hJ hB 0 b a
    rw [zero_nsmul] at z0
    simp only [Over.id_left, pow_zero, cubN, Finset.range_zero, Finset.prod_empty, _root_.mul_one] at z0
    have s0 : (-(k : ℤ)) • b + k • b = 0 := by rw [← natCast_zsmul, ← add_smul, neg_add_cancel, zero_smul]
    rw [s0, z0, _root_.one_mul] at e
    have s1 := val_tau_symm (𝟙 (TK R)) hJ a ((-(k : ℤ)) • b)
    have s2 := val_tau_symm (𝟙 (TK R)) hJ a b
    simp only [Over.id_left] at s1 s2
    rw [s1, s2]
    rw [show cubN (th D z J) k (cP D (TK R) ((-(k : ℤ)) • b)) (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c a) =
      cubN (th D z J) k (cP D (TK R) ((-(k : ℤ)) • b)) (cP D (TK R) b) (cP D (TK R) a) from rfl, e,
      mul_inv_rev, zpow_neg, zpow_natCast, mul_comm (_ ^ k)⁻¹, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]

end GlobalTheory.Mum
