import Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedModuleWeightLemmaOfInterfaces

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]`.
-/
theorem zpow_finset_sum_root_weights {G α : Type*} [CommGroup G] (u : G) (s : Finset α) (f : α → ℤ) :
    u ^ (∑ i ∈ s, f i) = ∏ i ∈ s, u ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

/- English proof (translation)
Introduce `R B _ _ ι _ LL n S φ D m c`. Establish `hu : (∏ v : ι × Fin n, (if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) ^ (m v)) = ∏ a, D a ^ (wtS LL S m a)`. Simplify using `only [wtS, zpow_finset_sum_root_weights]`. Rewrite using `[Fintype.prod_prod_type_right]`. Use `Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp [zpow_neg, zpow_natCast, inv_pow]`. Establish `hU : (∏ v : ι × Fin n, (((if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) : Bˣ) : B) ^ (m v)) = ((∏ a, D a ^ (wtS LL S m a) : Bˣ) : B)`. Rewrite using `[← hu, Units.coe_prod]`. Simplify using `only [Units.val_pow_eq_pow_val]`. Simplify using `only [matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, RingHom.coe_comp, Function.comp_apply]`.

Rewrite using `[Finsupp.prod_congr (g2 := fun v e => (MvPolynomial.C (((if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) : Bˣ) : B) * X v) ^ e) ?_]`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => by simp), Finset.prod_congr rfl (fun v _ => mul_pow _ _ _), Finset.prod_mul_distrib, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), ← hU]`. Simplify using `only [map_mul, map_prod, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Introduce `v _`.

Use `congr 1`. Use `split_ifs with h1 h2`. Rewrite using `[Finset.sum_eq_single v.2 (fun b _ hb => by simp [Matrix.diagonal_apply, hb, Ne.symm hb]) (fun h => absurd (Finset.mem_univ _) h)]`. Simplify using `[Matrix.diagonal_apply]`. Rewrite using `[Finset.sum_eq_single v.2 (fun b _ hb => by simp [Matrix.diagonal_apply, hb, Ne.symm hb]) (fun h => absurd (Finset.mem_univ _) h)]`.

Simplify using `[Matrix.diagonal_apply]`. Simplify using the standard rewrite rules.
-/
theorem torus_acts_through_weight : TorusActsThroughWeight := by
  intro R B _ _ ι _ LL n S φ D m c
  classical
  have hu : (∏ v : ι × Fin n, (if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) ^ (m v)) = ∏ a, D a ^ (wtS LL S m a) := by
    simp only [wtS, zpow_finset_sum_root_weights]
    rw [Fintype.prod_prod_type_right]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun l _ => ?_
    split_ifs <;> simp [zpow_neg, zpow_natCast, inv_pow]
  have hU : (∏ v : ι × Fin n, (((if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) : Bˣ) : B) ^ (m v)) = ((∏ a, D a ^ (wtS LL S m a) : Bˣ) : B) := by
    rw [← hu, Units.coe_prod]
    simp only [Units.val_pow_eq_pow_val]
  simp only [matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, RingHom.coe_comp,
    Function.comp_apply]
  rw [Finsupp.prod_congr (g2 := fun v e => (MvPolynomial.C (((if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) : Bˣ) : B) * X v) ^ e) ?_]
  · rw [Finsupp.prod_fintype _ _ (fun _ => by simp),
      Finset.prod_congr rfl (fun v _ => mul_pow _ _ _), Finset.prod_mul_distrib,
      MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), ← hU]
    simp only [map_mul, map_prod, map_pow]
    ring
  · intro v _
    congr 1
    split_ifs with h1 h2
    · rw [Finset.sum_eq_single v.2 (fun b _ hb => by simp [Matrix.diagonal_apply, hb, Ne.symm hb])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp [Matrix.diagonal_apply]
    · rw [Finset.sum_eq_single v.2 (fun b _ hb => by simp [Matrix.diagonal_apply, hb, Ne.symm hb])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp [Matrix.diagonal_apply]
    · simp

/- English proof (translation)
Use extensionality with `r`. Simplify using `only [coefficientMap, RingHom.comp_apply, mul_sp_alg, genericMatrixEvaluation, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]`.
-/
theorem specialise_coefficientMap {R : Type*} [CommRing R] {n : ℕ} {K : Type*} [CommRing K] (φ : R →+* K)
    {g0 g0inv : Matrix (Fin n) (Fin n) K} (h : g0 * g0inv = 1) :
    (mul_sp φ g0 g0inv h).comp (coefficientMap R n) = φ := by
  ext r
  simp only [coefficientMap, RingHom.comp_apply, mul_sp_alg, genericMatrixEvaluation, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_C]

/- English proof (translation)
Use extensionality with `i k`. Establish `hg` using `congrFun (congrFun (generic_matrix_evaluation_eq (j := φ) (g0 := g0)) i) k`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply] at hg`. Simplify using `only [genericMatrixRootWeights, Matrix.map_apply, mul_sp_alg]`. Conclude with `hg`.
-/
theorem specialise_genericMatrix {R : Type*} [CommRing R] {n : ℕ} {K : Type*} [CommRing K] (φ : R →+* K)
    {g0 g0inv : Matrix (Fin n) (Fin n) K} (h : g0 * g0inv = 1) :
    (genericMatrixRootWeights R n).map (mul_sp φ g0 g0inv h) = g0 := by
  ext i k
  have hg := congrFun (congrFun (generic_matrix_evaluation_eq (j := φ) (g0 := g0)) i) k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hg
  simp only [genericMatrixRootWeights, Matrix.map_apply, mul_sp_alg]
  exact hg

/- English proof (translation)
Establish `hadj : g0.adjugate = g0.det • g0inv`. Combine the equalities or inequalities in the displayed calculation. Establish `hu` using `mul_sp_inv (j := φ) (g0 := g0) (g0inv := g0inv) h`. Use extensionality with `i k`. Establish `hA` using `congrFun (congrFun (RingHom.map_adjugate (genericMatrixEvaluation φ g0) (genMat R n)) i) k`.

Rewrite `hA` using `[generic_matrix_evaluation_eq]`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply] at hA`. Simplify using `only [genericMatrixInverse, Matrix.map_apply, map_mul, mul_sp_alg, hA, hadj, Matrix.smul_apply, smul_eq_mul]`. Take the linear combination `(g0inv i k) * hu`.
-/
theorem specialise_genericMatrixInverse {R : Type*} [CommRing R] {n : ℕ} {K : Type*} [CommRing K] (φ : R →+* K)
    {g0 g0inv : Matrix (Fin n) (Fin n) K} (h : g0 * g0inv = 1) :
    (genericMatrixInverse R n).map (mul_sp φ g0 g0inv h) = g0inv := by
  have hadj : g0.adjugate = g0.det • g0inv := by
    calc g0.adjugate = g0.adjugate * (g0 * g0inv) := by rw [h, Matrix.mul_one]
      _ = (g0.adjugate * g0) * g0inv := (Matrix.mul_assoc _ _ _).symm
      _ = g0.det • g0inv := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hu := mul_sp_inv (j := φ) (g0 := g0) (g0inv := g0inv) h
  ext i k
  have hA := congrFun (congrFun (RingHom.map_adjugate (genericMatrixEvaluation φ g0) (genMat R n)) i) k
  rw [generic_matrix_evaluation_eq] at hA
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hA
  simp only [genericMatrixInverse, Matrix.map_apply, map_mul, mul_sp_alg, hA, hadj, Matrix.smul_apply, smul_eq_mul]
  linear_combination (g0inv i k) * hu

/- English proof (translation)
Introduce `R _ ι _ LL n S k1 _ φ g0 g0inv h G`. Establish `hAi : ∀ a b, mul_sp φ g0 g0inv h (genericMatrixInverse R n a b) = g0inv a b` using `fun a b => by`. Establish `e` using `congrFun (congrFun (specialise_genericMatrixInverse φ h) a) b`. Simplify `e` using `only [Matrix.map_apply]`. Establish `hAg : ∀ a b, mul_sp φ g0 g0inv h (genericMatrixRootWeights R n a b) = g0 a b` using `fun a b => by`.

Establish `e` using `congrFun (congrFun (specialise_genericMatrix φ h) a) b`. Simplify `e` using `only [Matrix.map_apply]`. Establish `hAc : ∀ r, mul_sp φ g0 g0inv h (coefficientMap R n r) = φ r` using `fun r => RingHom.congr_fun (specialise_coefficientMap φ h) r`. Establish `e : (MvPolynomial.map (mul_sp φ g0 g0inv h)).comp (matrixSubst LL S (coefficientMap R n) (genericMatrixInverse R n) (genericMatrixRootWeights R n)) = matrixSubst LL S φ g0inv g0`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `r`. Simplify using `only [RingHom.comp_apply, matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.map_C, hAc]`. Introduce `w`. Simplify using `only [RingHom.comp_apply, matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]`. Apply the tactic sequence `split_ifs <;> simp [map_sum, hAi, hAg]`.

Establish `key : matrixSubst LL S φ g0inv g0 G = MvPolynomial.map (mul_sp φ g0 g0inv h) (genericTranslate LL S G)`. Rewrite using `[← e]`. Both sides reduce to the same expression. Rewrite using `[key]`. Conclude with `MvPolynomial.support_map_subset _ _`.
-/
theorem generic_monomials_specialise : GenericMonomialsSpecialise := by
  intro R _ ι _ LL n S k1 _ φ g0 g0inv h G
  have hAi : ∀ a b, mul_sp φ g0 g0inv h (genericMatrixInverse R n a b) = g0inv a b := fun a b => by
    have e := congrFun (congrFun (specialise_genericMatrixInverse φ h) a) b
    simpa only [Matrix.map_apply] using e
  have hAg : ∀ a b, mul_sp φ g0 g0inv h (genericMatrixRootWeights R n a b) = g0 a b := fun a b => by
    have e := congrFun (congrFun (specialise_genericMatrix φ h) a) b
    simpa only [Matrix.map_apply] using e
  have hAc : ∀ r, mul_sp φ g0 g0inv h (coefficientMap R n r) = φ r := fun r =>
    RingHom.congr_fun (specialise_coefficientMap φ h) r
  have e : (MvPolynomial.map (mul_sp φ g0 g0inv h)).comp
      (matrixSubst LL S (coefficientMap R n) (genericMatrixInverse R n) (genericMatrixRootWeights R n)) = matrixSubst LL S φ g0inv g0 := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
        MvPolynomial.map_C, hAc]
    · intro w
      simp only [RingHom.comp_apply, matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      split_ifs <;> simp [map_sum, hAi, hAg]
  have key : matrixSubst LL S φ g0inv g0 G = MvPolynomial.map (mul_sp φ g0 g0inv h) (genericTranslate LL S G) := by
    rw [← e]
    rfl
  rw [key]
  exact MvPolynomial.support_map_subset _ _

end Formalism.MainNotions.G.GLWeightTheory
