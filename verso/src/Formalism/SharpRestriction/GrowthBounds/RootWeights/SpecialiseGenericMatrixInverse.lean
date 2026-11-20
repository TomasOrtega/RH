import Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedModuleWeightLemmaOfInterfaces

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem zpow_finset_sum_root_weights {G α : Type*} [CommGroup G] (u : G) (s : Finset α) (f : α → ℤ) :
    u ^ (∑ i ∈ s, f i) = ∏ i ∈ s, u ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem specialise_coefficientMap {R : Type*} [CommRing R] {n : ℕ} {K : Type*} [CommRing K] (φ : R →+* K)
    {g0 g0inv : Matrix (Fin n) (Fin n) K} (h : g0 * g0inv = 1) :
    (mul_sp φ g0 g0inv h).comp (coefficientMap R n) = φ := by
  ext r
  simp only [coefficientMap, RingHom.comp_apply, mul_sp_alg, genericMatrixEvaluation, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_C]

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
