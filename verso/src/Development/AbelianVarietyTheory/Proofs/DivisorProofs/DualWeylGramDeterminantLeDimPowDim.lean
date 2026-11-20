import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMinorLeOneAndHadamardColumnsStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.OnMatGram

/- English proof (translation)
Take `⟨-, -, K, sz, hsz, I, -, -, hb⟩` from `(Formalism.GradedWeylDivisibility.sSBasis ℤ n n la).choose_spec.2 j`. Establish `hv : intVec la j = Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I` using `hb`. Rewrite using `[hv, Formalism.GradedWeylDivisibility.ldlat_map_bidet]`. Unfold `Formalism.GradedWeylDivisibility.bideterminant`. Rewrite using `[map_prod, norm_prod]`.

Use `Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => ?_` and prove the remaining obligations. Unfold `Formalism.GradedWeylDivisibility.initMinor`. Rewrite using `[Formalism.GradedWeylDivisibility.algHom_det_of]`. Establish `h : (Matrix.of fun p q : Fin (sz k) => evalAt g.1 (X (I k p, Fin.castLE (hsz k) q) : Pol n ℂ)) = g.1.submatrix (I k) (Fin.castLE (hsz k))`. Use extensionality with `p q`.

Simplify using the standard rewrite rules. Rewrite using `[h]`. Conclude with `GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns.1 n (sz k) g (I k) (Fin.castLE (hsz k))`.
-/
theorem norm_evalAt_intVec_le {n : ℕ} (la : Fin n → ℕ) (j : Idx la) (g : UN n) :
    ‖evalAt g.1 (map (Int.castRingHom ℂ) (intVec la j))‖ ≤ 1 := by
  obtain ⟨-, -, K, sz, hsz, I, -, -, hb⟩ := (Formalism.GradedWeylDivisibility.sSBasis ℤ n n la).choose_spec.2 j
  have hv : intVec la j = Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I := hb
  rw [hv, Formalism.GradedWeylDivisibility.ldlat_map_bidet]
  unfold Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod, norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [Formalism.GradedWeylDivisibility.algHom_det_of]
  have h : (Matrix.of fun p q : Fin (sz k) => evalAt g.1 (X (I k p, Fin.castLE (hsz k) q) : Pol n ℂ)) =
      g.1.submatrix (I k) (Fin.castLE (hsz k)) := by
    ext p q
    simp
  rw [h]
  exact GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns.1 n (sz k) g (I k) (Fin.castLE (hsz k))

/- English proof (translation)
Use `normSq_le_dim fun g => ?_` and prove the remaining obligations. Rewrite using `[coe_basis]`. Conclude with `norm_evalAt_intVec_le la j g`.
-/
theorem normSq_basis_le {n : ℕ} (la : Fin n → ℕ) (j : Idx la) :
    normSq la (basis la ℂ j).1 ≤ dim la := by
  refine normSq_le_dim fun g => ?_
  rw [coe_basis]
  exact norm_evalAt_intVec_le la j g

/- English proof (translation)
Rewrite using `[← norm_toSpace_sq, ← (onBasis la).repr.norm_map, EuclideanSpace.norm_sq_eq]`. Both sides reduce to the same expression.
-/
theorem sum_norm_sq_onMat {n : ℕ} (la : Fin n → ℕ) (j : Idx la) :
    ∑ i, ‖onMat la i j‖ ^ 2 = normSq la (basis la ℂ j).1 := by
  rw [← norm_toSpace_sq, ← (onBasis la).repr.norm_map, EuclideanSpace.norm_sq_eq]
  rfl

/- English proof (translation)
Set `c : Module.Basis (Idx la) ℂ (Space la)` to `(basis la ℂ).map (toSpace la)`. Establish `hc : onMat la = (onBasis la).toBasis.toMatrix c`. Use extensionality with `i j`. Simplify using `[onMat, c, Module.Basis.toMatrix_apply]`. Rewrite using `[hc]`.

Conclude with `(Matrix.isUnit_det_of_left_inverse (Module.Basis.toMatrix_mul_toMatrix_flip c _)).ne_zero`.
-/
theorem det_onMat_ne_zero {n : ℕ} (la : Fin n → ℕ) : (onMat la).det ≠ 0 := by
  let c : Module.Basis (Idx la) ℂ (Space la) := (basis la ℂ).map (toSpace la)
  have hc : onMat la = (onBasis la).toBasis.toMatrix c := by
    ext i j
    simp [onMat, c, Module.Basis.toMatrix_apply]
  rw [hc]
  exact (Matrix.isUnit_det_of_left_inverse (Module.Basis.toMatrix_mul_toMatrix_flip c _)).ne_zero

end GlobalTheory.OnMatGram

namespace GlobalTheory.OnMatGram

/- English proof (translation)
Introduce `n la _`. Use `⟨det_onMat_ne_zero la, ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns.2 (Idx la) (onMat la)).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_det_onMat_sq_le : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → (onMat la).det ≠ 0 ∧ ‖(onMat la).det‖ ^ 2 ≤ (dim la : ℝ) ^ dim la := by
  intro n la _
  refine ⟨det_onMat_ne_zero la, ?_⟩
  refine (GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns.2 (Idx la) (onMat la)).trans ?_
  calc ∏ j, ∑ i, ‖onMat la i j‖ ^ 2 ≤ ∏ _j : Idx la, (dim la : ℝ) :=
        Finset.prod_le_prod (fun j _ => Finset.sum_nonneg fun _ _ => by positivity)
          fun j _ => (sum_norm_sq_onMat la j).trans_le (normSq_basis_le la j)
    _ = (dim la : ℝ) ^ dim la := by rw [Finset.prod_const, Finset.card_univ, ← dim_eq_card]

end GlobalTheory.OnMatGram
