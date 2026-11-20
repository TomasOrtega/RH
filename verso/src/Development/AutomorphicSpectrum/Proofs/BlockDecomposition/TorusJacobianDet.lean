import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ZeroC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Substitute using the available equality. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dlog_ratio_det {K R : Type} [Field K] [CommRing R] [Algebra K R] (n : ℕ) (t : Fin (n + 1) → Rˣ)
    (D : Fin (n + 1) → Derivation K R R) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) :
    let g : Fin (n + 1) → R := fun k => if h : (k : ℕ) = 0 then ((t 0)⁻¹ : Rˣ) else
      (t ⟨k - 1, by omega⟩ : R) * ((t k)⁻¹ : Rˣ)
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = (((∏ k, t k)⁻¹ : Rˣ) : R) ∨
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = -(((∏ k, t k)⁻¹ : Rˣ) : R) := by
  intro g
  set u : Fin (n + 1) → R := fun j => (((t j)⁻¹ : Rˣ) : R) with hu
  have htu : ∀ j, (t j : R) * u j = 1 := fun j => by simp [hu]
  have hDu : ∀ k j, D k (u j) = if k = j then -(u j * u j) else 0 := by
    intro k j
    have h2 := (D k).leibniz_of_mul_eq_one (a := u j) (b := (t j : R)) (by rw [mul_comm]; exact htu j)
    rw [h2, hD k j]
    split_ifs <;> simp [pow_two]
  have hg0 : g 0 = u 0 := by simp [g, hu]
  have hgs : ∀ (l : Fin (n + 1)) (h : (l : ℕ) ≠ 0), g l = (t ⟨l - 1, by omega⟩ : R) * u l := by
    intro l h
    exact dif_neg h
  have hgu : ∀ l, IsUnit (g l) := by
    intro l
    by_cases h : (l : ℕ) = 0
    · simp only [g, h, dite_true]; exact Units.isUnit _
    · simp only [g, h, dite_false]; exact (Units.isUnit _).mul (Units.isUnit _)
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    Matrix.of fun k l => if k = l then -1 else if (k : ℕ) + 1 = l then 1 else 0
  have hM : (Matrix.of fun k l => D k (g l)) = Matrix.diagonal u * B * Matrix.diagonal g := by
    ext k l
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, B]
    by_cases h : (l : ℕ) = 0
    · have hl : l = 0 := Fin.ext h
      subst hl
      have hk : ¬ ((k : ℕ) + 1 = ((0 : Fin (n + 1)) : ℕ)) := by simp
      rw [hg0, hDu k 0]
      by_cases hk0 : k = 0
      · subst hk0; simp
      · simp [hk0]
    · rw [hgs l h, Derivation.leibniz, hDu k l, hD k _]
      simp only [smul_eq_mul]
      by_cases hkl : k = l
      · subst hkl
        have hne : k ≠ ⟨(k : ℕ) - 1, by omega⟩ := by
          intro e
          have := congrArg Fin.val e
          simp at this
          omega
        simp only [if_true, hne, if_false]
        ring
      · by_cases hs : (k : ℕ) + 1 = l
        · have hp : k = ⟨(l : ℕ) - 1, by omega⟩ := Fin.ext (by simp; omega)
          rw [if_neg hkl, if_pos hp, if_neg hkl, if_pos hs, ← hp]
          have := htu k
          linear_combination (-(u l)) * this
        · have hp : k ≠ ⟨(l : ℕ) - 1, by omega⟩ := by
            intro e
            have := congrArg Fin.val e
            simp at this
            omega
          rw [if_neg hkl, if_neg hp, if_neg hkl, if_neg hs]
          simp
  have hB : B.det = (-1) ^ (n + 1) := by
    rw [Matrix.det_of_upperTriangular]
    · simp [B]
    · intro i j hij
      have : (j : ℕ) < i := hij
      have h1 : i ≠ j := fun h => by simp [h] at this
      have h2 : ¬ ((i : ℕ) + 1 = j) := by omega
      simp [B, h1, h2]
  have hprod : ∏ k, u k = (((∏ k, t k)⁻¹ : Rˣ) : R) := by
    simp only [hu, ← Units.coe_prod, Finset.prod_inv_distrib]
  have hU : IsUnit (∏ k, g k) := by
    obtain ⟨v, hv⟩ := IsUnit.prod_univ_iff.2 hgu
    exact hv ▸ v.isUnit
  have hcan : Ring.inverse (∏ k, g k) * (∏ k, g k) = 1 := Ring.inverse_mul_cancel _ hU
  have key : Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det =
      (-1) ^ (n + 1) * (((∏ k, t k)⁻¹ : Rˣ) : R) := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hB, hprod]
    linear_combination ((-1) ^ (n + 1) * (((∏ k, t k)⁻¹ : Rˣ) : R)) * hcan
  rcases neg_one_pow_eq_or R (n + 1) with h | h
  · left; rw [key, h, one_mul]
  · right; rw [key, h, neg_one_mul]

end GlobalTheory.CompanionTheory.Cone
