import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ZeroC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

/- English proof (translation)
Introduce `g`. Use `set u : Fin (n + 1) → R := fun j => (((t j)⁻¹ : Rˣ) : R) with hu`. Establish `htu : ∀ j, (t j : R) * u j = 1` using `fun j => by simp [hu]`. Establish `hDu : ∀ k j, D k (u j) = if k = j then -(u j * u j) else 0`. Introduce `k j`.

Establish `h2` using `(D k).leibniz_of_mul_eq_one (a := u j) (b := (t j : R)) (by rw [mul_comm]; exact htu j)`. Rewrite using `[h2, hD k j]`. Apply the tactic sequence `split_ifs <;> simp [pow_two]`. Establish `hg0 : g 0 = u 0` using `by simp [g, hu]`. Establish `hgs : ∀ (l : Fin (n + 1)) (h : (l : ℕ) ≠ 0), g l = (t ⟨l - 1, by omega⟩ : R) * u l`.

Introduce `l h`. Conclude with `dif_neg h`. Establish `hgu : ∀ l, IsUnit (g l)`. Introduce `l`. Distinguish the cases in `h : (l : ℕ) = 0`.

Simplify using `only [g, h, dite_true]`. Conclude with `Units.isUnit _`. Simplify using `only [g, h, dite_false]`. Conclude with `(Units.isUnit _).mul (Units.isUnit _)`. Set `B : Matrix (Fin (n + 1)) (Fin (n + 1)) R` to `Matrix.of fun k l => if k = l then -1 else if (k : ℕ) + 1 = l then 1 else 0`.

Establish `hM : (Matrix.of fun k l => D k (g l)) = Matrix.diagonal u * B * Matrix.diagonal g`. Use extensionality with `k l`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Simplify using `only [Matrix.of_apply, B]`. Distinguish the cases in `h : (l : ℕ) = 0`.

Establish `hl : l = 0` using `Fin.ext h`. Substitute `hl` using the available equality. Establish `hk : ¬ ((k : ℕ) + 1 = ((0 : Fin (n + 1)) : ℕ))` using `by simp`. Rewrite using `[hg0, hDu k 0]`. Distinguish the cases in `hk0 : k = 0`.

Substitute `hk0` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hk0]`. Rewrite using `[hgs l h, Derivation.leibniz, hDu k l, hD k _]`. Simplify using `only [smul_eq_mul]`.

Distinguish the cases in `hkl : k = l`. Substitute `hkl` using the available equality. Establish `hne : k ≠ ⟨(k : ℕ) - 1, by omega⟩`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Simplify using `only [if_true, hne, if_false]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hs : (k : ℕ) + 1 = l`.

Establish `hp : k = ⟨(l : ℕ) - 1, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[if_neg hkl, if_pos hp, if_neg hkl, if_pos hs, ← hp]`. Use `htu k` as an intermediate fact. Take the linear combination `(-(u l)) * this`. Establish `hp : k ≠ ⟨(l : ℕ) - 1, by omega⟩`.

Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hkl, if_neg hp, if_neg hkl, if_neg hs]`.

Simplify using the standard rewrite rules. Establish `hB : B.det = (-1) ^ (n + 1)`. Rewrite using `[Matrix.det_of_upperTriangular]`. Simplify using `[B]`. Introduce `i j hij`.

Establish `: (j : ℕ) < i` using `hij`. Establish `h1 : i ≠ j` using `fun h => by simp [h] at this`. Establish `h2 : ¬ ((i : ℕ) + 1 = j)` using `by omega`. Simplify using `[B, h1, h2]`. Establish `hprod : ∏ k, u k = (((∏ k, t k)⁻¹ : Rˣ) : R)`.

Simplify using `only [hu, ← Units.coe_prod, Finset.prod_inv_distrib]`. Establish `hU : IsUnit (∏ k, g k)`. Take `⟨v, hv⟩` from `IsUnit.prod_univ_iff.2 hgu`. Conclude with `hv ▸ v.isUnit`. Establish `hcan : Ring.inverse (∏ k, g k) * (∏ k, g k) = 1` using `Ring.inverse_mul_cancel _ hU`.

Establish `key : Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = (-1) ^ (n + 1) * (((∏ k, t k)⁻¹ : Rˣ) : R)`. Rewrite using `[hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hB, hprod]`. Take the linear combination `((-1) ^ (n + 1) * (((∏ k, t k)⁻¹ : Rˣ) : R)) * hcan`. Break down `neg_one_pow_eq_or R (n + 1) with h | h` into its components or cases. Use `left`.

Rewrite using `[key, h, one_mul]`. Use `right`. Rewrite using `[key, h, neg_one_mul]`.
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
