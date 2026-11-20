import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq

open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

section Sel

variable {K : Type} [Field K]

def selE (K : Type) [Field K] (r n : ℕ) : Matrix (Fin r) (Fin n) K :=
  fun i j => if (j : ℕ) = i then 1 else 0

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, selE, Matrix.one_apply]`. Rewrite using `[Finset.sum_eq_single ⟨i, lt_of_lt_of_le i.2 hr⟩]`. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality.

Simplify using the standard rewrite rules. Establish `hne : (i : ℕ) ≠ k` using `fun h => hik (Fin.ext h)`. Simplify using `[hik, hne]`. Introduce `j _ hj`. Establish `hne : (j : ℕ) ≠ i` using `fun h => hj (Fin.ext h)`.

Simplify using `[hne]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem selE_mul_transpose {r n : ℕ} (hr : r ≤ n) :
    selE K r n * (selE K r n)ᵀ = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selE, Matrix.one_apply]
  rw [Finset.sum_eq_single ⟨i, lt_of_lt_of_le i.2 hr⟩]
  · by_cases hik : i = k
    · subst hik; simp
    · have hne : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
      simp [hik, hne]
  · intro j _ hj
    have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use extensionality with `j k`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, selE, eId, Matrix.diagonal_apply]`. Distinguish the cases in `hj : (j : ℕ) < r`. Rewrite using `[Finset.sum_eq_single ⟨j, hj⟩]`. Distinguish the cases in `hjk : j = k`.

Substitute `hjk` using the available equality. Simplify using `[hj]`. Establish `hne : (k : ℕ) ≠ j` using `fun h => hjk (Fin.ext h.symm)`. Simplify using `[hjk, hne]`. Introduce `i _ hi`.

Establish `hne : (j : ℕ) ≠ i` using `fun h => hi (Fin.ext h.symm)`. Simplify using `[hne]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[Finset.sum_eq_zero]`.

Simplify using `[hj]`. Introduce `i _`. Establish `hne : (j : ℕ) ≠ i` using `fun h => hj (h ▸ i.2)`. Simplify using `[hne]`.
-/
theorem transpose_selE_mul {r n : ℕ} (hr : r ≤ n) :
    (selE K r n)ᵀ * selE K r n = eId K n r := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selE, eId, Matrix.diagonal_apply]
  by_cases hj : (j : ℕ) < r
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · by_cases hjk : j = k
      · subst hjk; simp [hj]
      · have hne : (k : ℕ) ≠ j := fun h => hjk (Fin.ext h.symm)
        simp [hjk, hne]
    · intro i _ hi
      have hne : (j : ℕ) ≠ i := fun h => hi (Fin.ext h.symm)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · simp [hj]
    · intro i _
      have hne : (j : ℕ) ≠ i := fun h => hj (h ▸ i.2)
      simp [hne]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply, selE]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem cT_selE (σ : K →+* K) {r n : ℕ} : cT σ (selE K r n) = (selE K r n)ᵀ := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, selE]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [extB, Matrix.mul_apply, Matrix.transpose_apply, selE]`. Distinguish the cases in `hi : (i : ℕ) < r`. Distinguish the cases in `hj : (j : ℕ) < r`. Rewrite using `[dif_pos ⟨hi, hj⟩]`.

Establish `e1 : ∀ l : Fin r, (∑ k : Fin r, (if (i : ℕ) = k then (1 : K) else 0) * b k l) = b ⟨i, hi⟩ l`. Introduce `l`. Rewrite using `[Finset.sum_eq_single ⟨i, hi⟩]`. Simplify using the standard rewrite rules. Introduce `k _ hk`.

Establish `hne : (i : ℕ) ≠ k` using `fun h => hk (Fin.ext h.symm)`. Simplify using `[hne]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Simplify using `only [e1]`.

Rewrite using `[Finset.sum_eq_single ⟨j, hj⟩]`. Simplify using the standard rewrite rules. Introduce `l _ hl`. Establish `hne : (j : ℕ) ≠ l` using `fun h => hl (Fin.ext h.symm)`. Simplify using `[hne]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[dif_neg (fun h => hj h.2)]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `l _`. Establish `hne : (j : ℕ) ≠ l` using `fun h => hj (h ▸ l.2)`. Simplify using `[hne]`. Rewrite using `[dif_neg (fun h => hi h.1)]`. Use `symm`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l _`. Rewrite using `[Finset.sum_eq_zero, zero_mul]`. Introduce `k _`. Establish `hne : (i : ℕ) ≠ k` using `fun h => hi (h ▸ k.2)`.

Simplify using `[hne]`.
-/
theorem extB_eq_selE {r n : ℕ} (hr : r ≤ n) (b : Matrix (Fin r) (Fin r) K) :
    extB (n := n) b = (selE K r n)ᵀ * b * selE K r n := by
  ext i j
  simp only [extB, Matrix.mul_apply, Matrix.transpose_apply, selE]
  by_cases hi : (i : ℕ) < r
  · by_cases hj : (j : ℕ) < r
    · rw [dif_pos ⟨hi, hj⟩]
      have e1 : ∀ l : Fin r, (∑ k : Fin r, (if (i : ℕ) = k then (1 : K) else 0) * b k l) = b ⟨i, hi⟩ l := by
        intro l
        rw [Finset.sum_eq_single ⟨i, hi⟩]
        · simp
        · intro k _ hk
          have hne : (i : ℕ) ≠ k := fun h => hk (Fin.ext h.symm)
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp only [e1]
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro l _ hl
        have hne : (j : ℕ) ≠ l := fun h => hl (Fin.ext h.symm)
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg (fun h => hj h.2)]
      symm
      apply Finset.sum_eq_zero
      intro l _
      have hne : (j : ℕ) ≠ l := fun h => hj (h ▸ l.2)
      simp [hne]
  · rw [dif_neg (fun h => hi h.1)]
    symm
    apply Finset.sum_eq_zero
    intro l _
    rw [Finset.sum_eq_zero, zero_mul]
    intro k _
    have hne : (i : ℕ) ≠ k := fun h => hi (h ▸ k.2)
    simp [hne]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, selE]`. Rewrite using `[Finset.sum_eq_single ⟨i, lt_of_lt_of_le i.2 hr⟩]`. Establish `key` using `congrFun (h.2 ⟨i, lt_of_lt_of_le i.2 hr⟩ i.2) j`. Simplify using `using key`.

Introduce `k _ hk`. Establish `hne : (k : ℕ) ≠ i` using `fun h' => hk (Fin.ext h')`. Simplify using `[hne]`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`.
-/
theorem selE_mul_of_isCompl {r n : ℕ} (hr : r ≤ n) {c : Matrix (Fin r) (Fin n) K}
    {a : Matrix (Fin n) (Fin n) K} (h : IsCompl c a) : selE K r n * a = c := by
  ext i j
  simp only [Matrix.mul_apply, selE]
  rw [Finset.sum_eq_single ⟨i, lt_of_lt_of_le i.2 hr⟩]
  · have key := congrFun (h.2 ⟨i, lt_of_lt_of_le i.2 hr⟩ i.2) j
    simpa using key
  · intro k _ hk
    have hne : (k : ℕ) ≠ i := fun h' => hk (Fin.ext h')
    simp [hne]
  · intro h'; exact absurd (Finset.mem_univ _) h'

end Sel

/- English proof (translation)
Introduce `K _ σ hσ n r hr c a C D T L hc hC hLT hH`. Establish `hca : c = selE K r n * a` using `(selE_mul_of_isCompl hr hc).symm`. Establish `ha : a * a⁻¹ = 1` using `Matrix.mul_nonsing_inv a hc.1`. Establish `hcTc : cT σ c = cT σ a * (selE K r n)ᵀ` using `by rw [hca, cT_mul, cT_selE]`. Establish `hcTT : cT σ T * cT σ L = 1` using `by rw [← cT_mul, hLT, cT_one]`.

Establish `h1 : T * c * cT σ D = D * cT σ a * (selE K r n)ᵀ * cT σ T`. Rewrite using `[← hC, hH, hC, cT_mul, hcTc]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hM : D * cT σ a * (selE K r n)ᵀ = T * (c * cT σ D * cT σ L)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hcTT, Matrix.mul_one]`. Use `_ = T * c * cT σ D * cT σ L := by rw [← Matrix.mul_assoc, ← h1]`. Use `_ = T * (c * cT σ D * cT σ L) := by simp only [Matrix.mul_assoc]`. Use `⟨c * cT σ D * cT σ L, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[cT_mul, cT_mul, cT_cT σ hσ, cT_cT σ hσ, hcTc]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hM]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = c * cT σ D * cT σ L := by rw [← Matrix.mul_assoc, hLT, Matrix.one_mul]`. Establish `hSP : selE K r n * eId K n r = selE K r n`.

Rewrite using `[← transpose_selE_mul hr, ← Matrix.mul_assoc, selE_mul_transpose hr, Matrix.one_mul]`. Establish `hSB : selE K r n * extB (n` using `n) (c * cT σ D * cT σ L) = (c * cT σ D * cT σ L) * selE K r n := by`. Rewrite using `[extB_eq_selE hr, ← Matrix.mul_assoc, ← Matrix.mul_assoc, selE_mul_transpose hr, Matrix.one_mul]`. Establish `hCa : C * a⁻¹ = T * selE K r n`. Rewrite using `[hC, hca, Matrix.mul_assoc T, Matrix.mul_assoc, ha, Matrix.mul_one]`.

Rewrite using `[hCa, Matrix.mul_assoc T (selE K r n), Matrix.mul_sub (selE K r n), Matrix.mul_sub (selE K r n), Matrix.mul_one, hSP, hSB, sub_self, zero_sub, Matrix.mul_neg, ← transpose_selE_mul hr, ← Matrix.mul_assoc (D * cT σ a), hM]`. Simplify using `only [Matrix.mul_assoc, neg_add_cancel]`.
-/
theorem exists_hermitian_lowerLeft :
    ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n r : ℕ}, r ≤ n →
      ∀ (c : Matrix (Fin r) (Fin n) K) (a C D : Matrix (Fin n) (Fin n) K)
        (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K),
        IsCompl c a → C = T * c → L * T = 1 → C * cT σ D = D * cT σ C →
        ∃ b : Matrix (Fin r) (Fin r) K, cT σ b = b ∧
          C * a⁻¹ * (1 - eId K n r - extB b) + D * cT σ a * eId K n r = 0 := by
  intro K _ σ hσ n r hr c a C D T L hc hC hLT hH
  have hca : c = selE K r n * a := (selE_mul_of_isCompl hr hc).symm
  have ha : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hc.1
  have hcTc : cT σ c = cT σ a * (selE K r n)ᵀ := by rw [hca, cT_mul, cT_selE]
  have hcTT : cT σ T * cT σ L = 1 := by rw [← cT_mul, hLT, cT_one]
  have h1 : T * c * cT σ D = D * cT σ a * (selE K r n)ᵀ * cT σ T := by
    rw [← hC, hH, hC, cT_mul, hcTc]
    simp only [Matrix.mul_assoc]
  have hM : D * cT σ a * (selE K r n)ᵀ = T * (c * cT σ D * cT σ L) := by
    calc D * cT σ a * (selE K r n)ᵀ = D * cT σ a * (selE K r n)ᵀ * (cT σ T * cT σ L) := by
          rw [hcTT, Matrix.mul_one]
      _ = T * c * cT σ D * cT σ L := by rw [← Matrix.mul_assoc, ← h1]
      _ = T * (c * cT σ D * cT σ L) := by simp only [Matrix.mul_assoc]
  refine ⟨c * cT σ D * cT σ L, ?_, ?_⟩
  · rw [cT_mul, cT_mul, cT_cT σ hσ, cT_cT σ hσ, hcTc]
    calc L * (D * (cT σ a * (selE K r n)ᵀ)) = L * (T * (c * cT σ D * cT σ L)) := by
          rw [← hM]; simp only [Matrix.mul_assoc]
      _ = c * cT σ D * cT σ L := by rw [← Matrix.mul_assoc, hLT, Matrix.one_mul]
  · have hSP : selE K r n * eId K n r = selE K r n := by
      rw [← transpose_selE_mul hr, ← Matrix.mul_assoc, selE_mul_transpose hr, Matrix.one_mul]
    have hSB : selE K r n * extB (n := n) (c * cT σ D * cT σ L) = (c * cT σ D * cT σ L) * selE K r n := by
      rw [extB_eq_selE hr, ← Matrix.mul_assoc, ← Matrix.mul_assoc, selE_mul_transpose hr, Matrix.one_mul]
    have hCa : C * a⁻¹ = T * selE K r n := by
      rw [hC, hca, Matrix.mul_assoc T, Matrix.mul_assoc, ha, Matrix.mul_one]
    rw [hCa, Matrix.mul_assoc T (selE K r n), Matrix.mul_sub (selE K r n), Matrix.mul_sub (selE K r n), Matrix.mul_one, hSP, hSB,
      sub_self, zero_sub, Matrix.mul_neg, ← transpose_selE_mul hr, ← Matrix.mul_assoc (D * cT σ a), hM]
    simp only [Matrix.mul_assoc, neg_add_cancel]

end GlobalTheory.CompanionTheory.BruhatCell
