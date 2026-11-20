import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

noncomputable section

open Matrix

namespace GlobalTheory.FlagEmb.CellLU

variable {K : Type} [Field K] {n : ℕ}

/- English proof (translation)
Establish `hw : ∀ i : Fin n, ∃ v : Fin i → K, vecMul v (A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le)) = fun j : Fin i => A i (Fin.castLE i.isLt.le j)` using `fun i => ⟨vecMul (fun j : Fin i => A i (Fin.castLE i.isLt.le j)) (A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le))⁻¹, by`. Rewrite using `[vecMul_vecMul, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hA _ _)), vecMul_one]⟩`. Use `choose v hv using hw`. Use `⟨Matrix.of fun i k => if h : (k : ℕ) < i then -v i ⟨k, h⟩ else if k = i then 1 else 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i k h`.

Simplify using `only [Matrix.of_apply]`. Rewrite using `[dif_neg (by have := Fin.lt_def.mp h; omega), if_neg (ne_of_gt h)]`. Introduce `i`. Simplify using the standard rewrite rules. Introduce `i j h`.

Rewrite using `[Matrix.mul_apply]`. Establish `hsplit : ∀ k : Fin n, (Matrix.of fun i k : Fin n => if h : (k : ℕ) < i then -v i ⟨k, h⟩ else if k = i then (1 : K) else 0) i k * A k j = (if h : (k : ℕ) < i then -v i ⟨k, h⟩ * A k j else 0) + (if k = i then A i j else 0)`. Introduce `k`. Simplify using `only [Matrix.of_apply]`. Break down `lt_trichotomy k i with h | h | h` into its components or cases.

Establish `hk : (k : ℕ) < i` using `h`. Rewrite using `[dif_pos hk, dif_pos hk, if_neg (ne_of_lt h), add_zero]`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `hk : ¬ (k : ℕ) < i` using `by have := Fin.lt_def.mp h; omega`.

Rewrite using `[dif_neg hk, dif_neg hk, if_neg (ne_of_gt h), if_neg (ne_of_gt h), zero_mul, add_zero]`. Rewrite using `[Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]`. Establish `hs : ∑ k : Fin i, -v i k * A (Fin.castLE i.isLt.le k) j = ∑ k : Fin n, (if h : (k : ℕ) < i then -v i ⟨k, h⟩ * A k j else 0)`. Use `Fintype.sum_of_injective (Fin.castLE i.isLt.le) (Fin.castLE_injective _) _ _ (fun k hk => ?_) (fun k => by simp)` and prove the remaining obligations. Rewrite using `[dif_neg]`.

Introduce `hlt`. Conclude with `hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩`. Rewrite using `[← hs]`. Establish `hj` using `congrFun (hv i) ⟨j, h⟩`. Simplify using `only [vecMul, dotProduct, Matrix.submatrix_apply] at hj`.

Establish `hcj : Fin.castLE i.isLt.le (⟨j, h⟩ : Fin i) = j` using `Fin.ext rfl`. Rewrite `hj` using `[hcj]`. Rewrite using `[← hj]`. Simplify using `only [neg_mul, Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_lower_mul_upper (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ (k : ℕ) (h : k ≤ n), (A.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0) :
    ∃ L : Matrix (Fin n) (Fin n) K, (∀ i k, i < k → L i k = 0) ∧ (∀ i, L i i = 1) ∧
      ∀ i j, j < i → (L * A) i j = 0 := by
  have hw : ∀ i : Fin n, ∃ v : Fin i → K, vecMul v (A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le)) =
      fun j : Fin i => A i (Fin.castLE i.isLt.le j) := fun i =>
    ⟨vecMul (fun j : Fin i => A i (Fin.castLE i.isLt.le j))
      (A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le))⁻¹, by
      rw [vecMul_vecMul, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hA _ _)), vecMul_one]⟩
  choose v hv using hw
  refine ⟨Matrix.of fun i k => if h : (k : ℕ) < i then -v i ⟨k, h⟩ else if k = i then 1 else 0, ?_, ?_, ?_⟩
  · intro i k h
    simp only [Matrix.of_apply]
    rw [dif_neg (by have := Fin.lt_def.mp h; omega), if_neg (ne_of_gt h)]
  · intro i
    simp
  · intro i j h
    rw [Matrix.mul_apply]
    have hsplit : ∀ k : Fin n,
        (Matrix.of fun i k : Fin n => if h : (k : ℕ) < i then -v i ⟨k, h⟩ else if k = i then (1 : K) else 0) i k * A k j =
        (if h : (k : ℕ) < i then -v i ⟨k, h⟩ * A k j else 0) + (if k = i then A i j else 0) := by
      intro k
      simp only [Matrix.of_apply]
      rcases lt_trichotomy k i with h | h | h
      · have hk : (k : ℕ) < i := h
        rw [dif_pos hk, dif_pos hk, if_neg (ne_of_lt h), add_zero]
      · subst h; simp
      · have hk : ¬ (k : ℕ) < i := by have := Fin.lt_def.mp h; omega
        rw [dif_neg hk, dif_neg hk, if_neg (ne_of_gt h), if_neg (ne_of_gt h), zero_mul, add_zero]
    rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
    have hs : ∑ k : Fin i, -v i k * A (Fin.castLE i.isLt.le k) j =
        ∑ k : Fin n, (if h : (k : ℕ) < i then -v i ⟨k, h⟩ * A k j else 0) := by
      refine Fintype.sum_of_injective (Fin.castLE i.isLt.le) (Fin.castLE_injective _) _ _ (fun k hk => ?_)
        (fun k => by simp)
      rw [dif_neg]
      intro hlt
      exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
    rw [← hs]
    have hj := congrFun (hv i) ⟨j, h⟩
    simp only [vecMul, dotProduct, Matrix.submatrix_apply] at hj
    have hcj : Fin.castLE i.isLt.le (⟨j, h⟩ : Fin i) = j := Fin.ext rfl
    rw [hcj] at hj
    rw [← hj]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring

/- English proof (translation)
Take `⟨L, hup, hd, hz⟩` from `exists_lower_mul_upper A hA`. Establish `hLt : L.BlockTriangular OrderDual.toDual` using `fun i k h => hup i k h`. Establish `hL : L.det = 1`. Rewrite using `[Matrix.det_of_lowerTriangular L hLt]`. Simplify using `[hd]`.

Establish `hu : IsUnit L.det` using `by rw [hL]; exact isUnit_one`. Use `letI := L.invertibleOfIsUnitDet hu`. Establish `hN : L⁻¹.BlockTriangular OrderDual.toDual` using `blockTriangular_inv_of_blockTriangular hLt`. Use `⟨L⁻¹, L * A, fun i k h => hN h, fun i => ?_, hz, fun i => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (L * L⁻¹) i i = 1` using `by rw [mul_nonsing_inv _ hu]; simp`.

Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_single i, hd, one_mul]`. Conclude with `h1`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[hN (show OrderDual.toDual i < OrderDual.toDual k from h), mul_zero]`.

Rewrite using `[hup i k h, zero_mul]`. Simplify using the standard rewrite rules. Establish `h1 : (L * A).det ≠ 0`. Rewrite using `[det_mul, hL, one_mul]`. Simplify using `using hA n le_rfl`.

Rewrite `h1` using `[Matrix.det_of_upperTriangular (fun i j h => hz i j h)]`. Conclude with `Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ _)`. Rewrite using `[← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]`.
-/
theorem exists_lu (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ (k : ℕ) (h : k ≤ n), (A.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0) :
    ∃ N b : Matrix (Fin n) (Fin n) K, (∀ i k, i < k → N i k = 0) ∧ (∀ i, N i i = 1) ∧
      (∀ i j, j < i → b i j = 0) ∧ (∀ i, b i i ≠ 0) ∧ A = N * b := by
  obtain ⟨L, hup, hd, hz⟩ := exists_lower_mul_upper A hA
  have hLt : L.BlockTriangular OrderDual.toDual := fun i k h => hup i k h
  have hL : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L hLt]
    simp [hd]
  have hu : IsUnit L.det := by rw [hL]; exact isUnit_one
  letI := L.invertibleOfIsUnitDet hu
  have hN : L⁻¹.BlockTriangular OrderDual.toDual := blockTriangular_inv_of_blockTriangular hLt
  refine ⟨L⁻¹, L * A, fun i k h => hN h, fun i => ?_, hz, fun i => ?_, ?_⟩
  · have h1 : (L * L⁻¹) i i = 1 := by rw [mul_nonsing_inv _ hu]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hd, one_mul] at h1
    · exact h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hN (show OrderDual.toDual i < OrderDual.toDual k from h), mul_zero]
      · rw [hup i k h, zero_mul]
    · simp
  · have h1 : (L * A).det ≠ 0 := by
      rw [det_mul, hL, one_mul]
      simpa using hA n le_rfl
    rw [Matrix.det_of_upperTriangular (fun i j h => hz i j h)] at h1
    exact Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ _)
  · rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]

/- English proof (translation)
Establish `h` using `Equiv.sum_comp (plE M k) (fun q : Fin k → Fin (M + 1) => (∏ l, D (ρ l) (q l)) * (Matrix.of fun l l' => u (e l) (q l')).det)`. Use `Eq.trans h ?_` and prove the remaining obligations. Simplify using `only [det_apply', Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_lform_plk {S : Type} [CommRing S] {M k : ℕ} {ι ι' : Type} (D : ι' → Fin (M + 1) → S)
    (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι) :
    ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det := by
  have h := Equiv.sum_comp (plE M k)
    (fun q : Fin k → Fin (M + 1) => (∏ l, D (ρ l) (q l)) * (Matrix.of fun l l' => u (e l) (q l')).det)
  refine Eq.trans h ?_
  simp only [det_apply', Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/- English proof (translation)
Establish `hA : ∀ τ, ∃ A : Matrix (Fin (m τ)) (Fin (m τ)) K, ∀ j, u ⟨τ, j⟩ = ∑ i, A i j • c ⟨τ, w τ i⟩` using `fun τ => by`. Use `fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hu ⟨τ, j⟩)` as an intermediate fact. Use `choose a ha using this`. Use `⟨Matrix.of fun i j => a j (w τ i), fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[← ha j]`.

Conclude with `(Equiv.sum_comp (w τ) (fun i => a j i • c ⟨τ, i⟩)).symm`. Use `choose A hA using hA`. Establish `hent : ∀ τ i j, ∑ r, D (wLet w ⟨τ, i⟩) r * u ⟨τ, j⟩ r = A τ i j` using `fun τ i j => by`. Rewrite using `[hA]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Establish `: ∀ i', ∑ r, D (wLet w ⟨τ, i⟩) r * (A τ i' j * c ⟨τ, w τ i'⟩ r) = if i' = i then A τ i' j else 0`. Introduce `i'`. Establish `h1` using `hD (wLet w ⟨τ, i⟩) ⟨τ, w τ i'⟩`. Rewrite using `[show (∑ r, D (wLet w ⟨τ, i⟩) r * (A τ i' j * c ⟨τ, w τ i'⟩ r)) = A τ i' j * ∑ r, D (wLet w ⟨τ, i⟩) r * c ⟨τ, w τ i'⟩ r by`.

Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring, h1]`. Distinguish the cases in `hi : i' = i`. Substitute `hi` using the available equality. Simplify using `[wLet]`. Rewrite using `[if_neg hi, if_neg, mul_zero]`.

Introduce `he`. Simplify using `only [wLet, Sigma.mk.injEq, heq_eq_eq, true_and] at he`. Conclude with `hi ((w τ).injective he).symm`. Simplify using `[this]`. Establish `hmin : ∀ τ (k : ℕ) (hk : k ≤ m τ), ((A τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0`.

Introduce `τ k hk`. Establish `h1` using `h τ k hk`. Rewrite `h1` using `[sum_lform_plk, ← det_transpose]`. Use `h1 using 2` and compare the differences between its conclusion and the goal. Use extensionality with `l l'`.

Conclude with `(hent τ _ _).symm`. Use `choose N b hN hN1 hb hb1 hNb using fun τ => exists_lu (A τ) (hmin τ)`. Use `⟨fun y => N y.1 y.2.1.1 y.2.1.2, fun z => b z.1 z.2 z.2, fun z => hb1 _ _, ?_⟩` and prove the remaining obligations. Establish `hcell : ∀ τ i j, cell (fun y : CellVar m => N y.1 y.2.1.1 y.2.1.2) τ i j = N τ i j`. Introduce `τ i j`.

Unfold `cell`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Rewrite using `[dif_neg (not_lt.2 h.le), if_neg h.ne, hN τ i j h]`. Substitute `h` using the available equality. Simplify using `[hN1]`.

Rewrite using `[dif_pos h]`. Introduce and unpack `⟨τ, j⟩`. Establish `hexp : u ⟨τ, j⟩ = ∑ k, b τ k j • cellVec c w (fun y : CellVar m => N y.1 y.2.1.1 y.2.1.2) ⟨τ, k⟩`. Rewrite using `[hA, hNb]`. Simplify using `only [cellVec, hcell, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]`. Rewrite using `[hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_sub_cancel_left]`. Use `Submodule.sum_mem _ fun k hk => ?_` and prove the remaining obligations. Break down `lt_or_gt_of_ne (Finset.ne_of_mem_erase hk) with h | h` into its components or cases.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, h, rfl⟩)`. Rewrite using `[hb τ k j h, zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem exists_cell (T : Type) (m : T → ℕ) (K : Type) [Field K] (M : ℕ) (D c u : Let m → Fin (M + 1) → K) (w : Pm m)
    (hD : LeftInv D c) (hu : InBlock c u)
    (h : ∀ τ j hj, ∑ q, lform D (wLet w ∘ std τ j hj) q * plk u (std τ j hj) q ≠ 0) :
    ∃ (x : CellVar m → K) (d : Let m → K), (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  have hA : ∀ τ, ∃ A : Matrix (Fin (m τ)) (Fin (m τ)) K, ∀ j, u ⟨τ, j⟩ = ∑ i, A i j • c ⟨τ, w τ i⟩ := fun τ => by
    have := fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hu ⟨τ, j⟩)
    choose a ha using this
    refine ⟨Matrix.of fun i j => a j (w τ i), fun j => ?_⟩
    rw [← ha j]
    exact (Equiv.sum_comp (w τ) (fun i => a j i • c ⟨τ, i⟩)).symm
  choose A hA using hA
  have hent : ∀ τ i j, ∑ r, D (wLet w ⟨τ, i⟩) r * u ⟨τ, j⟩ r = A τ i j := fun τ i j => by
    rw [hA]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ i', ∑ r, D (wLet w ⟨τ, i⟩) r * (A τ i' j * c ⟨τ, w τ i'⟩ r) = if i' = i then A τ i' j else 0 := by
      intro i'
      have h1 := hD (wLet w ⟨τ, i⟩) ⟨τ, w τ i'⟩
      rw [show (∑ r, D (wLet w ⟨τ, i⟩) r * (A τ i' j * c ⟨τ, w τ i'⟩ r)) =
        A τ i' j * ∑ r, D (wLet w ⟨τ, i⟩) r * c ⟨τ, w τ i'⟩ r by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring, h1]
      by_cases hi : i' = i
      · subst hi; simp [wLet]
      · rw [if_neg hi, if_neg, mul_zero]
        intro he
        simp only [wLet, Sigma.mk.injEq, heq_eq_eq, true_and] at he
        exact hi ((w τ).injective he).symm
    simp [this]
  have hmin : ∀ τ (k : ℕ) (hk : k ≤ m τ), ((A τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
    intro τ k hk
    have h1 := h τ k hk
    rw [sum_lform_plk, ← det_transpose] at h1
    convert h1 using 2
    ext l l'
    exact (hent τ _ _).symm
  choose N b hN hN1 hb hb1 hNb using fun τ => exists_lu (A τ) (hmin τ)
  refine ⟨fun y => N y.1 y.2.1.1 y.2.1.2, fun z => b z.1 z.2 z.2, fun z => hb1 _ _, ?_⟩
  have hcell : ∀ τ i j, cell (fun y : CellVar m => N y.1 y.2.1.1 y.2.1.2) τ i j = N τ i j := by
    intro τ i j
    unfold cell
    rcases lt_trichotomy i j with h | h | h
    · rw [dif_neg (not_lt.2 h.le), if_neg h.ne, hN τ i j h]
    · subst h; simp [hN1]
    · rw [dif_pos h]
  rintro ⟨τ, j⟩
  have hexp : u ⟨τ, j⟩ = ∑ k, b τ k j • cellVec c w (fun y : CellVar m => N y.1 y.2.1.1 y.2.1.2) ⟨τ, k⟩ := by
    rw [hA, hNb]
    simp only [cellVec, hcell, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_sub_cancel_left]
  refine Submodule.sum_mem _ fun k hk => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hk) with h | h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, h, rfl⟩)
  · rw [hb τ k j h, zero_smul]
    exact Submodule.zero_mem _

end GlobalTheory.FlagEmb.CellLU
