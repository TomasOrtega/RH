import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsGLSplitSeqStandardOfStableRangeLe

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

/- English proof (translation)
Establish `h1 : (1 + Matrix.vecMulVec z u) * (1 - Matrix.vecMulVec z u) = 1`. Simplify using `[add_mul, mul_sub, Matrix.vecMulVec_mul_vecMulVec, h]`. Establish `h2 : (1 - Matrix.vecMulVec z u) * (1 + Matrix.vecMulVec z u) = 1`. Simplify using `[sub_mul, mul_add, Matrix.vecMulVec_mul_vecMulVec, h]`. Use `⟨⟨1 + Matrix.vecMulVec z u, 1 - Matrix.vecMulVec z u, h1, h2⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x show Matrix.mulVec (1 + Matrix.vecMulVec z u) x = _`. Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]`. Introduce `x show Matrix.vecMul x (1 + Matrix.vecMulVec z u) = _`. Rewrite using `[Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_vecMulVec]`. Introduce `x show Matrix.mulVec (1 - Matrix.vecMulVec z u) x = _`.

Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]`. Introduce `x show Matrix.vecMul x (1 - Matrix.vecMulVec z u) = _`. Rewrite using `[Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_vecMulVec]`.
-/
private theorem transvection_vecMul_and_inv_mulVec_vecMul_formulas {R : Type} [CommRing R] {n : ℕ} (z u : Fin n → R)
    (h : u ⬝ᵥ z = 0) : ∃ T : GL (Fin n) R,
      (∀ x, Matrix.mulVec (T : Matrix (Fin n) (Fin n) R) x = x + (u ⬝ᵥ x) • z) ∧
      (∀ x, Matrix.vecMul x (T : Matrix (Fin n) (Fin n) R) = x + (x ⬝ᵥ z) • u) ∧
      (∀ x, Matrix.mulVec ((T⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) x = x - (u ⬝ᵥ x) • z) ∧
      (∀ x, Matrix.vecMul x ((T⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = x - (x ⬝ᵥ z) • u) := by
  have h1 : (1 + Matrix.vecMulVec z u) * (1 - Matrix.vecMulVec z u) = 1 := by
    simp [add_mul, mul_sub, Matrix.vecMulVec_mul_vecMulVec, h]
  have h2 : (1 - Matrix.vecMulVec z u) * (1 + Matrix.vecMulVec z u) = 1 := by
    simp [sub_mul, mul_add, Matrix.vecMulVec_mul_vecMulVec, h]
  refine ⟨⟨1 + Matrix.vecMulVec z u, 1 - Matrix.vecMulVec z u, h1, h2⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    show Matrix.mulVec (1 + Matrix.vecMulVec z u) x = _
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  · intro x
    show Matrix.vecMul x (1 + Matrix.vecMulVec z u) = _
    rw [Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_vecMulVec]
  · intro x
    show Matrix.mulVec (1 - Matrix.vecMulVec z u) x = _
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  · intro x
    show Matrix.vecMul x (1 - Matrix.vecMulVec z u) = _
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_vecMulVec]

/- English proof (translation)
Take `⟨T, h1, h2, -, -⟩` from `transvection_vecMul_and_inv_mulVec_vecMul_formulas z u h`. Use `⟨T, h1, h2, fun j hj => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[h1, dotProduct_single, hu j hj]`. Simplify using the standard rewrite rules. Rewrite using `[h2, single_dotProduct, hz j hj]`.

Simplify using the standard rewrite rules.
-/
private theorem transvection_vecMul_and_fixes_single_of_le {R : Type} [CommRing R] {n m : ℕ} (z u : Fin n → R)
    (h : u ⬝ᵥ z = 0) (hz : ∀ k : Fin n, m ≤ (k : ℕ) → z k = 0)
    (hu : ∀ k : Fin n, m ≤ (k : ℕ) → u k = 0) : ∃ T : GL (Fin n) R,
      (∀ x, Matrix.mulVec (T : Matrix (Fin n) (Fin n) R) x = x + (u ⬝ᵥ x) • z) ∧
      (∀ x, Matrix.vecMul x (T : Matrix (Fin n) (Fin n) R) = x + (x ⬝ᵥ z) • u) ∧
      (∀ j : Fin n, m ≤ (j : ℕ) →
        Matrix.mulVec (T : Matrix (Fin n) (Fin n) R) (Pi.single j (1 : R)) = Pi.single j 1 ∧
        Matrix.vecMul (Pi.single j (1 : R)) (T : Matrix (Fin n) (Fin n) R) = Pi.single j 1) := by
  obtain ⟨T, h1, h2, -, -⟩ := transvection_vecMul_and_inv_mulVec_vecMul_formulas z u h
  refine ⟨T, h1, h2, fun j hj => ⟨?_, ?_⟩⟩
  · rw [h1, dotProduct_single, hu j hj]
    simp
  · rw [h2, single_dotProduct, hz j hj]
    simp

/- English proof (translation)
Introduce `j hj`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec, (hb j hj).1, (ha j hj).1]`. Rewrite using `[Units.val_mul, ← Matrix.vecMul_vecMul, (ha j hj).2, (hb j hj).2]`.
-/
private theorem splitSet_transitive_lemma_3 {R : Type} [CommRing R] {n m : ℕ} (a b : GL (Fin n) R)
    (ha : ∀ j : Fin n, m ≤ (j : ℕ) →
      Matrix.mulVec (a : Matrix (Fin n) (Fin n) R) (Pi.single j (1 : R)) = Pi.single j 1 ∧
      Matrix.vecMul (Pi.single j (1 : R)) (a : Matrix (Fin n) (Fin n) R) = Pi.single j 1)
    (hb : ∀ j : Fin n, m ≤ (j : ℕ) →
      Matrix.mulVec (b : Matrix (Fin n) (Fin n) R) (Pi.single j (1 : R)) = Pi.single j 1 ∧
      Matrix.vecMul (Pi.single j (1 : R)) (b : Matrix (Fin n) (Fin n) R) = Pi.single j 1) :
    ∀ j : Fin n, m ≤ (j : ℕ) →
      Matrix.mulVec ((a * b : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) (Pi.single j (1 : R)) = Pi.single j 1 ∧
      Matrix.vecMul (Pi.single j (1 : R)) ((a * b : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Pi.single j 1 := by
  intro j hj
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, (hb j hj).1, (ha j hj).1]
  · rw [Units.val_mul, ← Matrix.vecMul_vecMul, (ha j hj).2, (hb j hj).2]

/- English proof (translation)
Use `set L : Fin n := ⟨m - 1, by omega⟩ with hL`. Establish `hsL : ∀ k : Fin n, m ≤ (k : ℕ) → (Pi.single L (1 : R) : Fin n → R) k = 0`. Introduce `k hk`. Establish `hne : k ≠ L`. Introduce `h`.

Rewrite `hk` using `[h]`. Simplify using `[L] at hk`. Use linear arithmetic over natural numbers and integers. Simplify using `[Pi.single_apply, hne]`. Establish `hr : Unimodular R (fun i : Fin (m - 1 + 1) => v ⟨i, by have` using `i.isLt; omega⟩) := by show Ideal.span _ = ⊤`.

Rewrite using `[Ideal.eq_top_iff_one, ← hwv]`. Use `show (∑ i, w i * v i) ∈ _`. Apply `Ideal.sum_mem` to reduce the goal to its premises. Introduce `k _`. Apply `Ideal.mul_mem_left` to reduce the goal to its premises.

Distinguish the cases in `hk : (k : ℕ) < m`. Apply `Ideal.subset_span` to reduce the goal to its premises. Conclude with `⟨⟨k, by omega⟩, rfl⟩`. Rewrite using `[hv k (by omega)]`. Conclude with `Ideal.zero_mem _`.

Take `⟨t, ht⟩` from `hs (m - 1) (by omega) _ hr`. Establish `ht' : (1 : R) ∈ Ideal.span (Set.range (fun i : Fin (m - 1) => v ⟨(Fin.castSucc i : ℕ), by have` using `(Fin.castSucc i).isLt; omega⟩ + t i * v ⟨(Fin.last (m - 1) : ℕ), by simp; omega⟩)) := by`. Rewrite using `[show Ideal.span _ = ⊤ from ht]`. Conclude with `Submodule.mem_top`. Take `⟨c, hc⟩` from `Ideal.mem_span_range_iff_exists_fun.mp ht'`.

Simplify using `only [Fin.coe_castSucc, Fin.val_last] at hc`. Use `set z1 : Fin n → R := fun k => if h : (k : ℕ) < m - 1 then t ⟨k, h⟩ else 0 with hz1`. Establish `z1L : z1 L = 0` using `by simp [z1, L]`. Establish `z1m : ∀ k : Fin n, m ≤ (k : ℕ) → z1 k = 0` using `fun k hk => by`. Simplify using `only [z1]`.

Rewrite using `[dif_neg (by omega)]`. Take `⟨T1, hT1, -, gT1⟩` from `transvection_vecMul_and_fixes_single_of_le (m := m) z1 (Pi.single L 1) (by rw [single_dotProduct, z1L, mul_zero]) z1m hsL`. Use `set v1 : Fin n → R := v + v L • z1 with hv1`. Establish `s1 : Matrix.mulVec (T1 : Matrix (Fin n) (Fin n) R) v = v1`. Rewrite using `[hT1, single_dotProduct, one_mul]`.

Use `set c' : Fin n → R := fun k => if h : (k : ℕ) < m - 1 then c ⟨k, h⟩ else 0 with hc'`. Use `set z2 : Fin n → R := (1 - v L) • Pi.single L 1 with hz2`. Establish `c'L : c' L = 0` using `by simp [c', L]`. Establish `c'm : ∀ k : Fin n, m ≤ (k : ℕ) → c' k = 0` using `fun k hk => by`. Simplify using `only [c']`.

Rewrite using `[dif_neg (by omega)]`. Establish `z2m : ∀ k : Fin n, m ≤ (k : ℕ) → z2 k = 0` using `fun k hk => by`. Simplify using `only [z2, Pi.smul_apply, hsL k hk, smul_zero]`. Take `⟨T2, hT2, -, gT2⟩` from `transvection_vecMul_and_fixes_single_of_le (m := m) z2 c' (by rw [hz2, dotProduct_smul, dotProduct_single, c'L]; simp) z2m c'm`. Establish `hc1 : c' ⬝ᵥ v1 = 1`.

Rewrite using `[← hc]`. Set `F : ℕ → R` to `fun k => if h : k < m - 1 then c ⟨k, h⟩ * (v ⟨k, by omega⟩ + t ⟨k, h⟩ * v L) else 0`. Establish `e1 : c' ⬝ᵥ v1 = ∑ k : Fin n, F k`. Simplify using `only [dotProduct]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `k _`. Simplify using `only [F, c', v1, z1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `split_ifs with h`. Simplify using `only [Fin.eta]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Apply the tactic sequence `rw [e1, Fin.sum_univ_eq_sum_range F n, ← Finset.sum_subset (s₁ := Finset.range (m - 1)) (s₂ := Finset.range n) (by intro k hk; rw [Finset.mem_range] at hk ⊢; exact lt_of_lt_of_le hk (by first | omega | exact L.isLt.le)) (fun k _ hk => dif_neg (by simp only [Finset.mem_range] at h …`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Simplify using `[F, hL]`.

Use `set v2 : Fin n → R := v1 + z2 with hv2`. Establish `s2 : Matrix.mulVec (T2 : Matrix (Fin n) (Fin n) R) v1 = v2`. Rewrite using `[hT2, hc1, one_smul]`. Establish `v2L : v2 L = 1`. Simplify using `only [v2, v1, z2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, z1L, Pi.single_eq_same]`.

Expand and normalize the polynomial expressions, which then agree. Use `set z3 : Fin n → R := fun k => if (k : ℕ) < m - 1 then -v2 k else 0 with hz3`. Establish `z3L : z3 L = 0` using `by simp [z3, L]`. Establish `z3m : ∀ k : Fin n, m ≤ (k : ℕ) → z3 k = 0` using `fun k hk => by`. Simplify using `only [z3]`.

Rewrite using `[if_neg (by omega)]`. Take `⟨T3, hT3, -, gT3⟩` from `transvection_vecMul_and_fixes_single_of_le (m := m) z3 (Pi.single L 1) (by rw [single_dotProduct, z3L, mul_zero]) z3m hsL`. Establish `s3 : Matrix.mulVec (T3 : Matrix (Fin n) (Fin n) R) v2 = Pi.single L 1`. Rewrite using `[hT3, single_dotProduct, one_mul, v2L, one_smul]`. Use function extensionality and compare the values at `k`.

Simplify using `only [Pi.add_apply, z3]`. Distinguish the cases in `hk : (k : ℕ) < m - 1`. Rewrite using `[if_pos hk, add_neg_cancel]`. Establish `hne : k ≠ L`. Introduce `h`.

Rewrite `hk` using `[h]`. Simplify using `[L] at hk`. Simplify using `[Pi.single_apply, hne]`. Rewrite using `[if_neg hk, add_zero]`. Distinguish the cases in `hk2 : k = L`.

Rewrite using `[hk2, v2L]`. Simplify using the standard rewrite rules. Establish `hkm : m ≤ (k : ℕ)`. Establish `: (k : ℕ) ≠ m - 1` using `fun h => hk2 (Fin.ext (by simpa [L] using h))`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [v2, v1, z2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv k hkm, z1m k hkm, hsL k hkm]`. Simplify using `[Pi.single_apply, hk2]`. Establish `hg0v : Matrix.mulVec ((T3 * T2 * T1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) v = Pi.single L 1`. Rewrite using `[Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, s1, s2, s3]`. Establish `gg0` using `splitSet_transitive_lemma_3 (T3 * T2) T1 (splitSet_transitive_lemma_3 T3 T2 gT3 gT2) gT1`.

Use `set g0 : GL (Fin n) R := T3 * T2 * T1 with hg0`. Establish `hinv : ∀ x y, Matrix.mulVec (g0 : Matrix (Fin n) (Fin n) R) x = y → Matrix.mulVec ((g0⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) y = x`. Introduce `x y h`. Rewrite using `[← h, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `hiv` using `hinv v _ hg0v`.

Use `set w' : Fin n → R := Matrix.vecMul w ((g0⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hw'`. Establish `w'dot : ∀ x y, Matrix.mulVec ((g0⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) x = y → w' ⬝ᵥ x = w ⬝ᵥ y`. Introduce `x y h`. Rewrite using `[hw', ← Matrix.dotProduct_mulVec, h]`. Establish `w'L : w' L = 1`.

Use `w'dot (Pi.single L 1) v hiv` as an intermediate fact. Rewrite `this` using `[dotProduct_single, mul_one]`. Rewrite using `[this, hwv]`. Establish `w'm : ∀ k : Fin n, m ≤ (k : ℕ) → w' k = 0`. Introduce `k hk`.

Use `w'dot (Pi.single k 1) (Pi.single k 1) (hinv _ _ (gg0 k hk).1)` as an intermediate fact. Rewrite `this` using `[dotProduct_single, mul_one, dotProduct_single, mul_one, hw k hk]`. Conclude with `this`. Use `set u4 : Fin n → R := w' - Pi.single L 1 with hu4`. Take `⟨T4, hT4, hT4', gT4⟩` from `transvection_vecMul_and_fixes_single_of_le (m := m) (Pi.single L 1) u4 (by rw [dotProduct_single, mul_one, hu4, Pi.sub_apply, w'L, Pi.single_eq_same, sub_self]) hsL (fun k hk => by rw [hu4, Pi.sub_apply, w'm k hk, hsL k hk, sub_zero])`.

Use `⟨T4 * g0, ?_, ?_, splitSet_transitive_lemma_3 T4 g0 gT4 gg0⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec, hg0v, hT4, dotProduct_single, mul_one, hu4, Pi.sub_apply, w'L, Pi.single_eq_same, sub_self, zero_smul, add_zero]`. Rewrite using `[Units.val_mul, ← Matrix.vecMul_vecMul, hT4', single_dotProduct, one_mul, Pi.single_eq_same, one_smul, hu4, add_sub_cancel, hw', Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]`.
-/
private theorem exists_gl_vecMul_single_eq_and_fixes_single_of_le {R : Type} [CommRing R] (s : ℕ) (hs : StableRangeLe R s)
    {n m : ℕ} (hm : s + 1 ≤ m) (hmn : m ≤ n) (v w : Fin n → R)
    (hv : ∀ k : Fin n, m ≤ (k : ℕ) → v k = 0) (hw : ∀ k : Fin n, m ≤ (k : ℕ) → w k = 0)
    (hwv : w ⬝ᵥ v = 1) : ∃ g : GL (Fin n) R,
      Matrix.mulVec (g : Matrix (Fin n) (Fin n) R) v = Pi.single (⟨m - 1, by omega⟩ : Fin n) 1 ∧
      Matrix.vecMul (Pi.single (⟨m - 1, by omega⟩ : Fin n) (1 : R)) (g : Matrix (Fin n) (Fin n) R) = w ∧
      (∀ j : Fin n, m ≤ (j : ℕ) →
        Matrix.mulVec (g : Matrix (Fin n) (Fin n) R) (Pi.single j (1 : R)) = Pi.single j 1 ∧
        Matrix.vecMul (Pi.single j (1 : R)) (g : Matrix (Fin n) (Fin n) R) = Pi.single j 1) := by
  set L : Fin n := ⟨m - 1, by omega⟩ with hL
  have hsL : ∀ k : Fin n, m ≤ (k : ℕ) → (Pi.single L (1 : R) : Fin n → R) k = 0 := by
    intro k hk
    have hne : k ≠ L := by
      intro h
      rw [h] at hk
      simp [L] at hk
      omega
    simp [Pi.single_apply, hne]
  have hr : Unimodular R (fun i : Fin (m - 1 + 1) => v ⟨i, by have := i.isLt; omega⟩) := by
    show Ideal.span _ = ⊤
    rw [Ideal.eq_top_iff_one, ← hwv]
    show (∑ i, w i * v i) ∈ _
    apply Ideal.sum_mem
    intro k _
    apply Ideal.mul_mem_left
    by_cases hk : (k : ℕ) < m
    · apply Ideal.subset_span
      exact ⟨⟨k, by omega⟩, rfl⟩
    · rw [hv k (by omega)]
      exact Ideal.zero_mem _
  obtain ⟨t, ht⟩ := hs (m - 1) (by omega) _ hr
  have ht' : (1 : R) ∈ Ideal.span (Set.range (fun i : Fin (m - 1) =>
      v ⟨(Fin.castSucc i : ℕ), by have := (Fin.castSucc i).isLt; omega⟩ +
        t i * v ⟨(Fin.last (m - 1) : ℕ), by simp; omega⟩)) := by
    rw [show Ideal.span _ = ⊤ from ht]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ht'
  simp only [Fin.coe_castSucc, Fin.val_last] at hc
  set z1 : Fin n → R := fun k => if h : (k : ℕ) < m - 1 then t ⟨k, h⟩ else 0 with hz1
  have z1L : z1 L = 0 := by simp [z1, L]
  have z1m : ∀ k : Fin n, m ≤ (k : ℕ) → z1 k = 0 := fun k hk => by
    simp only [z1]
    rw [dif_neg (by omega)]
  obtain ⟨T1, hT1, -, gT1⟩ := transvection_vecMul_and_fixes_single_of_le (m := m) z1 (Pi.single L 1)
    (by rw [single_dotProduct, z1L, mul_zero]) z1m hsL
  set v1 : Fin n → R := v + v L • z1 with hv1
  have s1 : Matrix.mulVec (T1 : Matrix (Fin n) (Fin n) R) v = v1 := by
    rw [hT1, single_dotProduct, one_mul]
  set c' : Fin n → R := fun k => if h : (k : ℕ) < m - 1 then c ⟨k, h⟩ else 0 with hc'
  set z2 : Fin n → R := (1 - v L) • Pi.single L 1 with hz2
  have c'L : c' L = 0 := by simp [c', L]
  have c'm : ∀ k : Fin n, m ≤ (k : ℕ) → c' k = 0 := fun k hk => by
    simp only [c']
    rw [dif_neg (by omega)]
  have z2m : ∀ k : Fin n, m ≤ (k : ℕ) → z2 k = 0 := fun k hk => by
    simp only [z2, Pi.smul_apply, hsL k hk, smul_zero]
  obtain ⟨T2, hT2, -, gT2⟩ := transvection_vecMul_and_fixes_single_of_le (m := m) z2 c'
    (by rw [hz2, dotProduct_smul, dotProduct_single, c'L]; simp) z2m c'm
  have hc1 : c' ⬝ᵥ v1 = 1 := by
    rw [← hc]
    let F : ℕ → R := fun k => if h : k < m - 1 then c ⟨k, h⟩ * (v ⟨k, by omega⟩ + t ⟨k, h⟩ * v L) else 0
    have e1 : c' ⬝ᵥ v1 = ∑ k : Fin n, F k := by
      simp only [dotProduct]
      apply Finset.sum_congr rfl
      intro k _
      simp only [F, c', v1, z1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs with h
      · simp only [Fin.eta]
        ring
      · simp
    rw [e1, Fin.sum_univ_eq_sum_range F n, ← Finset.sum_subset (s₁ := Finset.range (m - 1)) (s₂ := Finset.range n)
      (by intro k hk; rw [Finset.mem_range] at hk ⊢; exact lt_of_lt_of_le hk (by first | omega | exact L.isLt.le))
      (fun k _ hk => dif_neg (by simp only [Finset.mem_range] at hk; omega)),
      ← Fin.sum_univ_eq_sum_range F (m - 1)]
    apply Finset.sum_congr rfl
    intro i _
    simp [F, hL]
  set v2 : Fin n → R := v1 + z2 with hv2
  have s2 : Matrix.mulVec (T2 : Matrix (Fin n) (Fin n) R) v1 = v2 := by
    rw [hT2, hc1, one_smul]
  have v2L : v2 L = 1 := by
    simp only [v2, v1, z2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, z1L, Pi.single_eq_same]
    ring
  set z3 : Fin n → R := fun k => if (k : ℕ) < m - 1 then -v2 k else 0 with hz3
  have z3L : z3 L = 0 := by simp [z3, L]
  have z3m : ∀ k : Fin n, m ≤ (k : ℕ) → z3 k = 0 := fun k hk => by
    simp only [z3]
    rw [if_neg (by omega)]
  obtain ⟨T3, hT3, -, gT3⟩ := transvection_vecMul_and_fixes_single_of_le (m := m) z3 (Pi.single L 1)
    (by rw [single_dotProduct, z3L, mul_zero]) z3m hsL
  have s3 : Matrix.mulVec (T3 : Matrix (Fin n) (Fin n) R) v2 = Pi.single L 1 := by
    rw [hT3, single_dotProduct, one_mul, v2L, one_smul]
    funext k
    simp only [Pi.add_apply, z3]
    by_cases hk : (k : ℕ) < m - 1
    · rw [if_pos hk, add_neg_cancel]
      have hne : k ≠ L := by
        intro h
        rw [h] at hk
        simp [L] at hk
      simp [Pi.single_apply, hne]
    · rw [if_neg hk, add_zero]
      by_cases hk2 : k = L
      · rw [hk2, v2L]
        simp
      · have hkm : m ≤ (k : ℕ) := by
          have : (k : ℕ) ≠ m - 1 := fun h => hk2 (Fin.ext (by simpa [L] using h))
          omega
        simp only [v2, v1, z2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv k hkm, z1m k hkm, hsL k hkm]
        simp [Pi.single_apply, hk2]
  have hg0v : Matrix.mulVec ((T3 * T2 * T1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) v = Pi.single L 1 := by
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, s1, s2, s3]
  have gg0 := splitSet_transitive_lemma_3 (T3 * T2) T1 (splitSet_transitive_lemma_3 T3 T2 gT3 gT2) gT1
  set g0 : GL (Fin n) R := T3 * T2 * T1 with hg0
  have hinv : ∀ x y, Matrix.mulVec (g0 : Matrix (Fin n) (Fin n) R) x = y →
      Matrix.mulVec ((g0⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) y = x := by
    intro x y h
    rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hiv := hinv v _ hg0v
  set w' : Fin n → R := Matrix.vecMul w ((g0⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hw'
  have w'dot : ∀ x y, Matrix.mulVec ((g0⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) x = y →
      w' ⬝ᵥ x = w ⬝ᵥ y := by
    intro x y h
    rw [hw', ← Matrix.dotProduct_mulVec, h]
  have w'L : w' L = 1 := by
    have := w'dot (Pi.single L 1) v hiv
    rw [dotProduct_single, mul_one] at this
    rw [this, hwv]
  have w'm : ∀ k : Fin n, m ≤ (k : ℕ) → w' k = 0 := by
    intro k hk
    have := w'dot (Pi.single k 1) (Pi.single k 1) (hinv _ _ (gg0 k hk).1)
    rw [dotProduct_single, mul_one, dotProduct_single, mul_one, hw k hk] at this
    exact this
  set u4 : Fin n → R := w' - Pi.single L 1 with hu4
  obtain ⟨T4, hT4, hT4', gT4⟩ := transvection_vecMul_and_fixes_single_of_le (m := m) (Pi.single L 1) u4
    (by rw [dotProduct_single, mul_one, hu4, Pi.sub_apply, w'L, Pi.single_eq_same, sub_self])
    hsL (fun k hk => by rw [hu4, Pi.sub_apply, w'm k hk, hsL k hk, sub_zero])
  refine ⟨T4 * g0, ?_, ?_, splitSet_transitive_lemma_3 T4 g0 gT4 gg0⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg0v, hT4, dotProduct_single, mul_one, hu4,
      Pi.sub_apply, w'L, Pi.single_eq_same, sub_self, zero_smul, add_zero]
  · rw [Units.val_mul, ← Matrix.vecMul_vecMul, hT4', single_dotProduct, one_mul, Pi.single_eq_same,
      one_smul, hu4, add_sub_cancel, hw', Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.vecMul_one]

/- English proof (translation)
Introduce `R _ s hs n p`. Establish `hE : ∀ i (hi : i < n), (fun k : Fin n => if (k : ℕ) = i then (1 : R) else 0) = Pi.single (⟨i, hi⟩ : Fin n) 1`. Introduce `i hi`. Use function extensionality and compare the values at `k`. Simplify using `[Pi.single_apply, Fin.ext_iff]`.

Establish `hmul : ∀ (a b : GL (Fin n) R) x, pairAct R n (a * b) x = pairAct R n a (pairAct R n b x)`. Introduce `a b x`. Simplify using `only [pairAct]`. Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec, mul_inv_rev, Units.val_mul, ← Matrix.vecMul_vecMul]`. Establish `hone : ∀ x, pairAct R n 1 x = x`.

Introduce `x`. Simplify using `only [pairAct, inv_one, Units.val_one, Matrix.one_mulVec, Matrix.vecMul_one]`. Establish `hval : ∀ (g : GL (Fin n) R) {q : ℕ} (y : SplitSet R n q), (g • y).val = List.map (pairAct R n g) y.val` using `fun _ _ _ => rfl`. Proceed by induction on `p with`. Consider the case `zero`.

Introduce `h _ y`. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul]`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hy : y.val = []` using `List.eq_nil_of_length_eq_zero y.2.2`.

Rewrite using `[hy]`. Use `show stdList R n 0 = []`. Simplify using `[stdList]`. Consider the case `succ p ih`. Introduce `h hps y`.

Take `⟨l, hsp, hlen⟩` from `y`. Consider the cases of `l with`. Consider the case `nil => simp at hlen`. Consider the case `cons a rest`. Establish `hrest : rest ∈ splitSeq R n`.

Introduce `i j`. Use `hsp i.succ j.succ` as an intermediate fact. Simplify `this` using `[Fin.succ_inj]`. Take `⟨g0, hg0⟩` from `ih (by omega) (by omega) ⟨rest, hrest, by simpa using hlen⟩`. Establish `hstd : List.map (pairAct R n g0) (stdList R n p) = rest` using `congrArg Subtype.val hg0`.

Establish `hstd' : List.map (pairAct R n g0⁻¹) rest = stdList R n p`. Rewrite using `[← hstd, List.map_map]`. Establish `hc : (pairAct R n g0⁻¹ ∘ pairAct R n g0) = id`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp, ← hmul, inv_mul_cancel, hone, id]`.

Rewrite using `[hc, List.map_id]`. Establish `hsp' : pairAct R n g0⁻¹ a :: stdList R n p ∈ splitSeq R n`. Set `y0 : SplitSet R n (p + 1)` to `⟨a :: rest, hsp, hlen⟩`. Establish `e : (g0⁻¹ • y0).val = pairAct R n g0⁻¹ a :: stdList R n p`. Rewrite using `[hval]`.

Use `show List.map (pairAct R n g0⁻¹) (a :: rest) = _`. Rewrite using `[List.map_cons, hstd']`. Rewrite using `[← e]`. Conclude with `(g0⁻¹ • y0).2.1`. Establish `hwv : (pairAct R n g0⁻¹ a).2 ⬝ᵥ (pairAct R n g0⁻¹ a).1 = 1`.

Use `hsp' ⟨0, by simp⟩ ⟨0, by simp⟩` as an intermediate fact. Simplify using `using this`. Establish `hv : ∀ k : Fin n, n - p ≤ (k : ℕ) → (pairAct R n g0⁻¹ a).1 k = 0`. Introduce `k hk`. Use `hsp' ⟨(k : ℕ) - (n - p) + 1, by simp [stdList]; omega⟩ ⟨0, by simp⟩` as an intermediate fact.

Simplify using `[stdList] at this`. Rewrite `this` using `[hE _ (by omega), single_dotProduct, one_mul]`. Establish `hk' : (⟨n - p + ((k : ℕ) - (n - p)), by omega⟩ : Fin n) = k` using `Fin.ext (by simp; omega)`. Rewrite `this` using `[hk']`. Rewrite using `[this]`.

Use `split_ifs with hc`. Use `first`. Consider the case `exact absurd (congrArg Fin.val hc) (by simp)`. Consider the case `exact absurd hc (by simp [Fin.ext_iff])`. Consider the case `simp [Fin.ext_iff] at hc`.

Both sides reduce to the same expression. Establish `hw : ∀ k : Fin n, n - p ≤ (k : ℕ) → (pairAct R n g0⁻¹ a).2 k = 0`. Introduce `k hk`. Use `hsp' ⟨0, by simp⟩ ⟨(k : ℕ) - (n - p) + 1, by simp [stdList]; omega⟩` as an intermediate fact. Simplify using `[stdList] at this`.

Rewrite `this` using `[hE _ (by omega), dotProduct_single, mul_one]`. Establish `hk' : (⟨n - p + ((k : ℕ) - (n - p)), by omega⟩ : Fin n) = k` using `Fin.ext (by simp; omega)`. Rewrite `this` using `[hk']`. Rewrite using `[this]`. Use `split_ifs with hc`.

Use `first`. Consider the case `exact absurd (congrArg Fin.val hc) (by simp)`. Consider the case `exact absurd hc (by simp [Fin.ext_iff])`. Consider the case `simp [Fin.ext_iff] at hc`. Both sides reduce to the same expression.

Take `⟨g1, hg1v, hg1w, hg1good⟩` from `exists_gl_vecMul_single_eq_and_fixes_single_of_le s hs (m := n - p) (by omega) (by omega) _ _ hv hw hwv`. Establish `hinv1 : ∀ x y, Matrix.mulVec (g1 : Matrix (Fin n) (Fin n) R) x = y → Matrix.mulVec ((g1⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) y = x`. Introduce `x y hxy`. Rewrite using `[← hxy, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Use `⟨g0 * g1⁻¹, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hval]`. Use `show List.map (pairAct R n (g0 * g1⁻¹)) (stdList R n (p + 1)) = a :: rest`. Establish `hLL : (⟨n - (p + 1), by omega⟩ : Fin n) = ⟨n - p - 1, by omega⟩` using `Fin.ext (by simp; omega)`. Establish `hsplit : stdList R n (p + 1) = (Pi.single (⟨n - p - 1, by omega⟩ : Fin n) (1 : R), Pi.single (⟨n - p - 1, by omega⟩ : Fin n) (1 : R)) :: stdList R n p`.

Simplify using `only [stdList, List.ofFn_succ]`. Use `congr 1`. Rewrite using `[Fin.val_zero, add_zero, hE (n - (p + 1)) (by omega), hLL]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `only [Fin.val_succ, show n - (p + 1) + ((i : ℕ) + 1) = n - p + (i : ℕ) by omega]`. Rewrite using `[hsplit, List.map_cons, hmul]`. Use `congr 1`. Establish `h1 : pairAct R n g1⁻¹ (Pi.single (⟨n - p - 1, by omega⟩ : Fin n) (1 : R), Pi.single (⟨n - p - 1, by omega⟩ : Fin n) (1 : R)) = pairAct R n g0⁻¹ a`. Apply `Prod.ext` to reduce the goal to its premises.

Conclude with `hinv1 _ _ hg1v`. Use `show Matrix.vecMul _ (((g1⁻¹)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = _`. Rewrite using `[inv_inv, hg1w]`. Rewrite using `[h1, ← hmul, mul_inv_cancel, hone]`. Rewrite using `[← hstd]`.

Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[hmul]`. Use `congr 1`. Take `⟨j, rfl⟩` from `List.mem_ofFn.mp hx`.

Rewrite using `[hE _ (by omega)]`. Establish `hg` using `hg1good ⟨n - p + (j : ℕ), by omega⟩ (by simp)`. Apply `Prod.ext` to reduce the goal to its premises. Conclude with `hinv1 _ _ hg.1`. Use `show Matrix.vecMul _ (((g1⁻¹)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = _`.

Rewrite using `[inv_inv, hg.2]`.
-/
theorem splitSet_transitive : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n p : ℕ) (h : p ≤ n),
    p + s ≤ n → ∀ y : SplitSet R n p, ∃ g : GL (Fin n) R, g • stdSeq R n p h = y := by
  intro R _ s hs n p
  have hE : ∀ i (hi : i < n),
      (fun k : Fin n => if (k : ℕ) = i then (1 : R) else 0) = Pi.single (⟨i, hi⟩ : Fin n) 1 := by
    intro i hi
    funext k
    simp [Pi.single_apply, Fin.ext_iff]
  have hmul : ∀ (a b : GL (Fin n) R) x,
      pairAct R n (a * b) x = pairAct R n a (pairAct R n b x) := by
    intro a b x
    simp only [pairAct]
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, mul_inv_rev, Units.val_mul, ← Matrix.vecMul_vecMul]
  have hone : ∀ x, pairAct R n 1 x = x := by
    intro x
    simp only [pairAct, inv_one, Units.val_one, Matrix.one_mulVec, Matrix.vecMul_one]
  have hval : ∀ (g : GL (Fin n) R) {q : ℕ} (y : SplitSet R n q),
      (g • y).val = List.map (pairAct R n g) y.val := fun _ _ _ => rfl
  induction p with
  | zero =>
    intro h _ y
    refine ⟨1, ?_⟩
    rw [one_smul]
    apply Subtype.ext
    have hy : y.val = [] := List.eq_nil_of_length_eq_zero y.2.2
    rw [hy]
    show stdList R n 0 = []
    simp [stdList]
  | succ p ih =>
    intro h hps y
    obtain ⟨l, hsp, hlen⟩ := y
    cases l with
    | nil => simp at hlen
    | cons a rest =>
      have hrest : rest ∈ splitSeq R n := by
        intro i j
        have := hsp i.succ j.succ
        simpa [Fin.succ_inj] using this
      obtain ⟨g0, hg0⟩ := ih (by omega) (by omega) ⟨rest, hrest, by simpa using hlen⟩
      have hstd : List.map (pairAct R n g0) (stdList R n p) = rest := congrArg Subtype.val hg0
      have hstd' : List.map (pairAct R n g0⁻¹) rest = stdList R n p := by
        rw [← hstd, List.map_map]
        have hc : (pairAct R n g0⁻¹ ∘ pairAct R n g0) = id := by
          funext x
          simp only [Function.comp, ← hmul, inv_mul_cancel, hone, id]
        rw [hc, List.map_id]
      have hsp' : pairAct R n g0⁻¹ a :: stdList R n p ∈ splitSeq R n := by
        let y0 : SplitSet R n (p + 1) := ⟨a :: rest, hsp, hlen⟩
        have e : (g0⁻¹ • y0).val = pairAct R n g0⁻¹ a :: stdList R n p := by
          rw [hval]
          show List.map (pairAct R n g0⁻¹) (a :: rest) = _
          rw [List.map_cons, hstd']
        rw [← e]
        exact (g0⁻¹ • y0).2.1
      have hwv : (pairAct R n g0⁻¹ a).2 ⬝ᵥ (pairAct R n g0⁻¹ a).1 = 1 := by
        have := hsp' ⟨0, by simp⟩ ⟨0, by simp⟩
        simpa using this
      have hv : ∀ k : Fin n, n - p ≤ (k : ℕ) → (pairAct R n g0⁻¹ a).1 k = 0 := by
        intro k hk
        have := hsp' ⟨(k : ℕ) - (n - p) + 1, by simp [stdList]; omega⟩ ⟨0, by simp⟩
        simp [stdList] at this
        rw [hE _ (by omega), single_dotProduct, one_mul] at this
        have hk' : (⟨n - p + ((k : ℕ) - (n - p)), by omega⟩ : Fin n) = k := Fin.ext (by simp; omega)
        rw [hk'] at this
        rw [this]
        split_ifs with hc
        · first
            | exact absurd (congrArg Fin.val hc) (by simp)
            | exact absurd hc (by simp [Fin.ext_iff])
            | simp [Fin.ext_iff] at hc
        · rfl
      have hw : ∀ k : Fin n, n - p ≤ (k : ℕ) → (pairAct R n g0⁻¹ a).2 k = 0 := by
        intro k hk
        have := hsp' ⟨0, by simp⟩ ⟨(k : ℕ) - (n - p) + 1, by simp [stdList]; omega⟩
        simp [stdList] at this
        rw [hE _ (by omega), dotProduct_single, mul_one] at this
        have hk' : (⟨n - p + ((k : ℕ) - (n - p)), by omega⟩ : Fin n) = k := Fin.ext (by simp; omega)
        rw [hk'] at this
        rw [this]
        split_ifs with hc
        · first
            | exact absurd (congrArg Fin.val hc) (by simp)
            | exact absurd hc (by simp [Fin.ext_iff])
            | simp [Fin.ext_iff] at hc
        · rfl
      obtain ⟨g1, hg1v, hg1w, hg1good⟩ := exists_gl_vecMul_single_eq_and_fixes_single_of_le s hs (m := n - p) (by omega) (by omega)
        _ _ hv hw hwv
      have hinv1 : ∀ x y, Matrix.mulVec (g1 : Matrix (Fin n) (Fin n) R) x = y →
          Matrix.mulVec ((g1⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) y = x := by
        intro x y hxy
        rw [← hxy, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      refine ⟨g0 * g1⁻¹, ?_⟩
      apply Subtype.ext
      rw [hval]
      show List.map (pairAct R n (g0 * g1⁻¹)) (stdList R n (p + 1)) = a :: rest
      have hLL : (⟨n - (p + 1), by omega⟩ : Fin n) = ⟨n - p - 1, by omega⟩ := Fin.ext (by simp; omega)
      have hsplit : stdList R n (p + 1) =
          (Pi.single (⟨n - p - 1, by omega⟩ : Fin n) (1 : R), Pi.single (⟨n - p - 1, by omega⟩ : Fin n) (1 : R))
            :: stdList R n p := by
        simp only [stdList, List.ofFn_succ]
        congr 1
        · rw [Fin.val_zero, add_zero, hE (n - (p + 1)) (by omega), hLL]
        · congr 1
          funext i
          simp only [Fin.val_succ, show n - (p + 1) + ((i : ℕ) + 1) = n - p + (i : ℕ) by omega]
      rw [hsplit, List.map_cons, hmul]
      congr 1
      · have h1 : pairAct R n g1⁻¹ (Pi.single (⟨n - p - 1, by omega⟩ : Fin n) (1 : R),
            Pi.single (⟨n - p - 1, by omega⟩ : Fin n) (1 : R)) = pairAct R n g0⁻¹ a := by
          apply Prod.ext
          · exact hinv1 _ _ hg1v
          · show Matrix.vecMul _ (((g1⁻¹)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = _
            rw [inv_inv, hg1w]
        rw [h1, ← hmul, mul_inv_cancel, hone]
      · rw [← hstd]
        apply List.map_congr_left
        intro x hx
        rw [hmul]
        congr 1
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
        rw [hE _ (by omega)]
        have hg := hg1good ⟨n - p + (j : ℕ), by omega⟩ (by simp)
        apply Prod.ext
        · exact hinv1 _ _ hg.1
        · show Matrix.vecMul _ (((g1⁻¹)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = _
          rw [inv_inv, hg.2]

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.HomStab.splitSet_transitive`.
-/
theorem _root_.GlobalTheory.T.GL_transitive_splitSet_of_stableRangeLe : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n p : ℕ) (h : p ≤ n), p + s ≤ n → ∀ y : SplitSet R n p, ∃ g : GL (Fin n) R, g • stdSeq R n p h = y := by
  first
  | exact @GlobalTheory.HomStab.splitSet_transitive
end
