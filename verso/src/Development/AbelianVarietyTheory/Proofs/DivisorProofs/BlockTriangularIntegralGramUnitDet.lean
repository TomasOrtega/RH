import Mathlib

namespace GlobalTheory

namespace TriDiagFrames

variable {K : Type} [Field K]

/- English proof (translation)
Establish `key : ∀ a b : K, w a ≤ w b → w (a + b) ≤ w b`. Introduce `a b h`. Distinguish the cases in `hb : b = 0`. Substitute `hb` using the available equality. Establish `ha : a = 0` using `w.eq_zero.1 (le_antisymm (by simpa using h) (w.nonneg a))`.

Simplify using `[ha]`. Establish `hwb : 0 < w b` using `w.pos hb`. Establish `h1 : w (a / b) ≤ 1`. Rewrite using `[map_div₀]`. Conclude with `(div_le_one hwb).2 h`.

Establish `h2 : (1 + a / b) ∈ O` using `add_mem (one_mem O) ((hO _).2 h1)`. Establish `h3 : w (1 + a / b) ≤ 1` using `(hO _).1 h2`. Establish `h4 : a + b = b * (1 + a / b)` using `by field_simp; ring`. Rewrite using `[h4, map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Break down `le_total (w a) (w b) with h | h` into its components or cases. Conclude with `(key a b h).trans (le_max_right _ _)`. Rewrite using `[add_comm]`. Conclude with `(key b a h).trans (le_max_left _ _)`.
-/
theorem ultra (w : AbsoluteValue K ℝ) (O : ValuationSubring K) (hO : ∀ x, x ∈ O ↔ w x ≤ 1)
    (a b : K) : w (a + b) ≤ max (w a) (w b) := by
  have key : ∀ a b : K, w a ≤ w b → w (a + b) ≤ w b := by
    intro a b h
    by_cases hb : b = 0
    · subst hb
      have ha : a = 0 := w.eq_zero.1 (le_antisymm (by simpa using h) (w.nonneg a))
      simp [ha]
    · have hwb : 0 < w b := w.pos hb
      have h1 : w (a / b) ≤ 1 := by
        rw [map_div₀]; exact (div_le_one hwb).2 h
      have h2 : (1 + a / b) ∈ O := add_mem (one_mem O) ((hO _).2 h1)
      have h3 : w (1 + a / b) ≤ 1 := (hO _).1 h2
      have h4 : a + b = b * (1 + a / b) := by field_simp; ring
      rw [h4, map_mul]
      calc w b * w (1 + a / b) ≤ w b * 1 := mul_le_mul_of_nonneg_left h3 (w.nonneg b)
        _ = w b := mul_one _
  rcases le_total (w a) (w b) with h | h
  · exact (key a b h).trans (le_max_right _ _)
  · rw [add_comm]; exact (key b a h).trans (le_max_left _ _)

/- English proof (translation)
Establish `u1` using `ultra w O hO (x - d) d`. Establish `u2` using `ultra w O hO (d - x) x`. Simplify using `only [sub_add_cancel] at u1 u2`. Rewrite `u2` using `[AbsoluteValue.map_sub]`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `u1.trans (max_le h.le le_rfl)`. Break down `le_max_iff.1 u2 with h' | h'` into its components or cases. Conclude with `absurd (h'.trans_lt h) (lt_irrefl _)`. Conclude with `h'`.
-/
theorem eq_of_sub_lt (w : AbsoluteValue K ℝ) (O : ValuationSubring K) (hO : ∀ x, x ∈ O ↔ w x ≤ 1)
    {x d : K} (h : w (x - d) < w d) : w x = w d := by
  have u1 := ultra w O hO (x - d) d
  have u2 := ultra w O hO (d - x) x
  simp only [sub_add_cancel] at u1 u2
  rw [AbsoluteValue.map_sub] at u2
  apply le_antisymm
  · exact u1.trans (max_le h.le le_rfl)
  · rcases le_max_iff.1 u2 with h' | h'
    · exact absurd (h'.trans_lt h) (lt_irrefl _)
    · exact h'

/- English proof (translation)
Set `M' : Matrix (Fin N) (Fin N) O` to `Matrix.of fun i j => ⟨M i j, hM i j⟩`. Establish `hMM : M = O.subtype.mapMatrix M'` using `by ext i j; rfl`. Establish `hadj : M.adjugate = O.subtype.mapMatrix M'.adjugate`. Rewrite using `[hMM]`. Conclude with `(RingHom.map_adjugate _ _).symm`.

Rewrite using `[Matrix.inv_def, Matrix.smul_apply, hadj, Ring.inverse_eq_inv, smul_eq_mul]`. Use `mul_mem ((hO _).2 ?_) ?_` and prove the remaining obligations. Rewrite using `[map_inv₀, hdet, inv_one]`. Conclude with `(M'.adjugate i j).2`.
-/
theorem inv_entry_mem {N : ℕ} (w : AbsoluteValue K ℝ) (O : ValuationSubring K)
    (hO : ∀ x, x ∈ O ↔ w x ≤ 1) (M : Matrix (Fin N) (Fin N) K) (hM : ∀ i j, M i j ∈ O)
    (hdet : w M.det = 1) (i j : Fin N) : M⁻¹ i j ∈ O := by
  let M' : Matrix (Fin N) (Fin N) O := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have hMM : M = O.subtype.mapMatrix M' := by ext i j; rfl
  have hadj : M.adjugate = O.subtype.mapMatrix M'.adjugate := by
    rw [hMM]; exact (RingHom.map_adjugate _ _).symm
  rw [Matrix.inv_def, Matrix.smul_apply, hadj, Ring.inverse_eq_inv, smul_eq_mul]
  refine mul_mem ((hO _).2 ?_) ?_
  · rw [map_inv₀, hdet, inv_one]
  · exact (M'.adjugate i j).2

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Conclude with `sum_mem fun k _ => mul_mem (hA i k) (hB k j)`.
-/
theorem mul_entry_mem {N : ℕ} (O : ValuationSubring K) (A B : Matrix (Fin N) (Fin N) K)
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) (i j : Fin N) : (A * B) i j ∈ O := by
  rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Introduce `j _ hji`. Break down `lt_or_gt_of_ne hji with h | h` into its components or cases. Rewrite using `[@hA i j h, zero_mul]`. Rewrite using `[@hB j i h, mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem diag_mul {N : ℕ} (A B : Matrix (Fin N) (Fin N) K) (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin N) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [@hA i j h, zero_mul]
    · rw [@hB j i h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

end TriDiagFrames

/- English proof (translation)
Introduce `K _ w O hO N G Ba Bb d ga gb hTa hTb hga hgb hEa hEb hDa hDb i`. Establish `hne : ∀ B : Matrix (Fin N) (Fin N) K, w (G * B).det = 1 → IsUnit G.det ∧ IsUnit B.det`. Introduce `B hB`. Establish `h0 : (G * B).det ≠ 0`. Introduce `h`.

Rewrite `hB` using `[h, map_zero]`. Conclude with `zero_ne_one hB`. Rewrite `h0` using `[Matrix.det_mul]`. Conclude with `⟨isUnit_iff_ne_zero.2 (left_ne_zero_of_mul h0), isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h0)⟩`. Take `⟨hG, hUa⟩` from `hne Ba hDa`.

Take `⟨-, hUb⟩` from `hne Bb hDb`. Establish `red : ∀ B C : Matrix (Fin N) (Fin N) K, (G * B)⁻¹ * (G * C) = B⁻¹ * C`. Introduce `B C`. Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc G⁻¹, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]`. Establish `triInv : ∀ B : Matrix (Fin N) (Fin N) K, B.BlockTriangular id → IsUnit B.det → B⁻¹.BlockTriangular id`.

Introduce `B hB hU`. Use `haveI := B.invertibleOfIsUnitDet hU`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hB`. Establish `hTa'` using `triInv Ba hTa hUa`. Establish `hTb'` using `triInv Bb hTb hUb`.

Establish `memA : ∀ a b, (G * Ba) a b ∈ O` using `fun a b => (hO _).2 (hEa a b)`. Establish `memB : ∀ a b, (G * Bb) a b ∈ O` using `fun a b => (hO _).2 (hEb a b)`. Establish `t1 : w ((Ba⁻¹ * Bb) i i) ≤ 1`. Rewrite using `[← red]`. Conclude with `(hO _).1 (TriDiagFrames.mul_entry_mem O _ _ (TriDiagFrames.inv_entry_mem w O hO _ memA hDa) memB i i)`.

Establish `t2 : w ((Bb⁻¹ * Ba) i i) ≤ 1`. Rewrite using `[← red]`. Conclude with `(hO _).1 (TriDiagFrames.mul_entry_mem O _ _ (TriDiagFrames.inv_entry_mem w O hO _ memB hDb) memA i i)`. Rewrite using `[red]`. Use `⟨fun k hk => (hTa'.mul hTb) hk, ?_⟩` and prove the remaining obligations.

Establish `dA : Ba⁻¹ i i * Ba i i = 1`. Rewrite using `[← TriDiagFrames.diag_mul _ _ hTa' hTa, Matrix.nonsing_inv_mul _ hUa, Matrix.one_apply_eq]`. Establish `dB : Bb⁻¹ i i * Bb i i = 1`. Rewrite using `[← TriDiagFrames.diag_mul _ _ hTb' hTb, Matrix.nonsing_inv_mul _ hUb, Matrix.one_apply_eq]`. Rewrite `t1`, the goal using `[TriDiagFrames.diag_mul _ _ hTa' hTb]`.

Rewrite `t2` using `[TriDiagFrames.diag_mul _ _ hTb' hTa]`. Establish `ha` using `hga i`. Establish `hb` using `hgb i`. Establish `hα : Ba i i ≠ 0` using `right_ne_zero_of_mul_eq_one dA`. Establish `hβ : Bb i i ≠ 0` using `right_ne_zero_of_mul_eq_one dB`.

Rewrite `t1`, the goal using `[eq_inv_of_mul_eq_one_left dA]`. Rewrite `t2` using `[eq_inv_of_mul_eq_one_left dB]`. Rewrite `t1`, `t2` using `[map_mul, map_inv₀]`. Establish `h1 : w (Bb i i) ≤ w (Ba i i)`. Rewrite `t1` using `[inv_mul_le_iff₀ (w.pos hα), mul_one]`. Then use the resulting hypothesis.

Establish `h2 : w (Ba i i) ≤ w (Bb i i)`. Rewrite `t2` using `[inv_mul_le_iff₀ (w.pos hβ), mul_one]`. Then use the resulting hypothesis. Establish `hαβ : w (Ba i i) = w (Bb i i)` using `le_antisymm h2 h1`. Establish `hd : d i ≠ 0`. Introduce `h`.

Rewrite `ha` using `[h, map_zero]`. Conclude with `absurd ha (not_lt.2 (w.nonneg _))`. Establish `hgb0 : gb i ≠ 0`. Introduce `h`. Rewrite `hb` using `[h, mul_zero, zero_sub, AbsoluteValue.map_neg]`.

Conclude with `lt_irrefl _ hb`. Establish `key : (Ba i i)⁻¹ * Bb i i - ga i / gb i = ((Bb i i * gb i - d i) - (Ba i i * ga i - d i)) / (Ba i i * gb i)` using `by field_simp; ring`. Establish `hnum : w ((Bb i i * gb i - d i) - (Ba i i * ga i - d i)) < w (d i)`. Rewrite using `[sub_eq_add_neg]`. Use `(TriDiagFrames.ultra w O hO _ _).trans_lt (max_lt hb ?_)` and prove the remaining obligations.

Rewrite using `[AbsoluteValue.map_neg]`. Conclude with `ha`. Establish `hden : w (Ba i i * gb i) = w (d i)`. Rewrite using `[map_mul, hαβ, ← map_mul]`. Conclude with `TriDiagFrames.eq_of_sub_lt w O hO hb`.

Rewrite using `[key, map_div₀, hden]`. Conclude with `(div_lt_one (w.pos hd)).2 hnum`.
-/
theorem triangular_change_of_frames : ∀ {K : Type} [Field K] (w : AbsoluteValue K ℝ) (O : ValuationSubring K), (∀ x, x ∈ O ↔ w x ≤ 1) →
    ∀ {N : ℕ} (G Ba Bb : Matrix (Fin N) (Fin N) K) (d ga gb : Fin N → K), Ba.BlockTriangular id → Bb.BlockTriangular id →
    (∀ i, w (Ba i i * ga i - d i) < w (d i)) → (∀ i, w (Bb i i * gb i - d i) < w (d i)) →
    (∀ i k, w ((G * Ba) i k) ≤ 1) → (∀ i k, w ((G * Bb) i k) ≤ 1) → w (G * Ba).det = 1 → w (G * Bb).det = 1 →
    ∀ i, (∀ k, k < i → ((G * Ba)⁻¹ * (G * Bb)) i k = 0) ∧ w (((G * Ba)⁻¹ * (G * Bb)) i i - ga i / gb i) < 1 := by
  intro K _ w O hO N G Ba Bb d ga gb hTa hTb hga hgb hEa hEb hDa hDb i
  have hne : ∀ B : Matrix (Fin N) (Fin N) K, w (G * B).det = 1 → IsUnit G.det ∧ IsUnit B.det := by
    intro B hB
    have h0 : (G * B).det ≠ 0 := by
      intro h; rw [h, map_zero] at hB; exact zero_ne_one hB
    rw [Matrix.det_mul] at h0
    exact ⟨isUnit_iff_ne_zero.2 (left_ne_zero_of_mul h0), isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h0)⟩
  obtain ⟨hG, hUa⟩ := hne Ba hDa
  obtain ⟨-, hUb⟩ := hne Bb hDb
  have red : ∀ B C : Matrix (Fin N) (Fin N) K, (G * B)⁻¹ * (G * C) = B⁻¹ * C := by
    intro B C
    rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc G⁻¹, Matrix.nonsing_inv_mul _ hG,
      Matrix.one_mul]
  have triInv : ∀ B : Matrix (Fin N) (Fin N) K, B.BlockTriangular id → IsUnit B.det →
      B⁻¹.BlockTriangular id := by
    intro B hB hU
    haveI := B.invertibleOfIsUnitDet hU
    exact Matrix.blockTriangular_inv_of_blockTriangular hB
  have hTa' := triInv Ba hTa hUa
  have hTb' := triInv Bb hTb hUb
  have memA : ∀ a b, (G * Ba) a b ∈ O := fun a b => (hO _).2 (hEa a b)
  have memB : ∀ a b, (G * Bb) a b ∈ O := fun a b => (hO _).2 (hEb a b)
  have t1 : w ((Ba⁻¹ * Bb) i i) ≤ 1 := by
    rw [← red]
    exact (hO _).1 (TriDiagFrames.mul_entry_mem O _ _ (TriDiagFrames.inv_entry_mem w O hO _ memA hDa) memB i i)
  have t2 : w ((Bb⁻¹ * Ba) i i) ≤ 1 := by
    rw [← red]
    exact (hO _).1 (TriDiagFrames.mul_entry_mem O _ _ (TriDiagFrames.inv_entry_mem w O hO _ memB hDb) memA i i)
  rw [red]
  refine ⟨fun k hk => (hTa'.mul hTb) hk, ?_⟩
  have dA : Ba⁻¹ i i * Ba i i = 1 := by
    rw [← TriDiagFrames.diag_mul _ _ hTa' hTa, Matrix.nonsing_inv_mul _ hUa, Matrix.one_apply_eq]
  have dB : Bb⁻¹ i i * Bb i i = 1 := by
    rw [← TriDiagFrames.diag_mul _ _ hTb' hTb, Matrix.nonsing_inv_mul _ hUb, Matrix.one_apply_eq]
  rw [TriDiagFrames.diag_mul _ _ hTa' hTb] at t1 ⊢
  rw [TriDiagFrames.diag_mul _ _ hTb' hTa] at t2
  have ha := hga i
  have hb := hgb i
  have hα : Ba i i ≠ 0 := right_ne_zero_of_mul_eq_one dA
  have hβ : Bb i i ≠ 0 := right_ne_zero_of_mul_eq_one dB
  rw [eq_inv_of_mul_eq_one_left dA] at t1 ⊢
  rw [eq_inv_of_mul_eq_one_left dB] at t2
  rw [map_mul, map_inv₀] at t1 t2
  have h1 : w (Bb i i) ≤ w (Ba i i) := by
    rwa [inv_mul_le_iff₀ (w.pos hα), mul_one] at t1
  have h2 : w (Ba i i) ≤ w (Bb i i) := by
    rwa [inv_mul_le_iff₀ (w.pos hβ), mul_one] at t2
  have hαβ : w (Ba i i) = w (Bb i i) := le_antisymm h2 h1
  have hd : d i ≠ 0 := by
    intro h; rw [h, map_zero] at ha; exact absurd ha (not_lt.2 (w.nonneg _))
  have hgb0 : gb i ≠ 0 := by
    intro h; rw [h, mul_zero, zero_sub, AbsoluteValue.map_neg] at hb; exact lt_irrefl _ hb
  have key : (Ba i i)⁻¹ * Bb i i - ga i / gb i
      = ((Bb i i * gb i - d i) - (Ba i i * ga i - d i)) / (Ba i i * gb i) := by
    field_simp; ring
  have hnum : w ((Bb i i * gb i - d i) - (Ba i i * ga i - d i)) < w (d i) := by
    rw [sub_eq_add_neg]
    refine (TriDiagFrames.ultra w O hO _ _).trans_lt (max_lt hb ?_)
    rw [AbsoluteValue.map_neg]; exact ha
  have hden : w (Ba i i * gb i) = w (d i) := by
    rw [map_mul, hαβ, ← map_mul]; exact TriDiagFrames.eq_of_sub_lt w O hO hb
  rw [key, map_div₀, hden]
  exact (div_lt_one (w.pos hd)).2 hnum

end GlobalTheory
