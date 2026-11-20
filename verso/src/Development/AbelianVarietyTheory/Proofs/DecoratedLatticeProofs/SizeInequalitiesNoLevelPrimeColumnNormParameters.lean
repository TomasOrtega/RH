import Mathlib
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLeLOfLeCond
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPartitionRowsNumericDatumMemIccStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.SizeRowsRec

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare.SizeRows

/- English proof (translation)
Introduce `D large₂ CY hR u`. Establish `hnu` using `GlobalTheory.T.fockPartitionRows_numericDatum_mem_Icc D large₂ CY hR u`. Take `⟨⟨P⟩, ⟨s2, s3, s4⟩, hg, ⟨s10, -, -, -, s14⟩, ⟨n, hn⟩, -⟩` from `hR`. Establish `hDel : ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del` using `by rw [hn, Nat.floor_natCast]`. Establish `hSc : (numDatumOfParameters D large₂).Sc = large₂.Sc`.

Rewrite using `[large₂.Sc_eq]`. Use `show (D.R.k : ℝ) * (4 * ((⌊D.s.Del⌋₊ : ℕ) : ℝ)) = _`. Rewrite using `[← Rat.cast_natCast, ← Rat.cast_natCast (α := ℝ) ⌊D.s.Del⌋₊, hDel]`. Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Establish `hm : (0 : ℝ) < D.R.m` using `by have := D.R.two_le_m; exact_mod_cast (by omega : 0 < D.R.m)`.

Establish `hn0 : 0 < D.R.n` using `D.R.n_pos'`. Establish `hq` using `D.host.hyp.1.pos`. Establish `hd` using `D.host.hyp.2.1.pos`. Use `⟨⟨?_, ?_, ?_, s4, ?_⟩, fun i => ⟨?_, hg i⟩, trivial, f_mul_N_le_b P s10, hnu, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `s2`.

Use `log_le_L_of_le_cond P hq ?_` and prove the remaining obligations. Unfold `LevelStarExponents.condE`. Conclude with `le_trans (Nat.le_mul_of_pos_left _ D.host.QS_pos) (Nat.le_mul_of_pos_right _ hd)`. Use `log_le_L_of_le_cond P hd ?_` and prove the remaining obligations. Unfold `LevelStarExponents.condE`.

Conclude with `Nat.le_mul_of_pos_left _ (Nat.mul_pos D.host.QS_pos hq)`. Rewrite `s3` using `[large₂.logDerivative_at_one_eq]`. Conclude with `s3`. Take `⟨Y, h1, -, -, h2⟩` from `P.g_Y`. Conclude with `h1.trans (h2 i).1`.

Introduce `z i j`. Use `(large₂.be_close (tauPl D z) i j).trans ?_` and prove the remaining obligations. Use `show large₂.etaSz ≤ (D.R.m : ℝ) * ((⌈LevelStarExponents.h0 large₂⌉₊ : ℕ) : ℝ)`. Establish `h` using `Nat.le_ceil (LevelStarExponents.h0 large₂)`. Combine the equalities or inequalities in the displayed calculation.

Introduce `z i`. Rewrite using `[hSc]`. Take `⟨h1, h2⟩` from `large₂.cloud_v (tauPl D z) i`. Conclude with `⟨by exact_mod_cast h1, h2⟩`. Introduce `z i h1 h2`.

Take `⟨i, hi⟩` from `i`. Take `⟨l, rfl⟩ : ∃ l, i = l + 1` from `⟨i - 1, by simp only at h1; omega⟩`. Establish `hl : l < D.R.k - 2`. Establish `: l + 1 + 1 < D.R.k` using `h2`. Use linear arithmetic over natural numbers and integers.

Establish `e : (numDatumOfParameters D large₂).uW (codeRec large₂ u) z ⟨l + 1, hi⟩ = (D.hcW u (tauPl D z)).u ⟨l + 1, hi⟩`. Rewrite using `[D.s.u_letter u (tauPl D z) l hl, D.hcW_v]`. Unfold `NumDatum.uW`. Rewrite using `[dif_pos ⟨h1, h2⟩]`. Use `show _ - _ - (if D.s.letter u ⟨l, hl⟩ = true then ((⌊D.s.Del⌋₊ : ℕ) : ℚ) else 0) = _`.

Rewrite using `[hDel]`. Both sides reduce to the same expression. Rewrite using `[hSc, e]`. Take `⟨a1, a2⟩` from `large₂.cloud_u u (tauPl D z) ⟨l + 1, hi⟩ h1 h2`. Conclude with `⟨by exact_mod_cast a1, a2⟩`.

Introduce `t ht`. Establish `h` using `(large₂.top_u (tauPl D (false, t)) ⟨t, ht⟩ (by omega) (eTau_tauPl (false, t))).2`. Establish `e : (((numDatumOfParameters D large₂).bT t : ℚ) : ℝ) = (large₂.bT ⟨t, ht⟩ : ℝ)`. Unfold `NumDatum.bT`. Use `push_cast`.

Use `erw [h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `⟨large₂.bT_ge _, s14 _⟩`. Introduce `z hz hk2`.

Establish `hz'` using `not_top_of z hz`. Rewrite using `[hSc]`. Use `⟨P.uk_extreme _ hk2 hz', (large₂.cloud_gap _ (by omega) hz').1, ?_⟩` and prove the remaining obligations. Establish `h1` using `P.cloud_place_bound _ (by omega) hz'`. Establish `h2` using `(large₂.cloud_v (tauPl D z) ⟨0, by omega⟩).2`.

Move the coercions through the operations in `at h1`. Use `show (((D.hc (tauPl D z)).u ⟨0, by omega⟩ : ℚ) : ℝ) ≤ _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sizeRowsS_numRec : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word),
    SizeRowsS CY (numDatumOfParameters D L) (codeRec L u) := by
  intro D large₂ CY hR u
  have hnu := GlobalTheory.T.fockPartitionRows_numericDatum_mem_Icc D large₂ CY hR u
  obtain ⟨⟨P⟩, ⟨s2, s3, s4⟩, hg, ⟨s10, -, -, -, s14⟩, ⟨n, hn⟩, -⟩ := hR
  have hDel : ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del := by rw [hn, Nat.floor_natCast]
  have hSc : (numDatumOfParameters D large₂).Sc = large₂.Sc := by
    rw [large₂.Sc_eq]
    show (D.R.k : ℝ) * (4 * ((⌊D.s.Del⌋₊ : ℕ) : ℝ)) = _
    rw [← Rat.cast_natCast, ← Rat.cast_natCast (α := ℝ) ⌊D.s.Del⌋₊, hDel]
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hm : (0 : ℝ) < D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 0 < D.R.m)
  have hn0 : 0 < D.R.n := D.R.n_pos'
  have hq := D.host.hyp.1.pos
  have hd := D.host.hyp.2.1.pos
  refine ⟨⟨?_, ?_, ?_, s4, ?_⟩, fun i => ⟨?_, hg i⟩, trivial, f_mul_N_le_b P s10, hnu, ?_, ?_, ?_, ?_, ?_⟩
  · exact s2
  · refine log_le_L_of_le_cond P hq ?_
    unfold LevelStarExponents.condE
    exact le_trans (Nat.le_mul_of_pos_left _ D.host.QS_pos) (Nat.le_mul_of_pos_right _ hd)
  · refine log_le_L_of_le_cond P hd ?_
    unfold LevelStarExponents.condE
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos D.host.QS_pos hq)
  · rw [large₂.logDerivative_at_one_eq] at s3
    exact s3
  · obtain ⟨Y, h1, -, -, h2⟩ := P.g_Y
    exact h1.trans (h2 i).1
  · intro z i j
    refine (large₂.be_close (tauPl D z) i j).trans ?_
    show large₂.etaSz ≤ (D.R.m : ℝ) * ((⌈LevelStarExponents.h0 large₂⌉₊ : ℕ) : ℝ)
    have h := Nat.le_ceil (LevelStarExponents.h0 large₂)
    calc large₂.etaSz = (D.R.m : ℝ) * LevelStarExponents.h0 large₂ := by unfold LevelStarExponents.h0; field_simp
      _ ≤ _ := by gcongr
  · intro z i
    rw [hSc]
    obtain ⟨h1, h2⟩ := large₂.cloud_v (tauPl D z) i
    exact ⟨by exact_mod_cast h1, h2⟩
  · intro z i h1 h2
    obtain ⟨i, hi⟩ := i
    obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by simp only at h1; omega⟩
    have hl : l < D.R.k - 2 := by
      have : l + 1 + 1 < D.R.k := h2
      omega
    have e : (numDatumOfParameters D large₂).uW (codeRec large₂ u) z ⟨l + 1, hi⟩ = (D.hcW u (tauPl D z)).u ⟨l + 1, hi⟩ := by
      rw [D.s.u_letter u (tauPl D z) l hl, D.hcW_v]
      unfold NumDatum.uW
      rw [dif_pos ⟨h1, h2⟩]
      show _ - _ - (if D.s.letter u ⟨l, hl⟩ = true then ((⌊D.s.Del⌋₊ : ℕ) : ℚ) else 0) = _
      rw [hDel]
      rfl
    rw [hSc, e]
    obtain ⟨a1, a2⟩ := large₂.cloud_u u (tauPl D z) ⟨l + 1, hi⟩ h1 h2
    exact ⟨by exact_mod_cast a1, a2⟩
  · intro t ht
    have h := (large₂.top_u (tauPl D (false, t)) ⟨t, ht⟩ (by omega) (eTau_tauPl (false, t))).2
    have e : (((numDatumOfParameters D large₂).bT t : ℚ) : ℝ) = (large₂.bT ⟨t, ht⟩ : ℝ) := by
      unfold NumDatum.bT
      push_cast
      erw [h]
      ring
    rw [e]
    exact ⟨large₂.bT_ge _, s14 _⟩
  · intro z hz hk2
    have hz' := not_top_of z hz
    rw [hSc]
    refine ⟨P.uk_extreme _ hk2 hz', (large₂.cloud_gap _ (by omega) hz').1, ?_⟩
    have h1 := P.cloud_place_bound _ (by omega) hz'
    have h2 := (large₂.cloud_v (tauPl D z) ⟨0, by omega⟩).2
    push_cast at h1
    show (((D.hc (tauPl D z)).u ⟨0, by omega⟩ : ℚ) : ℝ) ≤ _
    linarith

end GlobalTheory.CoreHt.SizeRowsRec
