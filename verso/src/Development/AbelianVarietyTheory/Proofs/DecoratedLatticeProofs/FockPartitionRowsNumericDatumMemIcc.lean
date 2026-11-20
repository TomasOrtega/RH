import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.RowsRangeS

variable {D : D7}

variable {D : D7}

/- English proof (translation)
The claim follows from `Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`.
-/
theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

/- English proof (translation)
The claim follows from `Real.one_le_exp (by linarith [one_le_scL L])`.
-/
theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (by linarith [one_le_scL L])

/- English proof (translation)
Use `L.sc.one_lt_alt` as an intermediate fact. Use `one_le_b L` as an intermediate fact. Unfold `Scale.b' Scale.a Scale.X'`. Check the signs of the components of the expression.
-/
theorem b'_pos (L : SizeData₂ D) : 0 < L.sc.b' := by
  have := L.sc.one_lt_alt
  have := one_le_b L
  unfold Scale.b' Scale.a Scale.X'
  positivity

/- English proof (translation)
Establish `: 1 ≤ D.R.n` using `by unfold Ranks.n; exact Nat.succ_le_of_lt (by positivity)`. Conclude with `this` after adjusting the coercions.
-/
theorem one_le_n (D : D7) : (1 : ℝ) ≤ D.R.n := by
  have : 1 ≤ D.R.n := by unfold Ranks.n; exact Nat.succ_le_of_lt (by positivity)
  exact_mod_cast this

/- English proof (translation)
Unfold `Host.topPlaces at h`. Take `⟨t, ht, hte⟩` from `Finset.mem_image.1 h`. Conclude with `⟨⟨t, ht⟩, hte.symm⟩`.
-/
theorem exists_top {τ : D.what₂.Tau} (h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces) :
    ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t := by
  unfold Host.topPlaces at h
  obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 h
  exact ⟨⟨t, ht⟩, hte.symm⟩

/- English proof (translation)
Take `⟨n, hn⟩` from `hD`. Take `⟨r, hr⟩` from `i`. Unfold `NumDatum.uW`. Use `split_ifs with h h1`. Take `⟨l, rfl⟩ : ∃ l, r = l + 1` from `⟨r - 1, by have := h.1; simp only at this; omega⟩`.

Establish `h' : l < D.R.k - 2` using `by have := h.2; simp only at this; omega`. Establish `a` using `D.s.u_letter u (tauPl D z) l h'`. Establish `h2 : D.s.letter u ⟨l, h'⟩ = true` using `h1`. Rewrite `a` using `[if_pos h2, D.hcW_v]`. Establish `h3 : (((numDatumOfParameters D large₂).Del : ℕ) : ℚ) = D.s.Del` using `by show ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del`.

Rewrite using `[hn, Nat.floor_natCast]`. Rewrite using `[a, h3]`. Both sides reduce to the same expression. Take `⟨l, rfl⟩ : ∃ l, r = l + 1` from `⟨r - 1, by have := h.1; simp only at this; omega⟩`. Establish `h' : l < D.R.k - 2` using `by have := h.2; simp only at this; omega`.

Establish `a` using `D.s.u_letter u (tauPl D z) l h'`. Establish `h2 : ¬ D.s.letter u ⟨l, h'⟩ = true` using `h1`. Rewrite `a` using `[if_neg h2, D.hcW_v]`. Rewrite using `[a]`. Both sides reduce to the same expression.

Distinguish the cases in `h0 : r = 0`. Substitute `h0` using the available equality. Conclude with `(D.hcW_first u _ hr).symm`. Take `rfl : r = D.R.k - 1` from `by simp only at h; omega`. Conclude with `(D.hcW_last u _ (by omega)).symm`.
-/
theorem uW_numRec (large₂ : SizeData₂ D) (hD : ∃ n : ℕ, D.s.Del = n) (u : D.what₂.Word) (z : RPl D.R) (i : Fin D.R.k) :
    (numDatumOfParameters D large₂).uW (codeRec large₂ u) z i = (D.hcW u (tauPl D z)).u i := by
  obtain ⟨n, hn⟩ := hD
  obtain ⟨r, hr⟩ := i
  unfold NumDatum.uW
  split_ifs with h h1
  · obtain ⟨l, rfl⟩ : ∃ l, r = l + 1 := ⟨r - 1, by have := h.1; simp only at this; omega⟩
    have h' : l < D.R.k - 2 := by have := h.2; simp only at this; omega
    have a := D.s.u_letter u (tauPl D z) l h'
    have h2 : D.s.letter u ⟨l, h'⟩ = true := h1
    rw [if_pos h2, D.hcW_v] at a
    have h3 : (((numDatumOfParameters D large₂).Del : ℕ) : ℚ) = D.s.Del := by
      show ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del
      rw [hn, Nat.floor_natCast]
    rw [a, h3]
    rfl
  · obtain ⟨l, rfl⟩ : ∃ l, r = l + 1 := ⟨r - 1, by have := h.1; simp only at this; omega⟩
    have h' : l < D.R.k - 2 := by have := h.2; simp only at this; omega
    have a := D.s.u_letter u (tauPl D z) l h'
    have h2 : ¬ D.s.letter u ⟨l, h'⟩ = true := h1
    rw [if_neg h2, D.hcW_v] at a
    rw [a]
    rfl
  · by_cases h0 : r = 0
    · subst h0
      exact (D.hcW_first u _ hr).symm
    · obtain rfl : r = D.R.k - 1 := by simp only at h; omega
      exact (D.hcW_last u _ (by omega)).symm

/- English proof (translation)
Establish `e1 : (numDatumOfParameters D large₂).srcPar (codeRec large₂ u) z i = DV.srcPar D u (tauPl D z) i`. Unfold `NumDatum.srcPar DV.srcPar`. Distinguish the cases in `h : i < D.R.k`. Rewrite using `[dif_pos h, dif_pos h]`. Conclude with `uW_numRec large₂ hD u z ⟨i, h⟩`.

Rewrite using `[dif_neg h, dif_neg h, D.hcW_e]`. Establish `e2 : (((numDatumOfParameters D large₂).eQ j z : ℚ) : ℝ) = DV.wSz D j (tauPl D z)`. Unfold `NumDatum.eQ DV.wSz`. Distinguish the cases in `h : 1 ≤ j ∧ j ≤ D.R.m`. Rewrite using `[dif_pos h, dif_pos h]`.

Rewrite using `[dif_neg h, dif_neg h, Rat.cast_zero]`. Unfold `NumDatum.nu DV.nuRow`. Rewrite using `[e1, ← e2]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem nu_numRec (large₂ : SizeData₂ D) (hD : ∃ n : ℕ, D.s.Del = n) (u : D.what₂.Word) (j : ℕ) (z : RPl D.R) (i : ℕ) :
    (((numDatumOfParameters D large₂).nu (codeRec large₂ u) j z i : ℚ) : ℝ) = DV.nuRow D u j (tauPl D z) i := by
  have e1 : (numDatumOfParameters D large₂).srcPar (codeRec large₂ u) z i = DV.srcPar D u (tauPl D z) i := by
    unfold NumDatum.srcPar DV.srcPar
    by_cases h : i < D.R.k
    · rw [dif_pos h, dif_pos h]
      exact uW_numRec large₂ hD u z ⟨i, h⟩
    · rw [dif_neg h, dif_neg h, D.hcW_e]
  have e2 : (((numDatumOfParameters D large₂).eQ j z : ℚ) : ℝ) = DV.wSz D j (tauPl D z) := by
    unfold NumDatum.eQ DV.wSz
    by_cases h : 1 ≤ j ∧ j ≤ D.R.m
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h, Rat.cast_zero]
  unfold NumDatum.nu DV.nuRow
  rw [e1, ← e2]
  push_cast
  rfl

/- English proof (translation)
Establish `hm` using `D.R.two_le_m`. Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `hk0 : 0 < D.R.k` using `by omega`. Establish `hk' : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast hk`. Establish `hm' : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm`.

Establish `ht : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`. Establish `hkN : (D.R.k : ℝ) ≤ D.R.N i`. Establish `: D.R.k ≤ D.R.N i` using `by unfold Ranks.N; omega`. Conclude with `this` after adjusting the coercions. Establish `hx` using `large₂.sc.one_lt_alt`.

Establish `hb1` using `one_le_b large₂`. Establish `hb'` using `b'_pos large₂`. Establish `hba : large₂.sc.b ≤ large₂.sc.a` using `le_mul_of_one_le_left (by linarith) hx.le`. Establish `hX : 2 ≤ large₂.sc.X'`. Establish `h1 : 1 ≤ large₂.sc.x ^ (large₂.sc.eps / 3)` using `Real.one_le_rpow hx.le (by linarith [large₂.sc.eps_pos])`.

Establish `h2` using `Real.add_one_le_exp (large₂.sc.x ^ (large₂.sc.eps / 3))`. Unfold `Scale.X'`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb'a : large₂.sc.b' ≤ large₂.sc.a / 2` using `div_le_div_of_nonneg_left (by linarith) (by norm_num) hX`. Establish `hw : large₂.sc.w'' D.R.n ≤ large₂.sc.b'` using `div_le_self hb'.le (one_le_mul_of_one_le_of_one_le hx.le (one_le_n D))`.

Establish `he` using `large₂.etaSz_pos`. Establish `hS` using `large₂.Sc_pos`. Establish `heta : 2 * large₂.etaSz ≤ large₂.sc.b'`. Establish `h1 : (2 : ℝ) ≤ D.R.m * ((D.R.t : ℝ) + 1)` using `by nlinarith`. Combine the linear relations using `[P.mteta, mul_le_mul_of_nonneg_right h1 he.le]`.

Establish `hSc : 5 * large₂.Sc ≤ large₂.sc.b'`. Combine the linear relations using `[P.kS_le, mul_le_mul_of_nonneg_right hk' hS.le]`. Establish `hwj : wj D (i + 1) τ = (((D.hc τ).e ⟨i, hi⟩ : ℚ) : ℝ)`. Unfold `wj`. Rewrite using `[dif_pos (by simpa using hi)]`.

Both sides reduce to the same expression. Rewrite using `[RowWeightLemmas.nuRow_head D u i hi τ 0 hk0, D.hcW_first u τ hk0, D.hcW_e]`. Use `push_cast`. Rewrite using `[← hwj]`. Distinguish the cases in `ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces`.

Take `⟨t, htt⟩` from `exists_top ha`. Rewrite using `[(large₂.top_u τ t hk0 htt).1]`. Establish `a1` using `(large₂.win_top (i + 1) (by omega) hi τ t htt).2`. Establish `a2` using `(large₂.aT_win t).2`. Establish `a3 : (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2)` using `hk'.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hx.le (by unfold Scale.A; norm_num)))`.

Establish `a4 : large₂.sc.a / ((D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2)) ≤ large₂.sc.a / 5` using `div_le_div_of_nonneg_left (by linarith) (by norm_num) a3`. Establish `a5 : large₂.sc.b' / large₂.sc.x ≤ large₂.sc.b'` using `div_le_self hb'.le hx.le`. Combine the linear relations using `[hb t]`. Establish `h1` using `P.cloud_place_bound τ (by omega) ha`. Establish `h2` using `(large₂.cloud_v τ ⟨0, by omega⟩).2`.

Move the coercions through the operations in `at h1`. Distinguish the cases in `hc : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces`. Establish `a1` using `hT (i + 1) (by omega) hi τ hc`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `a1` using `(large₂.win_thin (i + 1) (by omega) hi τ ⟨(D.eTau τ).2, ha, hc⟩).2`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nuRow_zero_le_three_mul (large₂ : SizeData₂ D) (P : ParameterChoice' D large₂) (hb : ∀ t, (large₂.bT t : ℝ) ≤ 2 * large₂.sc.b')
    (hT : ThickUp large₂) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    DV.nuRow D u (i + 1) τ 0 ≤ 3 * large₂.sc.a := by
  have hm := D.R.two_le_m
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk0 : 0 < D.R.k := by omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hkN : (D.R.k : ℝ) ≤ D.R.N i := by
    have : D.R.k ≤ D.R.N i := by unfold Ranks.N; omega
    exact_mod_cast this
  have hx := large₂.sc.one_lt_alt
  have hb1 := one_le_b large₂
  have hb' := b'_pos large₂
  have hba : large₂.sc.b ≤ large₂.sc.a := le_mul_of_one_le_left (by linarith) hx.le
  have hX : 2 ≤ large₂.sc.X' := by
    have h1 : 1 ≤ large₂.sc.x ^ (large₂.sc.eps / 3) := Real.one_le_rpow hx.le (by linarith [large₂.sc.eps_pos])
    have h2 := Real.add_one_le_exp (large₂.sc.x ^ (large₂.sc.eps / 3))
    unfold Scale.X'
    linarith
  have hb'a : large₂.sc.b' ≤ large₂.sc.a / 2 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hX
  have hw : large₂.sc.w'' D.R.n ≤ large₂.sc.b' :=
    div_le_self hb'.le (one_le_mul_of_one_le_of_one_le hx.le (one_le_n D))
  have he := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have heta : 2 * large₂.etaSz ≤ large₂.sc.b' := by
    have h1 : (2 : ℝ) ≤ D.R.m * ((D.R.t : ℝ) + 1) := by nlinarith
    linarith [P.mteta, mul_le_mul_of_nonneg_right h1 he.le]
  have hSc : 5 * large₂.Sc ≤ large₂.sc.b' := by
    linarith [P.kS_le, mul_le_mul_of_nonneg_right hk' hS.le]
  have hwj : wj D (i + 1) τ = (((D.hc τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dif_pos (by simpa using hi)]
    rfl
  rw [RowWeightLemmas.nuRow_head D u i hi τ 0 hk0, D.hcW_first u τ hk0, D.hcW_e]
  push_cast
  rw [← hwj]
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, htt⟩ := exists_top ha
    rw [(large₂.top_u τ t hk0 htt).1]
    have a1 := (large₂.win_top (i + 1) (by omega) hi τ t htt).2
    have a2 := (large₂.aT_win t).2
    have a3 : (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2) :=
      hk'.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hx.le (by unfold Scale.A; norm_num)))
    have a4 : large₂.sc.a / ((D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2)) ≤ large₂.sc.a / 5 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) a3
    have a5 : large₂.sc.b' / large₂.sc.x ≤ large₂.sc.b' := div_le_self hb'.le hx.le
    linarith [hb t]
  · have h1 := P.cloud_place_bound τ (by omega) ha
    have h2 := (large₂.cloud_v τ ⟨0, by omega⟩).2
    push_cast at h1
    by_cases hc : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have a1 := hT (i + 1) (by omega) hi τ hc
      linarith
    · have a1 := (large₂.win_thin (i + 1) (by omega) hi τ ⟨(D.eTau τ).2, ha, hc⟩).2
      linarith

/- English proof (translation)
Introduce and unpack `D large₂ CY ⟨⟨P⟩, -, -, hN, hD, hT⟩ u j hj z r hr`. Take `⟨j1, j2⟩` from `Finset.mem_Icc.1 hj`. Take `⟨i, rfl⟩ : ∃ i, j = i + 1` from `⟨j - 1, by omega⟩`. Establish `hi : i < D.R.m` using `j2`. Establish `hr' : r < D.R.N i` using `hr`.

Establish `e` using `nu_numRec large₂ hD u (i + 1) z r`. Prove the components needed by the constructor for the conclusion. Establish `h` using `(RowWeightLemmas.nuRow_pos D u i hi (tauPl D z) r hr').le`. Rewrite `h` using `[← e]`. Conclude with `h` after adjusting the coercions.

Rewrite using `[e]`. Conclude with `(RowWeightLemmas.nuRow_anti' D u i hi _ r 0 (Nat.zero_le _) hr').trans (nuRow_zero_le_three_mul large₂ P hN.2.2.2.2 hT u i hi _)`.
-/
theorem nu_numRec_mem : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word), ∀ j ∈ (numDatumOfParameters D L).lifts, ∀ z,
    ∀ i < D.R.N (j - 1), 0 ≤ (numDatumOfParameters D L).nu (codeRec L u) j z i ∧
      (((numDatumOfParameters D L).nu (codeRec L u) j z i : ℚ) : ℝ) ≤ 3 * L.sc.a := by
  rintro D large₂ CY ⟨⟨P⟩, -, -, hN, hD, hT⟩ u j hj z r hr
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m := j2
  have hr' : r < D.R.N i := hr
  have e := nu_numRec large₂ hD u (i + 1) z r
  constructor
  · have h := (RowWeightLemmas.nuRow_pos D u i hi (tauPl D z) r hr').le
    rw [← e] at h
    exact_mod_cast h
  · rw [e]
    exact (RowWeightLemmas.nuRow_anti' D u i hi _ r 0 (Nat.zero_le _) hr').trans
      (nuRow_zero_le_three_mul large₂ P hN.2.2.2.2 hT u i hi _)

end GlobalTheory.CoreHt.RowsRangeS
