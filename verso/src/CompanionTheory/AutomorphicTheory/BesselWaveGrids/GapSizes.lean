import Formalism.HermitianCurvature.BesselNonvanishingReduction

noncomputable section

namespace CompanionTheory.WaveGrid.GapSizes

/- English proof (translation)
Establish `hN1 : (1 : ℝ) ≤ N` using `by linarith`. Establish `hN3 : (0 : ℝ) ≤ N ^ 3` using `by positivity`. Establish `hm2' : (4 : ℝ) ≤ m ^ 2` using `by nlinarith`. Establish `hm4e : m ^ 4 = m ^ 2 * m ^ 2` using `by ring`. Establish `hm4 : (16 : ℝ) ≤ m ^ 4` using `by rw [hm4e]; nlinarith`.

Establish `hm4' : 4 * m ^ 2 ≤ m ^ 4` using `by rw [hm4e]; nlinarith`. Establish `hCg0 : (0 : ℝ) ≤ Cg` using `by linarith`. Prove the components needed by the constructor for the conclusion. Establish `a : (16 : ℝ) ≤ m ^ 4 * s` using `le_trans hm4 (le_mul_of_one_le_right (by positivity) hs)`. Establish `b : (16000 : ℝ) ≤ Cg * (m ^ 4 * s)` using `by nlinarith`.

Establish `c : 16000 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P` using `le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b : 4000 * m ^ 2 ≤ Cg * m ^ 4` using `by nlinarith`. Establish `c : 4000 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P` using `le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sizes (Cg m N P s : ℝ) (hCg : 1000 ≤ Cg) (hm2 : 2 ≤ m) (hmN : m ≤ N) (hPN : N ^ 3 ≤ P) (hs : 1 ≤ s) :
    120 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P / 4 ∧ 125 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P / 32 := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN3 : (0 : ℝ) ≤ N ^ 3 := by positivity
  have hm2' : (4 : ℝ) ≤ m ^ 2 := by nlinarith
  have hm4e : m ^ 4 = m ^ 2 * m ^ 2 := by ring
  have hm4 : (16 : ℝ) ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hm4' : 4 * m ^ 2 ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hCg0 : (0 : ℝ) ≤ Cg := by linarith
  constructor
  · have a : (16 : ℝ) ≤ m ^ 4 * s := le_trans hm4 (le_mul_of_one_le_right (by positivity) hs)
    have b : (16000 : ℝ) ≤ Cg * (m ^ 4 * s) := by nlinarith
    have c : 16000 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith
  · have b : 4000 * m ^ 2 ≤ Cg * m ^ 4 := by nlinarith
    have c : 4000 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith

/- English proof (translation)
Establish `hr0 : (0 : ℝ) ≤ r` using `Nat.cast_nonneg _`. Establish `hk1 : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Use `set N : ℝ := 2 * (r : ℝ) + k + 1 with hN`. Establish `hN1 : (1 : ℝ) ≤ N` using `by linarith`. Establish `hN2 : N ^ 2 ≤ N ^ 3` using `by nlinarith`.

Establish `hdN : Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ 2 * N ^ 2` using `by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; rw [hN]; nlinarith`. Establish `hdN0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.dN k r` using `by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; nlinarith`. Establish `hnk : ((2 * r + k : ℕ) : ℝ) ≤ N` using `by rw [hN]; push_cast; linarith`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `Formalism.FourierDecayAlt.ThreeDimData.Mexp`.

Use the polynomial consequences of the given equalities and inequalities. Unfold `Formalism.FourierDecayAlt.ThreeDimData.Mexp`. Check the signs of the components of the expression. Unfold `Formalism.FourierDecayAlt.ThreeDimData.AS`. Establish `: ((2 * r + k : ℕ) : ℝ) * Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ N * (2 * N ^ 2)` using `mul_le_mul hnk hdN hdN0 (by linarith)`.

Use the polynomial consequences of the given equalities and inequalities. Unfold `Formalism.FourierDecayAlt.ThreeDimData.AS`. Check the signs of the components of the expression. Unfold `Formalism.FourierDecayAlt.ThreeDimData.AG`. Establish `e1 : ((k : ℝ) + r) ≤ N` using `by rw [hN]; linarith`.

Establish `e2 : ((r : ℝ) + 1) ≤ N` using `by rw [hN]; linarith`. Establish `e3 : ((k : ℝ) + r) * ((r : ℝ) + 1) ≤ N * N` using `mul_le_mul e1 e2 (by linarith) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Unfold `Formalism.FourierDecayAlt.ThreeDimData.AG`. Check the signs of the components of the expression.
-/
theorem consts (k r : ℕ) (hk : 1 ≤ k) :
    Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ (2 * (r : ℝ) + 2) ^ 2 / 2 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set N : ℝ := 2 * (r : ℝ) + k + 1 with hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN2 : N ^ 2 ≤ N ^ 3 := by nlinarith
  have hdN : Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ 2 * N ^ 2 := by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; rw [hN]; nlinarith
  have hdN0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.dN k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; nlinarith
  have hnk : ((2 * r + k : ℕ) : ℝ) ≤ N := by rw [hN]; push_cast; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; positivity
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AS
    have : ((2 * r + k : ℕ) : ℝ) * Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ N * (2 * N ^ 2) :=
      mul_le_mul hnk hdN hdN0 (by linarith)
    nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AS; positivity
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    have e1 : ((k : ℝ) + r) ≤ N := by rw [hN]; linarith
    have e2 : ((r : ℝ) + 1) ≤ N := by rw [hN]; linarith
    have e3 : ((k : ℝ) + r) * ((r : ℝ) + 1) ≤ N * N := mul_le_mul e1 e2 (by linarith) (by linarith)
    nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity

/- English proof (translation)
Establish `hr0 : (0 : ℝ) ≤ r` using `Nat.cast_nonneg _`. Establish `hk1 : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `em : ((2 * r + 2 : ℕ) : ℝ) = 2 * (r : ℝ) + 2` using `by push_cast; ring`. Establish `eN : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1` using `by push_cast; ring`. Establish `e3 : ((3 * (r + 1) : ℕ) : ℝ) = 3 * ((r : ℝ) + 1)` using `by push_cast; ring`.

Unfold `Formalism.FourierDecayAlt.ThreeDimData.GapOK`. Rewrite using `[em, eN, e3]`. Generalize the expression as in `hm : 2 * (r : ℝ) + 2 = m`. Generalize the expression as in `hN : 2 * (r : ℝ) + k + 1 = N`. Establish `hm2 : (2 : ℝ) ≤ m` using `by rw [← hm]; linarith`.

Establish `hmN : m ≤ N` using `by rw [← hm, ← hN]; linarith`. Establish `hmpos : (0 : ℝ) < m` using `by linarith`. Establish `hN1 : (1 : ℝ) ≤ N` using `by linarith`. Establish `hsq : Real.sqrt (2 * ((r : ℝ) + 1)) = Real.sqrt m` using `by rw [← hm]; ring_nf`. Establish `h92 : m ^ ((9 : ℝ) / 2) = m ^ 4 * Real.sqrt m`.

Rewrite using `[show (9 : ℝ) / 2 = ((4 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add hmpos, Real.rpow_natCast, Real.sqrt_eq_rpow]`. Establish `hs1 : (1 : ℝ) ≤ Real.sqrt m`. Rewrite using `[show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)`. Establish `hspos : (0 : ℝ) < Real.sqrt m` using `by linarith`. Establish `hN3 : (1 : ℝ) ≤ N ^ 3` using `one_le_pow₀ hN1`.

Establish `hPN : N ^ 3 ≤ 3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3`. Establish `: (0 : ℝ) ≤ 3 * ((r : ℝ) + 1) * N ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨s1, s2⟩` from `sizes Cg m N (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) (Real.sqrt m) hCg hm2 hmN hPN hs1`. Establish `hA : Formalism.FourierDecayAlt.ThreeDimData.aOf r (Cg * m ^ ((9 : ℝ) / 2) * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 4) = Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32`.

Unfold `Formalism.FourierDecayAlt.ThreeDimData.aOf`. Rewrite using `[hsq, h92]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨cM, cM0, cS, cS0, cG, cG0⟩` from `consts k r hk`.

Rewrite `cM` using `[hm]`. Rewrite `cS`, `cG` using `[hN]`. Establish `hm2' : (4 : ℝ) ≤ m ^ 2` using `by nlinarith`. Establish `hN3' : (0 : ℝ) ≤ N ^ 3` using `by positivity`. Establish `hmm : m ^ 2 * N ^ 3 ≥ 4 * N ^ 3` using `by nlinarith`.

Establish `hX : 4 * N ^ 3 ≤ m ^ 2 * N ^ 3` using `by nlinarith`. Establish `hX1 : (4 : ℝ) ≤ m ^ 2 * N ^ 3` using `by linarith`. Use `⟨hk, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h92]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hA]`. Establish `hsum : Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 6 * N ^ 3` using `by linarith`. Establish `hL : 2 * Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤ 2 * (m ^ 2 / 2) * (6 * N ^ 3)` using `mul_le_mul (by linarith) hsum (by positivity) (by positivity)`. Establish `hL' : 2 * (m ^ 2 / 2) * (6 * N ^ 3) = 6 * (m ^ 2 * N ^ 3)` using `by ring`. Establish `s2' : 125 * (m ^ 2 * N ^ 3) ≤ Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32`.

Establish `: 125 * m ^ 2 * N ^ 3 = 125 * (m ^ 2 * N ^ 3)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear relations using `only [hL, hL', s2', cG, hX, hX1]`. Rewrite using `[hA]`. Establish `hN23 : N ^ 2 ≤ N ^ 3`.

Establish `: N ^ 3 = N ^ 2 * N` using `by ring`. Rewrite using `[this]; exact le_mul_of_one_le_right (by positivity) hN1`. Establish `h9 : 9 * ((r : ℝ) + 1) = 4.5 * m` using `by rw [← hm]; ring`. Establish `e1 : 9 * ((r : ℝ) + 1) * N ^ 2 ≤ 4.5 * m * N ^ 3`. Rewrite using `[h9]; exact mul_le_mul_of_nonneg_left hN23 (by positivity)`.

Establish `hq : 4.5 * m ≤ 3 * m ^ 2` using `by nlinarith only [hm2]`. Establish `e2 : 4.5 * m * N ^ 3 ≤ 3 * (m ^ 2 * N ^ 3)`. Use `mul_le_mul_of_nonneg_right hq hN3'` as an intermediate fact. Combine the linear relations using `only [this]`. Establish `s2' : 125 * (m ^ 2 * N ^ 3) ≤ Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32`.

Establish `: 125 * m ^ 2 * N ^ 3 = 125 * (m ^ 2 * N ^ 3)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear relations using `only [e1, e2, hX, hX1, s2', cG]`.
-/
theorem gapOK_of (k r : ℕ) (hk : 1 ≤ k) (Cg : ℝ) (hCg : 1000 ≤ Cg) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 4) := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have em : ((2 * r + 2 : ℕ) : ℝ) = 2 * (r : ℝ) + 2 := by push_cast; ring
  have eN : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  have e3 : ((3 * (r + 1) : ℕ) : ℝ) = 3 * ((r : ℝ) + 1) := by push_cast; ring
  unfold Formalism.FourierDecayAlt.ThreeDimData.GapOK
  rw [em, eN, e3]
  generalize hm : 2 * (r : ℝ) + 2 = m
  generalize hN : 2 * (r : ℝ) + k + 1 = N
  have hm2 : (2 : ℝ) ≤ m := by rw [← hm]; linarith
  have hmN : m ≤ N := by rw [← hm, ← hN]; linarith
  have hmpos : (0 : ℝ) < m := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hsq : Real.sqrt (2 * ((r : ℝ) + 1)) = Real.sqrt m := by rw [← hm]; ring_nf
  have h92 : m ^ ((9 : ℝ) / 2) = m ^ 4 * Real.sqrt m := by
    rw [show (9 : ℝ) / 2 = ((4 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add hmpos, Real.rpow_natCast,
      Real.sqrt_eq_rpow]
  have hs1 : (1 : ℝ) ≤ Real.sqrt m := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hspos : (0 : ℝ) < Real.sqrt m := by linarith
  have hN3 : (1 : ℝ) ≤ N ^ 3 := one_le_pow₀ hN1
  have hPN : N ^ 3 ≤ 3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3 := by
    have : (0 : ℝ) ≤ 3 * ((r : ℝ) + 1) * N ^ 2 := by positivity
    linarith
  obtain ⟨s1, s2⟩ := sizes Cg m N (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) (Real.sqrt m) hCg hm2 hmN hPN hs1
  have hA : Formalism.FourierDecayAlt.ThreeDimData.aOf r (Cg * m ^ ((9 : ℝ) / 2) * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 4) =
      Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.aOf
    rw [hsq, h92]
    field_simp
    ring
  obtain ⟨cM, cM0, cS, cS0, cG, cG0⟩ := consts k r hk
  rw [hm] at cM
  rw [hN] at cS cG
  have hm2' : (4 : ℝ) ≤ m ^ 2 := by nlinarith
  have hN3' : (0 : ℝ) ≤ N ^ 3 := by positivity
  have hmm : m ^ 2 * N ^ 3 ≥ 4 * N ^ 3 := by nlinarith
  have hX : 4 * N ^ 3 ≤ m ^ 2 * N ^ 3 := by nlinarith
  have hX1 : (4 : ℝ) ≤ m ^ 2 * N ^ 3 := by linarith
  refine ⟨hk, ?_, ?_, ?_⟩
  · rw [h92]; linarith
  · rw [hA]
    have hsum : Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 6 * N ^ 3 := by linarith
    have hL : 2 * Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤ 2 * (m ^ 2 / 2) * (6 * N ^ 3) :=
      mul_le_mul (by linarith) hsum (by positivity) (by positivity)
    have hL' : 2 * (m ^ 2 / 2) * (6 * N ^ 3) = 6 * (m ^ 2 * N ^ 3) := by ring
    have s2' : 125 * (m ^ 2 * N ^ 3) ≤ Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32 := by
      have : 125 * m ^ 2 * N ^ 3 = 125 * (m ^ 2 * N ^ 3) := by ring
      linarith
    linarith only [hL, hL', s2', cG, hX, hX1]
  · rw [hA]
    have hN23 : N ^ 2 ≤ N ^ 3 := by
      have : N ^ 3 = N ^ 2 * N := by ring
      rw [this]; exact le_mul_of_one_le_right (by positivity) hN1
    have h9 : 9 * ((r : ℝ) + 1) = 4.5 * m := by rw [← hm]; ring
    have e1 : 9 * ((r : ℝ) + 1) * N ^ 2 ≤ 4.5 * m * N ^ 3 := by
      rw [h9]; exact mul_le_mul_of_nonneg_left hN23 (by positivity)
    have hq : 4.5 * m ≤ 3 * m ^ 2 := by nlinarith only [hm2]
    have e2 : 4.5 * m * N ^ 3 ≤ 3 * (m ^ 2 * N ^ 3) := by
      have := mul_le_mul_of_nonneg_right hq hN3'
      linarith only [this]
    have s2' : 125 * (m ^ 2 * N ^ 3) ≤ Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32 := by
      have : 125 * m ^ 2 * N ^ 3 = 125 * (m ^ 2 * N ^ 3) := by ring
      linarith
    linarith only [e1, e2, hX, hX1, s2', cG]

end CompanionTheory.WaveGrid.GapSizes
