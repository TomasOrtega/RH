import Formalism.LandauZeroFreeBounds.NoZeroComplexOf

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (authored)
The modulus is a nonzero natural number and is therefore at least one, also when regarded as a real number.
-/
lemma one_le_natCast (q : ℕ) [NeZero q] : (1 : ℝ) ≤ q := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)

/- English proof (authored)
The modulus is at least one and the other factor is at least two. Their product is at least two, so its logarithm is at least log 2.
-/
lemma log_two_le_log_mul_abs_add_two (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq := one_le_natCast q
  apply Real.log_le_log (by norm_num)
  nlinarith [abs_nonneg t]

/- English proof (authored)
The preceding lower bound is log 2, which is strictly positive.
-/
lemma log_mul_abs_add_two_pos (q : ℕ) [NeZero q] (t : ℝ) :
    0 < Real.log ((q : ℝ) * (|t| + 2)) := lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_two_le_log_mul_abs_add_two q t)

/- English proof (authored)
The conductor logarithm is positive. Replacing the region constant by a larger one increases the shift subtracted from one, lowering the real-part threshold. The original region condition implies the new one.
-/
lemma inRegion_mono' {c c' : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (h : c ≤ c') (hs : InRegion c q s) :
    InRegion c' q s := by
  unfold InRegion at *
  have hL := log_mul_abs_add_two_pos q s.im
  have := div_le_div_of_nonneg_right h hL.le
  linarith

/- English proof (authored)
The shift in the real-part threshold is at most one half divided by log 2. Because log 2 exceeds one half, this upper bound is less than one, so the real part is positive.
-/
lemma re_pos_of_inRegion {c : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (hc : c ≤ 1 / 2) (hs : InRegion c q s) :
    0 < s.re := by
  unfold InRegion at hs
  have hL := log_two_le_log_mul_abs_add_two q s.im
  have hLpos := log_mul_abs_add_two_pos q s.im
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := div_le_div_of_nonneg_right hc hLpos.le
  have h2 : (1 / 2 : ℝ) / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ (1 / 2) / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) h2pos hL
  have h3 : (1 / 2 : ℝ) / Real.log 2 < 1 := by
    rw [div_lt_one h2pos]; linarith [Real.log_two_gt_d9]
  linarith

/- English proof (authored)
The modulus is at least one, so the conductor logarithm is at least the height logarithm, and both are positive. Replacing c by the larger positive constant and then dividing by the smaller logarithm can only increase the shift. This gives the weaker lower bound on the real part.
-/
lemma one_sub_div_log_le_re {c cz : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (hcz : 0 < cz) (h : c ≤ cz)
    (hs : InRegion c q s) : 1 - cz / Real.log (|s.im| + 2) ≤ s.re := by
  unfold InRegion at hs
  have hq := one_le_natCast q
  have hT : (2 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hlogT : 0 < Real.log (|s.im| + 2) := Real.log_pos (by linarith)
  have hle : Real.log (|s.im| + 2) ≤ Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hLpos := log_mul_abs_add_two_pos q s.im
  have h1 := div_le_div_of_nonneg_right h hLpos.le
  have h2 := div_le_div_of_nonneg_left hcz.le hlogT hle
  linarith

/- English proof (authored)
Take the minimum of the positive region constants and one half. In this common region the principal character is excluded by its reduction to zeta, using the positive real part and the zeta region. The nonreal-character bound forces any remaining character to be quadratic. The large-height exclusion puts the zero in the small-height range, where it is real and simple. If two different quadratic characters had zeros there, their real zeros would contradict the two-character bound. Thus any second zero is for the same character, and the small-height uniqueness theorem makes it the same zero.
-/
theorem zeroFreeRegionExceptionalZeroOfBounds : ZFRDirichletOf := by
  intro hZ hT hN hL hS h2
  obtain ⟨cz, hcz, hZ⟩ := hZ
  obtain ⟨cN, hcN, hN⟩ := hN
  obtain ⟨δ, cS, hδ, hcS, hS⟩ := hS
  obtain ⟨cL, hcL, hL⟩ := hL δ hδ
  obtain ⟨c2, hc2, h2⟩ := h2
  set c := min (min (min cz cN) (min cL cS)) (min c2 (1 / 2)) with hc
  have hc0 : 0 < c := lt_min (lt_min (lt_min hcz hcN) (lt_min hcL hcS)) (lt_min hc2 (by norm_num))
  have hccz : c ≤ cz := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hccN : c ≤ cN := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hccL : c ≤ cL := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hccS : c ≤ cS := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcc2 : c ≤ c2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc12 : c ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc0, ?_⟩
  intro q _ χ s hs hz

  have key : ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), InRegion c q s → IsLZero χ s →
      χ ^ 2 = 1 ∧ χ ≠ 1 ∧ |s.im| < δ / Real.log ((q : ℝ) * (|s.im| + 2)) := by
    intro χ s hs hz
    obtain ⟨hne, h0⟩ := hz
    have hχ1 : χ ≠ 1 := by
      rintro rfl
      have hs1 : s ≠ 1 := hne.resolve_left (fun h => h rfl)
      have hre := re_pos_of_inRegion hc12 hs
      exact hZ s hs1 (one_sub_div_log_le_re hcz hccz hs) (hT q s hre hs1 h0)
    have hsq : χ ^ 2 = 1 := by
      by_contra hsq
      exact hN q χ s hsq (inRegion_mono' hccN hs) h0
    refine ⟨hsq, hχ1, ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hL q χ s hsq hχ1 hlt (inRegion_mono' hccL hs) h0
  obtain ⟨hsq, hχ1, hsm⟩ := key χ s hs hz
  obtain ⟨him, hder, -⟩ := hS q χ hsq hχ1 s s hsm hsm (inRegion_mono' hccS hs)
    (inRegion_mono' hccS hs) hz.2 hz.2
  refine ⟨hsq, hχ1, him, hder, ?_⟩
  intro χ' s' hs' hz'
  obtain ⟨hsq', hχ1', hsm'⟩ := key χ' s' hs' hz'
  have him' := (hS q χ' hsq' hχ1' s' s' hsm' hsm' (inRegion_mono' hccS hs')
    (inRegion_mono' hccS hs') hz'.2 hz'.2).1
  have hχeq : χ' = χ := by
    by_contra hne
    have es : ((s.re : ℝ) : ℂ) = s := Complex.ext (by simp) (by simp [him])
    have es' : ((s'.re : ℝ) : ℂ) = s' := Complex.ext (by simp) (by simp [him'])
    have r1 : InRegion c2 q ((s.re : ℝ) : ℂ) := by rw [es]; exact inRegion_mono' hcc2 hs
    have r2 : InRegion c2 q ((s'.re : ℝ) : ℂ) := by rw [es']; exact inRegion_mono' hcc2 hs'
    rcases h2 q χ χ' hsq hsq' hχ1 hχ1' (Ne.symm hne) s.re s'.re r1 r2 with h | h
    · exact h (by rw [es]; exact hz.2)
    · exact h (by rw [es']; exact hz'.2)
  refine ⟨hχeq, ?_⟩
  rw [hχeq] at hz'
  exact (hS q χ hsq hχ1 s s' hsm hsm' (inRegion_mono' hccS hs) (inRegion_mono' hccS hs')
    hz.2 hz'.2).2.2

end Formalism.ZeroFreeDirichlet
