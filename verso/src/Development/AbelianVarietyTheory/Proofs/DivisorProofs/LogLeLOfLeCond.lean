import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.ColumnNormCompare.SizeRows

variable {D : D7} {large₂ : SizeData₂ D}

/- English proof (translation)
Unfold `Scale.b Scale.L`. Use `s.one_lt_alt` as an intermediate fact. Conclude with `Real.one_le_exp (by positivity)`.
-/
theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  have := s.one_lt_alt
  exact Real.one_le_exp (by positivity)

/- English proof (translation)
Establish `h` using `P.condE_le`. Establish `hb` using `one_le_b large₂.sc`. Establish `h1 : large₂.sc.b ^ ((1 : ℝ) / 2) ≤ large₂.sc.b`. Simplify using `using Real.rpow_le_rpow_of_exponent_le hb (show (1 : ℝ) / 2 ≤ 1 by norm_num)`. Establish `ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150` using `one_le_pow₀ large₂.t_win.1`.

Establish `hc : (LevelStarExponents.condE D : ℝ) ≤ (LevelStarExponents.condE D : ℝ) ^ 36`. Conclude with `Nat.le_self_pow (by norm_num) _` after adjusting the coercions. Establish `h2 : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ (LevelStarExponents.condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150` using `le_mul_of_one_le_right (by positivity) ht`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem condE_le_b (P : ParameterChoice' D large₂) : (LevelStarExponents.condE D : ℝ) ≤ large₂.sc.b := by
  have h := P.condE_le
  have hb := one_le_b large₂.sc
  have h1 : large₂.sc.b ^ ((1 : ℝ) / 2) ≤ large₂.sc.b := by
    simpa using Real.rpow_le_rpow_of_exponent_le hb (show (1 : ℝ) / 2 ≤ 1 by norm_num)
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ large₂.t_win.1
  have hc : (LevelStarExponents.condE D : ℝ) ≤ (LevelStarExponents.condE D : ℝ) ^ 36 := by
    exact_mod_cast Nat.le_self_pow (by norm_num) _
  have h2 : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ (LevelStarExponents.condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 :=
    le_mul_of_one_le_right (by positivity) ht
  linarith

/- English proof (translation)
Establish `h1 : (p : ℝ) ≤ Real.exp large₂.sc.L` using `le_trans (by exact_mod_cast h) (condE_le_b P)`. Conclude with `(Real.log_le_iff_le_exp (by exact_mod_cast hp)).2 h1`.
-/
theorem log_le_L_of_le_cond (P : ParameterChoice' D large₂) {p : ℕ} (hp : 0 < p) (h : p ≤ LevelStarExponents.condE D) :
    Real.log p ≤ large₂.sc.L := by
  have h1 : (p : ℝ) ≤ Real.exp large₂.sc.L := le_trans (by exact_mod_cast h) (condE_le_b P)
  exact (Real.log_le_iff_le_exp (by exact_mod_cast hp)).2 h1

/- English proof (translation)
Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Establish `hk' : (1 : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : 1 ≤ D.R.k)`. Establish `hf : (0 : ℝ) < D.R.f`. Establish `: 0 < D.R.f` using `by unfold Ranks.f Ranks.n; positivity`. Conclude with `this` after adjusting the coercions.

Establish `ht` using `large₂.t_win.1`. Establish `he` using `large₂.etaSz_pos`. Establish `h` using `P.eta_le`. Rewrite `h` using `[le_div_iff₀ (by positivity)]`. Establish `hN : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3`.

Conclude with `Nat.le_self_pow (by norm_num) _` after adjusting the coercions. Establish `hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3` using `by positivity`. Unfold `placeRankTwoOne.NN at h4`. Establish `h5 : (D.R.N D.R.m : ℝ) ≤ large₂.etaSz` using `by linarith`. Establish `h6 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3` using `one_le_pow₀ ht`.

Establish `h7 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3` using `one_le_pow₀ hk'`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem f_mul_N_le_b (P : ParameterChoice' D large₂) (h4 : 4 * placeRankTwoOne.NN D ^ 3 ≤ large₂.etaSz) :
    (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ≤ large₂.sc.b := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk' : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (0 : ℝ) < D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  have ht := large₂.t_win.1
  have he := large₂.etaSz_pos
  have h := P.eta_le
  rw [le_div_iff₀ (by positivity)] at h
  have hN : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by
    exact_mod_cast Nat.le_self_pow (by norm_num) _
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
  unfold placeRankTwoOne.NN at h4
  have h5 : (D.R.N D.R.m : ℝ) ≤ large₂.etaSz := by linarith
  have h6 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ ht
  have h7 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hk'
  calc (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) = (D.R.N D.R.m : ℝ) * (1 * D.R.f * 1) := by ring
    _ ≤ large₂.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := by gcongr
    _ ≤ _ := h

/- English proof (translation)
Unfold `tauPl`. Rewrite using `[Equiv.apply_symm_apply]`.
-/
theorem eTau_tauPl (z : RPl D.R) : (D.eTau (tauPl D z) : D.R.GG) = G.plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

/- English proof (translation)
Rewrite using `[eTau_tauPl]`. Introduce `h`. Unfold `Host.topPlaces at h`. Take `⟨t, ht, he⟩` from `Finset.mem_image.1 h`. Take `⟨b, s⟩` from `z`.

Consider the cases of `b`. Establish `h1 : D.R.tau1 t = D.R.tau1 s` using `he`. Establish `h2 : t = s` using `D.R.toFrame.tau1_injective h1`. Substitute `h2` using the available equality. Conclude with `hz ⟨rfl, ht⟩`.

Establish `h1 : D.R.tau1 t = D.R.tau2 s` using `he`. Conclude with `(factPlaces D.R.toFrame).2 _ _ h1`.
-/
theorem not_top_of (z : RPl D.R) (hz : ¬ PlaceLogThetaBounds.IsTopPl (numDatumOfParameters D large₂) z) :
    (D.eTau (tauPl D z) : D.R.GG) ∉ D.host.topPlaces := by
  rw [eTau_tauPl]
  intro h
  unfold Host.topPlaces at h
  obtain ⟨t, ht, he⟩ := Finset.mem_image.1 h
  obtain ⟨b, s⟩ := z
  cases b
  · have h1 : D.R.tau1 t = D.R.tau1 s := he
    have h2 : t = s := D.R.toFrame.tau1_injective h1
    subst h2
    exact hz ⟨rfl, ht⟩
  · have h1 : D.R.tau1 t = D.R.tau2 s := he
    exact (factPlaces D.R.toFrame).2 _ _ h1

/- English proof (translation)
Introduce `D large₂ EX ⟨⟨P⟩, hS, _⟩ ⟨⟨n, hn⟩, hg, _⟩ u hnu`. Take `⟨-, s2, s3, s4, -, -, s7, -, s9, s10, -, -, -, s14⟩` from `hS`. Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Establish `hm : (0 : ℝ) < D.R.m` using `by have := D.R.two_le_m; exact_mod_cast (by omega : 0 < D.R.m)`. Establish `hDel : ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del` using `by rw [hn, Nat.floor_natCast]`.

Establish `hSc : (numDatumOfParameters D large₂).Sc = large₂.Sc`. Rewrite using `[large₂.Sc_eq]`. Use `show (D.R.k : ℝ) * (4 * ((⌊D.s.Del⌋₊ : ℕ) : ℝ)) = _`. Rewrite using `[← Rat.cast_natCast, ← Rat.cast_natCast (α := ℝ) ⌊D.s.Del⌋₊, hDel]`. Establish `hq` using `D.host.hyp.1.pos`.

Establish `hd` using `D.host.hyp.2.1.pos`. Establish `hn0 : 0 < D.R.n` using `by unfold Ranks.n; positivity`. Use `⟨⟨?_, ?_, ?_, s4, ?_⟩, fun i => ⟨?_, hg i⟩, s7 u, f_mul_N_le_b P s10, hnu, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `s2`. Use `log_le_L_of_le_cond P hq ?_` and prove the remaining obligations.

Unfold `LevelStarExponents.condE`. Conclude with `le_trans (Nat.le_mul_of_pos_left D.host.q D.host.QS_pos) (Nat.le_mul_of_pos_right _ hd)`. Use `log_le_L_of_le_cond P hd ?_` and prove the remaining obligations. Unfold `LevelStarExponents.condE`. Conclude with `Nat.le_mul_of_pos_left D.host.d (Nat.mul_pos D.host.QS_pos hq)`.

Rewrite `s3` using `[large₂.logDerivative_at_one_eq]`. Conclude with `s3`. Take `⟨Y, h1, -, -, h2⟩` from `P.g_Y`. Conclude with `h1.trans (h2 i).1`. Introduce `z i j`.

Use `(large₂.be_close (tauPl D z) i j).trans ?_` and prove the remaining obligations. Use `show large₂.etaSz ≤ (D.R.m : ℝ) * ((⌈LevelStarExponents.h0 large₂⌉₊ : ℕ) : ℝ)`. Establish `h` using `Nat.le_ceil (LevelStarExponents.h0 large₂)`. Combine the equalities or inequalities in the displayed calculation. Introduce `z i`.

Rewrite using `[hSc]`. Take `⟨h1, h2⟩` from `large₂.cloud_v (tauPl D z) i`. Conclude with `⟨by exact_mod_cast h1, h2⟩`. Introduce `z i h1 h2`. Take `⟨i, hi⟩` from `i`.

Take `⟨l, rfl⟩ : ∃ l, i = l + 1` from `⟨i - 1, by simp only at h1; omega⟩`. Establish `hl : l < D.R.k - 2`. Establish `: l + 1 + 1 < D.R.k` using `h2`. Use linear arithmetic over natural numbers and integers. Establish `e : (numDatumOfParameters D large₂).uW (codeRec large₂ u) z ⟨l + 1, hi⟩ = (D.hcW u (tauPl D z)).u ⟨l + 1, hi⟩`.

Rewrite using `[D.s.u_letter u (tauPl D z) l hl, D.hcW_v]`. Unfold `NumDatum.uW`. Rewrite using `[dif_pos ⟨h1, h2⟩]`. Use `show _ - _ - (if D.s.letter u ⟨l, hl⟩ = true then ((⌊D.s.Del⌋₊ : ℕ) : ℚ) else 0) = _`. Rewrite using `[hDel]`.

Both sides reduce to the same expression. Rewrite using `[hSc, e]`. Take `⟨a1, a2⟩` from `large₂.cloud_u u (tauPl D z) ⟨l + 1, hi⟩ h1 h2`. Conclude with `⟨by exact_mod_cast a1, a2⟩`. Introduce `t ht`.

Establish `h` using `(large₂.top_u (tauPl D (false, t)) ⟨t, ht⟩ (by omega) (eTau_tauPl (false, t))).2`. Establish `e : (((numDatumOfParameters D large₂).bT t : ℚ) : ℝ) = (large₂.bT ⟨t, ht⟩ : ℝ)`. Unfold `NumDatum.bT`. Use `push_cast`. Use `erw [h]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `⟨large₂.bT_ge _, s14 _⟩`. Introduce `z hz hk2`. Establish `hz'` using `not_top_of z hz`.

Rewrite using `[hSc]`. Use `⟨s9 _ hk2 hz', (large₂.cloud_gap _ (by omega) hz').1, ?_⟩` and prove the remaining obligations. Establish `h1` using `P.cloud_place_bound _ (by omega) hz'`. Establish `h2` using `(large₂.cloud_v (tauPl D z) ⟨0, by omega⟩).2`. Move the coercions through the operations in `at h1`.

Use `show (((D.hc (tauPl D z)).u ⟨0, by omega⟩ : ℚ) : ℝ) ≤ _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sizeRows_numRec : ∀ (D : D7) (large₂ : SizeData₂ D) (EX : ErrX D), ConjugateFieldBounds.ParamHyp large₂ EX 25 → PageRows large₂ EX → ∀ (u : D.what₂.Word), (∀ j ∈ (numDatumOfParameters D large₂).lifts, ∀ z, ∀ i < D.R.N (j - 1), 0 ≤ (numDatumOfParameters D large₂).nu (codeRec large₂ u) j z i ∧ (((numDatumOfParameters D large₂).nu (codeRec large₂ u) j z i : ℚ) : ℝ) ≤ 3 * large₂.sc.a) → PlaceLogThetaBounds.SizeRows (numDatumOfParameters D large₂) (codeRec large₂ u) (D.mem u).A.T := by
  intro D large₂ EX ⟨⟨P⟩, hS, _⟩ ⟨⟨n, hn⟩, hg, _⟩ u hnu
  obtain ⟨-, s2, s3, s4, -, -, s7, -, s9, s10, -, -, -, s14⟩ := hS
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hm : (0 : ℝ) < D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 0 < D.R.m)
  have hDel : ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del := by rw [hn, Nat.floor_natCast]
  have hSc : (numDatumOfParameters D large₂).Sc = large₂.Sc := by
    rw [large₂.Sc_eq]
    show (D.R.k : ℝ) * (4 * ((⌊D.s.Del⌋₊ : ℕ) : ℝ)) = _
    rw [← Rat.cast_natCast, ← Rat.cast_natCast (α := ℝ) ⌊D.s.Del⌋₊, hDel]
  have hq := D.host.hyp.1.pos
  have hd := D.host.hyp.2.1.pos
  have hn0 : 0 < D.R.n := by unfold Ranks.n; positivity
  refine ⟨⟨?_, ?_, ?_, s4, ?_⟩, fun i => ⟨?_, hg i⟩, s7 u, f_mul_N_le_b P s10, hnu, ?_, ?_, ?_, ?_, ?_⟩
  · exact s2
  · refine log_le_L_of_le_cond P hq ?_
    unfold LevelStarExponents.condE
    exact le_trans (Nat.le_mul_of_pos_left D.host.q D.host.QS_pos) (Nat.le_mul_of_pos_right _ hd)
  · refine log_le_L_of_le_cond P hd ?_
    unfold LevelStarExponents.condE
    exact Nat.le_mul_of_pos_left D.host.d (Nat.mul_pos D.host.QS_pos hq)
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
    refine ⟨s9 _ hk2 hz', (large₂.cloud_gap _ (by omega) hz').1, ?_⟩
    have h1 := P.cloud_place_bound _ (by omega) hz'
    have h2 := (large₂.cloud_v (tauPl D z) ⟨0, by omega⟩).2
    push_cast at h1
    show (((D.hc (tauPl D z)).u ⟨0, by omega⟩ : ℚ) : ℝ) ≤ _
    linarith

end GlobalTheory.ColumnNormCompare.SizeRows
