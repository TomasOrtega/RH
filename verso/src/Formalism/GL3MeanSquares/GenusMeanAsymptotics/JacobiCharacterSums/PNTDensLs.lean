import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensSt
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensLsA

open Complex Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums

def Φe (j : ZMod 2) : ℂ := if j = 0 then -1 else 1

def eps (n : ℕ) : ℂ := Φe (n : ZMod 2)

/- English proof (translation)
Use `show ∑ j : Fin 2, (if j = 0 then (-1 : ℂ) else 1) = 0`. Simplify using `[Fin.sum_univ_two]`.
-/
lemma Φe_sum : ∑ j, Φe j = 0 := by
  show ∑ j : Fin 2, (if j = 0 then (-1 : ℂ) else 1) = 0
  simp [Fin.sum_univ_two]

/- English proof (translation)
Unfold `eps Φe`. Establish `h : ((n : ZMod 2) = 0) ↔ n % 2 = 0` using `by rw [ZMod.natCast_eq_zero_iff]; omega`. Distinguish the cases in `hn : n % 2 = 0`. Rewrite using `[if_pos (h.mpr hn), if_pos hn]`. Rewrite using `[if_neg (fun h' => hn (h.mp h')), if_neg hn]`.
-/
lemma eps_eq (n : ℕ) : eps n = if n % 2 = 0 then -1 else 1 := by
  unfold eps Φe
  have h : ((n : ZMod 2) = 0) ↔ n % 2 = 0 := by rw [ZMod.natCast_eq_zero_iff]; omega
  by_cases hn : n % 2 = 0
  · rw [if_pos (h.mpr hn), if_pos hn]
  · rw [if_neg (fun h' => hn (h.mp h')), if_neg hn]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [Ap_zero]`. Consider the case `succ n ih`. Rewrite using `[Ap_succ, ih, eps_eq]`. Break down `Nat.mod_two_eq_zero_or_one n with h | h` into its components or cases.

Establish `h' : (n + 1) % 2 = 1` using `by omega`. Rewrite using `[h, h']`. Evaluate the numerical expressions. Establish `h' : (n + 1) % 2 = 0` using `by omega`. Rewrite using `[h, h']`.

Evaluate the numerical expressions.
-/
lemma Ap_eps (n : ℕ) : Ap eps n = ((n % 2 : ℕ) : ℂ) := by
  induction n with
  | zero => simp [Ap_zero]
  | succ n ih =>
    rw [Ap_succ, ih, eps_eq]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h' : (n + 1) % 2 = 1 := by omega
      rw [h, h']
      norm_num
    · have h' : (n + 1) % 2 = 0 := by omega
      rw [h, h']
      norm_num

/- English proof (translation)
Rewrite using `[Ap_eps]`. Apply the tactic sequence `rcases Nat.mod_two_eq_zero_or_one M with h | h <;> rw [h] <;> simp`.
-/
lemma norm_Ap_eps_le (M : ℕ) : ‖Ap eps M‖ ≤ 1 := by
  rw [Ap_eps]
  rcases Nat.mod_two_eq_zero_or_one M with h | h <;> rw [h] <;> simp

/- English proof (translation)
Rewrite using `[ZMod.LFunction_eq_LSeries Φe hs]`. Establish `h1 : Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, eps n * (n : ℂ) ^ (-s)) atTop (𝓝 (LSeries (fun n => Φe n) s))`. Establish `hsum` using `(ZMod.LSeriesSummable_of_one_lt_re Φe hs).hasSum.tendsto_sum_nat`. Establish `h2` using `hsum.comp (tendsto_add_atTop_nat 1)`. Use `h2.congr (fun M => ?_)` and prove the remaining obligations.

Simplify using `only [Function.comp_apply]`. Rewrite using `[← Formalism.FX.LFunctionPartialSum.sum_Icc_eq_sum_range _ (LSeries.term_zero _ _)]`. Use `Finset.sum_congr rfl (fun n hn => ?_)` and prove the remaining obligations. Establish `hn0 : n ≠ 0`. Simplify using `only [Finset.mem_Icc] at hn`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]`. Both sides reduce to the same expression. Conclude with `tendsto_nhds_unique h1 (partial_tendsto_G eps norm_Ap_eps_le (by linarith))`.
-/
lemma LFunction_eq_G_of_one_lt {s : ℂ} (hs : 1 < s.re) : ZMod.LFunction Φe s = G eps s := by
  rw [ZMod.LFunction_eq_LSeries Φe hs]
  have h1 : Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, eps n * (n : ℂ) ^ (-s)) atTop
      (𝓝 (LSeries (fun n => Φe n) s)) := by
    have hsum := (ZMod.LSeriesSummable_of_one_lt_re Φe hs).hasSum.tendsto_sum_nat
    have h2 := hsum.comp (tendsto_add_atTop_nat 1)
    refine h2.congr (fun M => ?_)
    simp only [Function.comp_apply]
    rw [← Formalism.FX.LFunctionPartialSum.sum_Icc_eq_sum_range _ (LSeries.term_zero _ _)]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn0 : n ≠ 0 := by
      simp only [Finset.mem_Icc] at hn
      omega
    rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]
    rfl
  exact tendsto_nhds_unique h1 (partial_tendsto_G eps norm_Ap_eps_le (by linarith))

/- English proof (translation)
Establish `hU : IsOpen {s : ℂ | 0 < s.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hconn : IsPreconnected {s : ℂ | 0 < s.re}` using `(convex_halfSpace_re_gt 0).isPreconnected`. Establish `hf : AnalyticOnNhd ℂ (ZMod.LFunction Φe) {s : ℂ | 0 < s.re}` using `(ZMod.differentiable_LFunction_of_sum_zero Φe_sum).differentiableOn.analyticOnNhd hU`. Establish `hg : AnalyticOnNhd ℂ (G eps) {s : ℂ | 0 < s.re}` using `(G_differentiableOn eps norm_Ap_eps_le).analyticOnNhd hU`. Establish `h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re}` using `by simp`.

Establish `hev : ZMod.LFunction Φe =ᶠ[𝓝 (2 : ℂ)] G eps`. Establish `: {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ)` using `(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)`. Use `filter_upwards [this] with s hs`. Conclude with `LFunction_eq_G_of_one_lt hs`. Conclude with `hf.eqOn_of_preconnected_of_eventuallyEq hg hconn h2 hev hs`.
-/
lemma LFunction_eq_G {s : ℂ} (hs : 0 < s.re) : ZMod.LFunction Φe s = G eps s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ (ZMod.LFunction Φe) {s : ℂ | 0 < s.re} :=
    (ZMod.differentiable_LFunction_of_sum_zero Φe_sum).differentiableOn.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (G eps) {s : ℂ | 0 < s.re} :=
    (G_differentiableOn eps norm_Ap_eps_le).analyticOnNhd hU
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have hev : ZMod.LFunction Φe =ᶠ[𝓝 (2 : ℂ)] G eps := by
    have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [this] with s hs
    exact LFunction_eq_G_of_one_lt hs
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn h2 hev hs

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]`.
-/
lemma two_cpow_one_sub (s : ℂ) : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]

/- English proof (translation)
Distinguish the cases in `hj : j = 0`. Substitute `hj` using the available equality. Rewrite using `[MulChar.map_nonunit _ not_isUnit_zero]`. Simplify using `[Φe]`. Rewrite using `[MulChar.one_apply (isUnit_iff_ne_zero.mpr hj)]`.

Simplify using `[Φe, hj]`.
-/
lemma Φe_eq (j : ZMod 2) :
    Φe j = (1 : DirichletCharacter ℂ 2) j - (if j = 0 then 1 else 0) := by
  by_cases hj : j = 0
  · subst hj
    rw [MulChar.map_nonunit _ not_isUnit_zero]
    simp [Φe]
  · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hj)]
    simp [Φe, hj]

/- English proof (translation)
Establish `h2 : ZMod.LFunction Φe s = DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 2) s - (2 : ℂ) ^ (-s) * riemannZeta s`. Rewrite using `[DirichletCharacter.LFunction, ZMod.LFunction, ZMod.LFunction]`. Repeatedly rewrite using `[Φe_eq, sub_mul, Finset.sum_sub_distrib, mul_sub, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero, HurwitzZeta.hurwitzZeta_zero]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h3` using `DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 2) hs`. Rewrite `h3` using `[DirichletCharacter.LFunctionTrivChar, Nat.Prime.primeFactors Nat.prime_two, Finset.prod_singleton]`. Rewrite using `[h2, h3, two_cpow_one_sub]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma LFunction_Φe {s : ℂ} (hs : s ≠ 1) :
    ZMod.LFunction Φe s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have h2 : ZMod.LFunction Φe s =
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 2) s - (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [DirichletCharacter.LFunction, ZMod.LFunction, ZMod.LFunction]
    simp_rw [Φe_eq, sub_mul, Finset.sum_sub_distrib, mul_sub, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero, HurwitzZeta.hurwitzZeta_zero]
    push_cast
    ring
  have h3 := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 2) hs
  rw [DirichletCharacter.LFunctionTrivChar, Nat.Prime.primeFactors Nat.prime_two,
    Finset.prod_singleton] at h3
  rw [h2, h3, two_cpow_one_sub]
  push_cast
  ring

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih`. Establish `hA : ∀ g : ℕ → ℂ, (Finset.Icc 1 (2 * (N + 1))).sum g = (Finset.Icc 1 (2 * N)).sum g + g (2 * N + 1) + g (2 * N + 2)`. Introduce `g`.

Rewrite using `[show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]`. Establish `hB : ∀ g : ℕ → ℂ, (Finset.Icc 1 (N + 1)).sum g = (Finset.Icc 1 N).sum g + g (N + 1)` using `fun g => Finset.sum_Icc_succ_top (by omega) _`. Rewrite using `[hA (fun n => (n : ℂ) ^ (-s)), hA (fun n => eps n * (n : ℂ) ^ (-s)), hB (fun n => (n : ℂ) ^ (-s))]`. Establish `e1 : eps (2 * N + 1) = 1` using `by rw [eps_eq, if_neg (by omega)]`. Establish `e2 : eps (2 * N + 2) = -1` using `by rw [eps_eq, if_pos (by omega)]`.

Establish `hb : ((2 * N + 2 : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * ((N + 1 : ℕ) : ℂ) ^ (-s)`. Establish `h` using `natCast_mul_natCast_cpow 2 (N + 1) (-s)`. Rewrite using `[show ((2 * N + 2 : ℕ) : ℂ) = ((2 : ℕ) : ℂ) * ((N + 1 : ℕ) : ℂ) by push_cast; ring, h]`. Evaluate the numerical expressions. Rewrite using `[e1, e2, hb]`.

Rewrite `ih`, the goal using `[two_cpow_one_sub]`. Take the linear combination `ih`.
-/
lemma alt_sum (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 (2 * N), (n : ℂ) ^ (-s) - (2 : ℂ) ^ (1 - s) * ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 (2 * N), eps n * (n : ℂ) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hA : ∀ g : ℕ → ℂ, (Finset.Icc 1 (2 * (N + 1))).sum g =
        (Finset.Icc 1 (2 * N)).sum g + g (2 * N + 1) + g (2 * N + 2) := by
      intro g
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
    have hB : ∀ g : ℕ → ℂ, (Finset.Icc 1 (N + 1)).sum g = (Finset.Icc 1 N).sum g + g (N + 1) :=
      fun g => Finset.sum_Icc_succ_top (by omega) _
    rw [hA (fun n => (n : ℂ) ^ (-s)), hA (fun n => eps n * (n : ℂ) ^ (-s)),
      hB (fun n => (n : ℂ) ^ (-s))]
    have e1 : eps (2 * N + 1) = 1 := by rw [eps_eq, if_neg (by omega)]
    have e2 : eps (2 * N + 2) = -1 := by rw [eps_eq, if_pos (by omega)]
    have hb : ((2 * N + 2 : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * ((N + 1 : ℕ) : ℂ) ^ (-s) := by
      have h := natCast_mul_natCast_cpow 2 (N + 1) (-s)
      rw [show ((2 * N + 2 : ℕ) : ℂ) = ((2 : ℕ) : ℂ) * ((N + 1 : ℕ) : ℂ) by push_cast; ring, h]
      norm_num
    rw [e1, e2, hb]
    rw [two_cpow_one_sub] at ih ⊢
    linear_combination ih

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet EtaPartialSums

/- English proof (translation)
Introduce `s hs hs1 N hN`. Establish `hG : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = EtaPartialSums.G eps s`. Rewrite using `[← LFunction_Φe hs1, LFunction_eq_G hs]`. Rewrite using `[hG, alt_sum]`. Use `(norm_G_sub_partial_le eps norm_Ap_eps_le hs (2 * N)).trans ?_` and prove the remaining obligations.

Establish `hNpos : (0 : ℝ) < N` using `by exact_mod_cast hN`. Establish `h3 : (((2 * N : ℕ) : ℝ) + 1) ^ (-s.re) ≤ (N : ℝ) ^ (-s.re)`. Apply `Real.rpow_le_rpow_of_nonpos hNpos _ (by linarith)` to reduce the goal to its premises. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hq : 0 ≤ 1 + ‖s‖ / s.re`. Use `div_nonneg (norm_nonneg s) hs.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : 0 ≤ (N : ℝ) ^ (-s.re)` using `Real.rpow_nonneg hNpos.le _`. Combine the equalities or inequalities in the displayed calculation.

Use `mul_nonneg hq h4` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem eta_partial_sums : EtaPartial := by
  intro s hs hs1 N hN
  have hG : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = EtaPartialSums.G eps s := by
    rw [← LFunction_Φe hs1, LFunction_eq_G hs]
  rw [hG, alt_sum]
  refine (norm_G_sub_partial_le eps norm_Ap_eps_le hs (2 * N)).trans ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : (((2 * N : ℕ) : ℝ) + 1) ^ (-s.re) ≤ (N : ℝ) ^ (-s.re) := by
    apply Real.rpow_le_rpow_of_nonpos hNpos _ (by linarith)
    push_cast
    linarith
  have hq : 0 ≤ 1 + ‖s‖ / s.re := by
    have := div_nonneg (norm_nonneg s) hs.le
    linarith
  have h4 : 0 ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg hNpos.le _
  calc 1 * (1 + ‖s‖ / s.re) * (((2 * N : ℕ) : ℝ) + 1) ^ (-s.re)
      ≤ 1 * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
    _ ≤ 4 * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
        have := mul_nonneg hq h4
        nlinarith

/- English proof (translation)
Introduce `M _ s hs hz`. Establish `hs1 : s ≠ 1`. Break down `hz.1 with h | h` into its components or cases. Conclude with `absurd rfl h`. Conclude with `h`.

Establish `h` using `hz.2`. Rewrite `h` using `[← DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1]`. Break down `mul_eq_zero.mp h with h | h` into its components or cases. It suffices to derive a contradiction. Rewrite `h` using `[Finset.prod_eq_zero_iff]`.

Take `⟨p, hp, hp0⟩` from `h`. Establish `hpp` using `Nat.prime_of_mem_primeFactors hp`. Establish `hlt : ‖(p : ℂ) ^ (-s)‖ < 1`. Rewrite using `[Complex.norm_natCast_cpow_of_pos hpp.pos]`. Simplify using `only [Complex.neg_re]`.

Conclude with `Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by linarith)`. Establish `: (p : ℂ) ^ (-s) = 1` using `by linear_combination -hp0`. Rewrite `hlt` using `[this, norm_one]`. Conclude with `lt_irrefl _ hlt`. Conclude with `h`.
-/
theorem principal_zeta_bound : PrincipalZeta := by
  intro M _ s hs hz
  have hs1 : s ≠ 1 := by
    rcases hz.1 with h | h
    · exact absurd rfl h
    · exact h
  have h := hz.2
  rw [← DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1] at h
  rcases mul_eq_zero.mp h with h | h
  · exfalso
    rw [Finset.prod_eq_zero_iff] at h
    obtain ⟨p, hp, hp0⟩ := h
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos]
      simp only [Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by linarith)
    have : (p : ℂ) ^ (-s) = 1 := by linear_combination -hp0
    rw [this, norm_one] at hlt
    exact lt_irrefl _ hlt
  · exact h

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
