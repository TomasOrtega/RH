import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

namespace GlobalTheory.CovTop.Sizes

/- English proof (translation)
Establish `h1` using `(tendsto_rpow_atTop he).eventually_ge_atTop M`. Establish `h2` using `(tendsto_rpow_atTop he).eventually_ge_atTop 10`. Establish `h3` using `(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1`. Establish `h5` using `(tendsto_rpow_atTop (by positivity : 0 < eps / 5)).eventually_ge_atTop 5`. Establish `h6` using `Filter.eventually_ge_atTop ((10 : ℝ) ^ 60)`.

Establish `h4` using `((isLittleO_log_rpow_atTop he).const_mul_left (A * M)).bound one_pos`. Take `⟨x0, hx0⟩` from `Filter.eventually_atTop.1 (h1.and (h2.and (h3.and (h4.and (h5.and h6)))))`. Use `⟨x0, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨a1, a2, a3, a4, a5, a6⟩` from `hx0 x hx`. Establish `hx0' : 0 < x` using `lt_of_lt_of_le (by norm_num) a6`.

Use `⟨a1, a2, a3, ?_, a5, a6⟩` and prove the remaining obligations. Rewrite using `[← Real.rpow_mul hx0'.le, Real.rpow_def_of_pos hx0', Real.exp_le_exp]`. Rewrite `a4` using `[one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0' eps)]`. Rewrite using `[mul_comm]`. Conclude with `(le_abs_self _).trans a4`.
-/
theorem eventually_scale {eps : ℝ} (he : 0 < eps) (A M : ℝ) : ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
    M ≤ x ^ eps ∧ 10 ≤ x ^ eps ∧ 1 ≤ Real.log (Real.log x) ∧ (x ^ A) ^ M ≤ Real.exp (x ^ eps) ∧ 5 ≤ x ^ (eps / 5) ∧
      (10 : ℝ) ^ 60 ≤ x := by
  have h1 := (tendsto_rpow_atTop he).eventually_ge_atTop M
  have h2 := (tendsto_rpow_atTop he).eventually_ge_atTop 10
  have h3 := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1
  have h5 := (tendsto_rpow_atTop (by positivity : 0 < eps / 5)).eventually_ge_atTop 5
  have h6 := Filter.eventually_ge_atTop ((10 : ℝ) ^ 60)
  have h4 := ((isLittleO_log_rpow_atTop he).const_mul_left (A * M)).bound one_pos
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (h1.and (h2.and (h3.and (h4.and (h5.and h6)))))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hx0 x hx
  have hx0' : 0 < x := lt_of_lt_of_le (by norm_num) a6
  refine ⟨a1, a2, a3, ?_, a5, a6⟩
  rw [← Real.rpow_mul hx0'.le, Real.rpow_def_of_pos hx0', Real.exp_le_exp]
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0' eps)] at a4
  rw [mul_comm]
  exact (le_abs_self _).trans a4

/- English proof (translation)
The claim follows from `((Nat.Prime.coprime_iff_not_dvd hg).2 fun hd => absurd (Nat.le_of_dvd (by norm_num) hd) (not_le.2 h)).symm`.
-/
theorem coprime_fifteen {g : ℕ} (hg : g.Prime) (h : 15 < g) : Nat.Coprime 15 g :=
  ((Nat.Prime.coprime_iff_not_dvd hg).2 fun hd => absurd (Nat.le_of_dvd (by norm_num) hd) (not_le.2 h)).symm

/- English proof (translation)
Establish `hfr` using `Pm.fr_le_pow S hx`. Take `⟨sN, -, -, -, -, -, sQD, -, -, -, -, -, -, -, -, -, -, sW, -, -, sG, -, -⟩` from `S`. Establish `hx1` using `L.sc.one_lt_alt.le`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `he` using `L.sc.eps_pos`.

Establish `he'` using `L.sc.eps_lt`. Establish `hL` using `Pm.one_le_L L`. Establish `hf` using `Pm.two_le_f D`. Establish `hr` using `Pm.six_le_r D`. Establish `hrt` using `Pm.r_le_alt_alt D`.

Establish `hLx : L.sc.L ≤ L.sc.x`. Combine the equalities or inequalities in the displayed calculation. Establish `hnV : (D.R.nV : ℝ) ≤ 2 * D.R.t`. Establish `: (D.R.nV : ℝ) = D.R.r + D.R.t` using `by unfold Ranks.nV; push_cast; ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hnV0 : (0 : ℝ) < D.R.nV`. Establish `: (D.R.nV : ℝ) = D.R.r + D.R.t` using `by unfold Ranks.nV; push_cast; ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hCt : 0 ≤ L.Ct`. Assume the negation of the conclusion as `hc`.

Use `Real.rpow_lt_one_of_one_lt_of_neg L.sc.one_lt_alt (not_le.1 hc)` as an intermediate fact. Combine the linear relations using `[L.t_win.1, L.t_win.2]`. Establish `hgl : ∀ k, 15 < D.host.g k` using `fun k => by`. Establish `hk : (1 : ℝ) ≤ D.R.k`. Establish `: 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`.

Conclude with `this` after adjusting the coercions. Establish `hb : (2 : ℝ) ≤ L.sc.b`. Use `Real.add_one_le_exp L.sc.L` as an intermediate fact. Unfold `Scale.b`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2 : (2 : ℝ) ≤ (D.R.k : ℝ) * L.sc.b` using `by nlinarith`. Establish `h3 : (2 : ℝ) ^ 8 ≤ D.host.g k` using `(pow_le_pow_left₀ (by norm_num) h2 8).trans (sG k k).1`. Establish `h4 : ((15 : ℕ) : ℝ) < D.host.g k` using `lt_of_lt_of_le (by norm_num) h3`. Conclude with `h4` after adjusting the coercions. Use `⟨⟨a1, a2, hLx, a3⟩, ?_, ?_, ⟨?_, ?_⟩, hg, ?_, ?_, ?_, ?_, ?_, ⟨by linarith, ?_, ?_⟩, a4, sW⟩` and prove the remaining obligations.

Establish `h1 : L.sc.x ≤ L.sc.x ^ (2 + 8 * L.sc.eps - szTh L)`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : (4 : ℝ) ≤ D.R.n` using `le_trans (by norm_num) (hx.trans (h1.trans sN.1))`. Establish `h3 : ((8 : ℕ) : ℝ) ≤ D.R.f` using `by rw [Pm.f_eq]; push_cast; linarith`. Conclude with `h3` after adjusting the coercions.

Establish `h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord` using `D.host.finrank_cmField`. Rewrite using `[h1]`. Unfold `Ranks.f Ranks.n`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Real.log_mul (by linarith) (by linarith)]`.

Combine the linear relations using `[Pm.log_f_le P, Pm.log_r_le P]`. Establish `h1` using `Real.log_le_log hnV0 hnV`. Rewrite `h1` using `[Real.log_mul (by norm_num) (by linarith)]`. Combine the linear relations using `[(Pm.log_cond_le P).2, Real.log_two_lt_d9]`. Establish `h : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ 2 * D.R.f * L.sc.L` using `logdE_le_two_f_L P`.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `sQD.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith))`. Conclude with `le_trans (Nat.le_floor (by exact_mod_cast a5)) L.split_tie`. Conclude with `Nat.Coprime.mul_right (coprime_fifteen (D.host.g_prime 0) (hgl 0)) (coprime_fifteen (D.host.g_prime 1) (hgl 1))`. Establish `hZ` using `Pm.one_le_Z L`.

Establish `h1 : zBase L ^ 12 ≤ zBase L ^ T.eP`. Rewrite using `[← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hZ (by exact_mod_cast T.eP_ge)`. Rewrite using `[T.PP_eq]`. Conclude with `h1.trans (le_mul_of_one_le_left (by positivity) T.one_le_CP)`.

Conclude with `T.PP_poly.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))`. Establish `h2 : (D.R.nV : ℝ) ≤ L.sc.x * L.sc.x ^ L.Ct` using `hnV.trans (mul_le_mul (le_trans (by norm_num) hx) L.t_win.2 (by positivity) hx0.le)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_one]`. Use `_ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`.
-/
theorem hostNum_of_sizes {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (T : ParamsT D L P) (S : SizesAt L) {A M : ℝ}
    (hg : ∀ k, Real.log (D.host.g k : ℝ) ≤ 9 * L.sc.L + 1) (hA : 22 + L.Ct ≤ A)
    (a1 : M ≤ L.sc.L) (a2 : 10 ≤ L.sc.L) (a3 : 1 ≤ Real.log (Real.log L.sc.x)) (a4 : (L.sc.x ^ A) ^ M ≤ L.sc.b)
    (a5 : 5 ≤ L.sc.x ^ (L.sc.ez / 5)) (hx : (10 : ℝ) ^ 60 ≤ L.sc.x) : HostNum D L T.PP A M := by
  have hfr := Pm.fr_le_pow S hx
  obtain ⟨sN, -, -, -, -, -, sQD, -, -, -, -, -, -, -, -, -, -, sW, -, -, sG, -, -⟩ := S
  have hx1 := L.sc.one_lt_alt.le
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_pos
  have he' := L.sc.eps_lt
  have hL := Pm.one_le_L L
  have hf := Pm.two_le_f D
  have hr := Pm.six_le_r D
  have hrt := Pm.r_le_alt_alt D
  have hLx : L.sc.L ≤ L.sc.x := by
    calc L.sc.L = L.sc.x ^ L.sc.eps := rfl
      _ ≤ L.sc.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = L.sc.x := Real.rpow_one _
  have hnV : (D.R.nV : ℝ) ≤ 2 * D.R.t := by
    have : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
    linarith
  have hnV0 : (0 : ℝ) < D.R.nV := by
    have : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
    linarith
  have hCt : 0 ≤ L.Ct := by
    by_contra hc
    have := Real.rpow_lt_one_of_one_lt_of_neg L.sc.one_lt_alt (not_le.1 hc)
    linarith [L.t_win.1, L.t_win.2]
  have hgl : ∀ k, 15 < D.host.g k := fun k => by
    have hk : (1 : ℝ) ≤ D.R.k := by
      have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
      exact_mod_cast this
    have hb : (2 : ℝ) ≤ L.sc.b := by
      have := Real.add_one_le_exp L.sc.L
      unfold Scale.b
      linarith
    have h2 : (2 : ℝ) ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
    have h3 : (2 : ℝ) ^ 8 ≤ D.host.g k := (pow_le_pow_left₀ (by norm_num) h2 8).trans (sG k k).1
    have h4 : ((15 : ℕ) : ℝ) < D.host.g k := lt_of_lt_of_le (by norm_num) h3
    exact_mod_cast h4
  refine ⟨⟨a1, a2, hLx, a3⟩, ?_, ?_, ⟨?_, ?_⟩, hg, ?_, ?_, ?_, ?_, ?_, ⟨by linarith, ?_, ?_⟩, a4, sW⟩
  · have h1 : L.sc.x ≤ L.sc.x ^ (2 + 8 * L.sc.eps - szTh L) := by
      calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith)
    have h2 : (4 : ℝ) ≤ D.R.n := le_trans (by norm_num) (hx.trans (h1.trans sN.1))
    have h3 : ((8 : ℕ) : ℝ) ≤ D.R.f := by rw [Pm.f_eq]; push_cast; linarith
    exact_mod_cast h3
  · have h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
    rw [h1]; unfold Ranks.f Ranks.n; ring
  · rw [Real.log_mul (by linarith) (by linarith)]
    linarith [Pm.log_f_le P, Pm.log_r_le P]
  · have h1 := Real.log_le_log hnV0 hnV
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith [(Pm.log_cond_le P).2, Real.log_two_lt_d9]
  · have h : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ 2 * D.R.f * L.sc.L := logdE_le_two_f_L P
    nlinarith
  · exact sQD.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith))
  · exact le_trans (Nat.le_floor (by exact_mod_cast a5)) L.split_tie
  · exact Nat.Coprime.mul_right (coprime_fifteen (D.host.g_prime 0) (hgl 0)) (coprime_fifteen (D.host.g_prime 1) (hgl 1))
  · have hZ := Pm.one_le_Z L
    have h1 : zBase L ^ 12 ≤ zBase L ^ T.eP := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by exact_mod_cast T.eP_ge)
    rw [T.PP_eq]
    exact h1.trans (le_mul_of_one_le_left (by positivity) T.one_le_CP)
  · exact T.PP_poly.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  · have h2 : (D.R.nV : ℝ) ≤ L.sc.x * L.sc.x ^ L.Ct :=
      hnV.trans (mul_le_mul (le_trans (by norm_num) hx) L.t_win.2 (by positivity) hx0.le)
    calc (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L ≤ L.sc.x ^ (20 : ℝ) * (L.sc.x * L.sc.x ^ L.Ct) * L.sc.x := by gcongr
      _ = L.sc.x ^ (20 + (1 + L.Ct) + 1) := by
        rw [Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)

/- English proof (translation)
Introduce `M`. Use `⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ => ?_⟩⟩` and prove the remaining obligations. Take `⟨x0, hx0⟩` from `eventually_scale he (22 + |Fm.Ct|) M`. Establish `hez : 0 < Fm.ez` using `div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)`. Take `⟨x2, hx2⟩` from `Filter.eventually_atTop.1 ((tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 5)).eventually_ge_atTop 5)`.

Use `⟨22 + |Fm.Ct|, by positivity, max x0 x2, fun x hx hle ι p _ _ => ?_⟩` and prove the remaining obligations. Take `⟨a1, a2, a3, a4, -, a6⟩` from `hx0 x ((le_max_left _ _).trans hle)`. Establish `a5 : 5 ≤ x ^ (Fm.ez / 5)` using `hx2 x ((le_max_right _ _).trans hle)`. Establish `hsz : (Fm.L x ι).sc.ez = Fm.ez` using `Fm.toFamCore.L_ez x ι`. Establish `hsx : (Fm.L x ι).sc.x = x` using `Fm.L_x x ι hx`.

Establish `hse : (Fm.L x ι).sc.eps = eps` using `Fm.L_eps x ι`. Establish `hsL : (Fm.L x ι).sc.L = x ^ eps` using `by unfold Scale.L; rw [hsx, hse]`. Establish `hg : ∀ k, Real.log ((Fm.D x ι).host.g k) ≤ 9 * (Fm.L x ι).sc.L + 1` using `fun k => by`. Establish `hlo : 0 < ((((Fm.D x ι).host.g k : ℕ)) : ℝ)` using `by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos`. Use `(Real.log_le_iff_le_exp hlo).2 ((hF.1.2.2.2.2.2.2.2.2 x hx ι).2.2.1 k)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `hostNum_of_sizes (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) hg ?_ ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[Fm.Ct_eq]`. Combine the linear relations using `[le_abs_self Fm.Ct]`. Rewrite using `[hsL]` and apply the resulting hypothesis.

Rewrite using `[hsL]` and apply the resulting hypothesis. Rewrite using `[hsx]` and apply the resulting hypothesis. Unfold `Scale.b`. Rewrite using `[hsL, hsx]` and apply the resulting hypothesis. Rewrite using `[hsx, hsz]` and apply the resulting hypothesis.

Rewrite using `[hsx]` and apply the resulting hypothesis.
-/
theorem hostN : ∀ M : ℝ, HostN M := by
  intro M
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := eventually_scale he (22 + |Fm.Ct|) M
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  obtain ⟨x2, hx2⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 5)).eventually_ge_atTop 5)
  refine ⟨22 + |Fm.Ct|, by positivity, max x0 x2, fun x hx hle ι p _ _ => ?_⟩
  obtain ⟨a1, a2, a3, a4, -, a6⟩ := hx0 x ((le_max_left _ _).trans hle)
  have a5 : 5 ≤ x ^ (Fm.ez / 5) := hx2 x ((le_max_right _ _).trans hle)
  have hsz : (Fm.L x ι).sc.ez = Fm.ez := Fm.toFamCore.L_ez x ι
  have hsx : (Fm.L x ι).sc.x = x := Fm.L_x x ι hx
  have hse : (Fm.L x ι).sc.eps = eps := Fm.L_eps x ι
  have hsL : (Fm.L x ι).sc.L = x ^ eps := by unfold Scale.L; rw [hsx, hse]
  have hg : ∀ k, Real.log ((Fm.D x ι).host.g k) ≤ 9 * (Fm.L x ι).sc.L + 1 := fun k => by
    have hlo : 0 < ((((Fm.D x ι).host.g k : ℕ)) : ℝ) := by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos
    have := (Real.log_le_iff_le_exp hlo).2 ((hF.1.2.2.2.2.2.2.2.2 x hx ι).2.2.1 k)
    linarith
  refine hostNum_of_sizes (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) hg ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Fm.Ct_eq]; linarith [le_abs_self Fm.Ct]
  · rwa [hsL]
  · rwa [hsL]
  · rwa [hsx]
  · unfold Scale.b; rwa [hsL, hsx]
  · rwa [hsx, hsz]
  · rwa [hsx]

end GlobalTheory.CovTop.Sizes

end
