import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.SizeTZ

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

/- English proof (translation)
Establish `h1 : ∑ f : Lt1 Dw, 2 * GlobalTheory.FactorDepth.rk f ≤ Fintype.card (Lt1 Dw) * (2 * (Dw.p + Dw.q))`. Rewrite using `[← Finset.card_univ, ← smul_eq_mul]`. Use `Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_` and prove the remaining obligations. Establish `h` using `GlobalTheory.FactorDepth.rk_le f`. Establish `h' : Dw.mult f.1 ≤ Dw.p + Dw.q`.

Apply the tactic sequence `rw [Datum.mult]; split_ifs <;> omega`. Use linear arithmetic over natural numbers and integers. Establish `h2 : Fintype.card (Lt1 Dw) ≤ Module.finrank ℚ E * (Dw.p + Dw.q)` using `card_Lt1_le_finrank_mul`. Establish `h3` using `Nat.mul_le_mul_right (2 * (Dw.p + Dw.q)) h2`. Establish `h4` using `Nat.mul_div_le (∑ f : Lt1 Dw, 2 * GlobalTheory.FactorDepth.rk f) 8`.

Unfold `nCol`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nCol_le (Dw : Datum H) :
    nCol Dw ≤ (2 * (Dw.p + Dw.q) + 8) * (Module.finrank ℚ E * (Dw.p + Dw.q)) + 8 := by
  have h1 : ∑ f : Lt1 Dw, 2 * GlobalTheory.FactorDepth.rk f ≤ Fintype.card (Lt1 Dw) * (2 * (Dw.p + Dw.q)) := by
    rw [← Finset.card_univ, ← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_
    have h := GlobalTheory.FactorDepth.rk_le f
    have h' : Dw.mult f.1 ≤ Dw.p + Dw.q := by
      rw [Datum.mult]; split_ifs <;> omega
    omega
  have h2 : Fintype.card (Lt1 Dw) ≤ Module.finrank ℚ E * (Dw.p + Dw.q) := card_Lt1_le_finrank_mul
  have h3 := Nat.mul_le_mul_right (2 * (Dw.p + Dw.q)) h2
  have h4 := Nat.mul_div_le (∑ f : Lt1 Dw, 2 * GlobalTheory.FactorDepth.rk f) 8
  unfold nCol
  nlinarith

end Free

variable {D : D7}

/- English proof (translation)
Establish `: 0 < D.R.ord` using `D.R.ord_pos`. Use `show 2 ≤ 2 * D.R.ord`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_le_f (D : D7) : 2 ≤ D.R.f := by
  have : 0 < D.R.ord := D.R.ord_pos
  show 2 ≤ 2 * D.R.ord
  omega

/- English proof (translation)
Establish `h1` using `D.R.two_le_m`. Establish `h2` using `D.R.m_add_three_le_k`. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers.
-/
theorem six_le_r (D : D7) : 6 ≤ D.R.r := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  unfold Ranks.r; omega

/- English proof (translation)
The claim follows from `Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`.
-/
theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

/- English proof (translation)
Establish `hf : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast (by have := two_le_f D; omega : 1 ≤ D.R.f)`. Establish `hr : (1 : ℝ) ≤ D.R.r` using `by exact_mod_cast (by have := six_le_r D; omega : 1 ≤ D.R.r)`. Conclude with `one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hr) (one_le_scL L)`.
-/
theorem one_le_zBase (L : SizeData₂ D) : 1 ≤ zBase L := by
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by have := two_le_f D; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by have := six_le_r D; omega : 1 ≤ D.R.r)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hr) (one_le_scL L)

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

/- English proof (translation)
Establish `hZ` using `one_le_zBase L`. Establish `h1 : zBase L ^ 12 ≤ zBase L ^ T.eP`. Rewrite using `[← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hZ (by exact_mod_cast T.eP_ge)`. Rewrite using `[T.PP_eq]`.

Conclude with `h1.trans (le_mul_of_one_le_left (by positivity) T.one_le_CP)`.
-/
theorem pow_le_PP (T : ParamsT D L P) : zBase L ^ 12 ≤ T.PP := by
  have hZ := one_le_zBase L
  have h1 : zBase L ^ 12 ≤ zBase L ^ T.eP := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by exact_mod_cast T.eP_ge)
  rw [T.PP_eq]
  exact h1.trans (le_mul_of_one_le_left (by positivity) T.one_le_CP)

/- English proof (translation)
Use `Nat.ceil_le.2 (le_trans ?_ T.TO_ge)` and prove the remaining obligations. Establish `hPP : 1 ≤ T.PP` using `(one_le_pow₀ (one_le_zBase L)).trans (pow_le_PP T)`. Establish `hf : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast (by have := two_le_f D; omega : 1 ≤ D.R.f)`. Establish `hD : (1 : ℝ) ≤ T.Dp`. Establish `h1 : 0 < D.R.r.choose 2` using `Nat.choose_pos (by have := six_le_r D; omega)`.

Establish `h2 : 0 < T.Dp` using `by rw [T.Dp_eq]; exact Nat.mul_pos (by have := two_le_f D; omega) h1`. Conclude with `h2` after adjusting the coercions. Establish `hx : 1 ≤ L.sc.x ^ T.Cp` using `Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg`. Establish `hm : (0 : ℝ) < D.R.m` using `by exact_mod_cast (by have := D.R.two_le_m; omega : 0 < D.R.m)`. Establish `hd` using `L.thickDensity_pos`.

Use `div_le_div₀ (by positivity) ?_ (by positivity) (mul_le_of_le_one_right hm.le L.thickDensity_le_one)` and prove the remaining obligations. Establish `e : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp = T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) * (T.PP ^ 2 * T.Dp * D.R.f * L.sc.x ^ T.Cp)` using `by ring`. Rewrite using `[e]`. Conclude with `le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hPP) hD) hf) hx)`.
-/
theorem ceil_le_TO (T : ParamsT D L P) :
    ⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ ≤ T.TO := by
  refine Nat.ceil_le.2 (le_trans ?_ T.TO_ge)
  have hPP : 1 ≤ T.PP := (one_le_pow₀ (one_le_zBase L)).trans (pow_le_PP T)
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by have := two_le_f D; omega : 1 ≤ D.R.f)
  have hD : (1 : ℝ) ≤ T.Dp := by
    have h1 : 0 < D.R.r.choose 2 := Nat.choose_pos (by have := six_le_r D; omega)
    have h2 : 0 < T.Dp := by rw [T.Dp_eq]; exact Nat.mul_pos (by have := two_le_f D; omega) h1
    exact_mod_cast h2
  have hx : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 0 < D.R.m)
  have hd := L.thickDensity_pos
  refine div_le_div₀ (by positivity) ?_ (by positivity) (mul_le_of_le_one_right hm.le L.thickDensity_le_one)
  have e : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp =
      T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) * (T.PP ^ 2 * T.Dp * D.R.f * L.sc.x ^ T.Cp) := by ring
  rw [e]
  exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hPP) hD) hf) hx)

/- English proof (translation)
Establish `hb : 1 ≤ L.sc.b` using `Real.one_le_exp (zero_le_one.trans (one_le_scL L))`. Establish `hZ` using `one_le_zBase L`. Establish `h1 : (⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ) ≤ T.TO` using `by exact_mod_cast ceil_le_TO T`. Use `(mul_le_mul h1 (pow_le_PP T) (by positivity) (by positivity)).trans (T.TO_PP'.trans ?_)` and prove the remaining obligations. Conclude with `(Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans (Real.rpow_one _).le`.
-/
theorem ceil_mul_le_b (T : ParamsT D L P) :
    (⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ) * zBase L ^ 12 ≤ L.sc.b := by
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (zero_le_one.trans (one_le_scL L))
  have hZ := one_le_zBase L
  have h1 : (⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ) ≤ T.TO := by exact_mod_cast ceil_le_TO T
  refine (mul_le_mul h1 (pow_le_PP T) (by positivity) (by positivity)).trans (T.TO_PP'.trans ?_)
  exact (Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans (Real.rpow_one _).le

/- English proof (translation)
Establish `h` using `log_rdE_le_scL P`. Establish `e : lrd D.host.E = Real.log D.host.rdE`. Rewrite using `[lrd, rootDiscr_def, Formalism.BasicNotions.Host.rdE, one_div, Int.cast_abs]`. Use `one_le_scL L` as an intermediate fact. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lrd_le (P : ParameterChoice' D L) : lrd D.host.E ≤ 3 * L.sc.L := by
  have h := log_rdE_le_scL P
  have e : lrd D.host.E = Real.log D.host.rdE := by
    rw [lrd, rootDiscr_def, Formalism.BasicNotions.Host.rdE, one_div, Int.cast_abs]
  have := one_le_scL L
  rw [e]; linarith

/- English proof (translation)
Establish `hfr : Module.finrank ℚ D.host.E = 2 * D.R.f`. Rewrite using `[D.host.finrank_cmField]`. Unfold `Ranks.f Ranks.n`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `nCol_le (T.Dw j)`.

Rewrite `h1` using `[hfr, (GlobalTheory.SlopeRec.sig_eq h hj).2.2]`. Establish `hf` using `two_le_f D`. Establish `hr` using `six_le_r D`. Establish `h2 : nCol (T.Dw j) ≤ 20 * D.R.f * D.R.r ^ 2`. Use `h1.trans ?_` and prove the remaining obligations.

Generalize the expression as in `D.R.f = f at *`. Generalize the expression as in `D.R.r = r at *`. Establish `a1 : f * r * 6 ≤ f * r * r` using `Nat.mul_le_mul_left _ hr`. Establish `a2 : 2 * 6 ≤ f * r` using `Nat.mul_le_mul hf hr`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `h2` after adjusting the coercions.
-/
theorem nCol_le_of_pins {T : Par D} (h : T.Pins) {j : ℕ} (hj : InR D j) :
    (nCol (T.Dw j) : ℝ) ≤ 20 * D.R.f * (D.R.r : ℝ) ^ 2 := by
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have h1 := nCol_le (T.Dw j)
  rw [hfr, (GlobalTheory.SlopeRec.sig_eq h hj).2.2] at h1
  have hf := two_le_f D
  have hr := six_le_r D
  have h2 : nCol (T.Dw j) ≤ 20 * D.R.f * D.R.r ^ 2 := by
    refine h1.trans ?_
    generalize D.R.f = f at *
    generalize D.R.r = r at *
    have a1 : f * r * 6 ≤ f * r * r := Nat.mul_le_mul_left _ hr
    have a2 : 2 * 6 ≤ f * r := Nat.mul_le_mul hf hr
    nlinarith
  exact_mod_cast h2

/- English proof (translation)
Establish `hj : InR D ((i : ℕ) + 1)` using `⟨Nat.le_add_left _ _, i.2⟩`. Establish `hpin : p.T.Q.Pins` using `p.fw.laws.pins`. Establish `hD : GlobalTheory.CompHt.dimFlag (dat p i) = T.Dp`. Rewrite using `[T.Dp_eq]`. Use `(GlobalTheory.SlopeRec.dimFlag_eq hpin hj).trans ?_` and prove the remaining obligations.

Simplify using `only [placeRankTwoOne.dimY, Nat.choose_two_right]`. Use `⟨?_, nCol_le_of_pins hpin hj⟩` and prove the remaining obligations. Rewrite using `[lenT, hD]`. Conclude with `ceil_mul_le_b T`.
-/
theorem lenT_mul_le_b {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
    (T : ParamsT D L P) :
    (lenT p i T.PP : ℝ) * zBase L ^ 12 ≤ L.sc.b ∧ (nCol (dat p i) : ℝ) ≤ 20 * D.R.f * (D.R.r : ℝ) ^ 2 := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hpin : p.T.Q.Pins := p.fw.laws.pins
  have hD : GlobalTheory.CompHt.dimFlag (dat p i) = T.Dp := by
    rw [T.Dp_eq]
    refine (GlobalTheory.SlopeRec.dimFlag_eq hpin hj).trans ?_
    simp only [placeRankTwoOne.dimY, Nat.choose_two_right]
  refine ⟨?_, nCol_le_of_pins hpin hj⟩
  rw [lenT, hD]
  exact ceil_mul_le_b T

/- English proof (translation)
Introduce `h` and use `Closed.imp h fun Fm _ _ ⟨C, h0, a, h⟩ => ⟨C, h0, a, fun x hx hle ι p hp i => ⟨(lenT_mul_le_b p i (Fm.parT x hx ι)).1.trans (h x hx hle ι p hp i).2.1, one_le_scL _, lrd_le (Fm.params x hx ι), (lenT_mul_le_b p i (Fm.parT x hx ι)).2, le_trans one_le_two (two_le_f _), le_trans (by no …`.
-/
theorem sizes : Size → Lifts fun Fm x _ ι p i PP _ => (lenT p i PP : ℝ) * zBase (Fm.L x ι) ^ 12 ≤ unitE p ∧ 1 ≤ (Fm.L x ι).sc.L ∧ lrd (Fm.D x ι).host.E ≤ 3 * (Fm.L x ι).sc.L ∧ (nCol (dat p i) : ℝ) ≤ 20 * (Fm.D x ι).R.f * (Fm.D x ι).R.r ^ 2 ∧ 1 ≤ (Fm.D x ι).R.f ∧ 1 ≤ (Fm.D x ι).R.r := fun h =>
  Closed.imp h fun Fm _ _ ⟨C, h0, a, h⟩ => ⟨C, h0, a, fun x hx hle ι p hp i =>
    ⟨(lenT_mul_le_b p i (Fm.parT x hx ι)).1.trans (h x hx hle ι p hp i).2.1, one_le_scL _, lrd_le (Fm.params x hx ι),
      (lenT_mul_le_b p i (Fm.parT x hx ι)).2,
      le_trans one_le_two (two_le_f _), le_trans (by norm_num) (six_le_r _)⟩⟩

end GlobalTheory.RefSum.SizeTZ

end
