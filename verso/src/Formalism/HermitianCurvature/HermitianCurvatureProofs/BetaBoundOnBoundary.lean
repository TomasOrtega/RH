import Formalism.HermitianCurvature.StatementSz
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CriticalThresholdLowerBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaFactorisation

namespace Formalism.FourierDecayAlt.P.Sz7

open Finset Formalism.FourierDecayAlt.Sz

/- English proof (translation)
Unfold `Cfg.vthp`. Use `split_ifs with ht`. Take `⟨h1, _⟩` from `h.htop ht`. Establish `hb1 : (1:ℝ) ≤ c.b 1` using `h.hb1`. Establish `hbp : 0 < c.bp` using `by linarith`.

Establish `hD : (1:ℝ) ≤ c.Del` using `h.hDel`. Conclude with `div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by linarith)) hbp.le`. Conclude with `le_refl _`.
-/
private lemma vthp_nonneg_of_ok (c : Cfg) (h : c.Ok) : 0 ≤ c.vthp := by
  unfold Cfg.vthp
  split_ifs with ht
  · obtain ⟨h1, _⟩ := h.htop ht
    have hb1 : (1:ℝ) ≤ c.b 1 := h.hb1
    have hbp : 0 < c.bp := by linarith
    have hD : (1:ℝ) ≤ c.Del := h.hDel
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by linarith)) hbp.le
  · exact le_refl _

/- English proof (translation)
Unfold `Cfg.vthp`. Use `split_ifs with ht`. Take `⟨h1, _⟩` from `h.htop ht`. Establish `hb1 : (1:ℝ) ≤ c.b 1` using `h.hb1`. Establish `hbp : 0 < c.bp` using `by linarith`.

Establish `hm : (2:ℝ) ≤ c.m` using `by exact_mod_cast h.hm`. Establish `hk : (0:ℝ) ≤ c.k` using `Nat.cast_nonneg _`. Establish `hD : (1:ℝ) ≤ c.Del` using `h.hDel`. Establish `hv` using `hs.hvth`. Unfold `Cfg.vth at hv`.

Rewrite `hv` using `[div_le_iff₀ (by linarith)]`. Rewrite using `[div_le_iff₀ hbp]`. Establish `hkD : 0 ≤ (c.k:ℝ) * c.Del` using `mul_nonneg hk (by linarith)`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hm hkD]`. Evaluate the numerical expressions.
-/
private lemma vthp_le_one_tenth_of_small (c : Cfg) (h : c.Ok) (bb : ℝ) (hs : c.Small bb) : c.vthp ≤ 1 / 10 := by
  unfold Cfg.vthp
  split_ifs with ht
  · obtain ⟨h1, _⟩ := h.htop ht
    have hb1 : (1:ℝ) ≤ c.b 1 := h.hb1
    have hbp : 0 < c.bp := by linarith
    have hm : (2:ℝ) ≤ c.m := by exact_mod_cast h.hm
    have hk : (0:ℝ) ≤ c.k := Nat.cast_nonneg _
    have hD : (1:ℝ) ≤ c.Del := h.hDel
    have hv := hs.hvth
    unfold Cfg.vth at hv
    rw [div_le_iff₀ (by linarith)] at hv
    rw [div_le_iff₀ hbp]
    have hkD : 0 ≤ (c.k:ℝ) * c.Del := mul_nonneg hk (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hm hkD]
  · norm_num

/- English proof (translation)
Introduce `c bb h hs`. Establish `hv0` using `vthp_nonneg_of_ok c h`. Establish `hv1` using `vthp_le_one_tenth_of_small c h bb hs`. Establish `hW : 0 < 1 + c.vthp` using `by linarith`. Establish `hE2 : (9:ℝ) / 10 ≤ Real.exp (-(2 * c.m * Real.log bb / c.k))`.

Use `Real.add_one_le_exp (-(2 * c.m * Real.log bb / c.k))` as an intermediate fact. Combine the linear relations using `[hs.hmu]`. Establish `hE1 : Real.exp c.vth ≤ 10 / 9`. Establish `h1` using `Real.add_one_le_exp (-c.vth)`. Establish `h2 : Real.exp c.vth * Real.exp (-c.vth) = 1` using `by rw [← Real.exp_add]; simp`.

Establish `h3` using `Real.exp_pos c.vth`. Establish `h4` using `hs.hvth`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h1 h3.le, mul_nonneg h3.le (by linarith : (0:ℝ) ≤ 1 / 10 - c.vth)]`. Establish `hS : Real.sqrt (14 / 5) ≤ 1.6734`. Use polynomial arithmetic with `[Real.sq_sqrt (show (0:ℝ) ≤ 14 / 5 by norm_num), Real.sqrt_nonneg (14 / 5)]`.

Establish `hSE : Real.sqrt (14 / 5) * Real.exp c.vth ≤ 1.6734 * (10 / 9)` using `mul_le_mul hS hE1 (Real.exp_pos _).le (by norm_num)`. Establish `hcOne : 0 < cOne c bb`. Unfold `cOne`. Conclude with `div_pos (by positivity) hW`. Establish `hcLow : 0.38 * (9 / 10) / (11 / 10) ≤ cOne c bb`.

Unfold `cOne`. Rewrite using `[le_div_iff₀ hW]`. Establish `: 0.38 * (9 / 10) / (11 / 10) * (1 + c.vthp) ≤ 0.38 * (9 / 10)`. Establish `: (1 + c.vthp) ≤ 11 / 10` using `by linarith`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `AZero`. Conclude with `div_pos (by positivity) hcOne`. Unfold `AZero`.

Rewrite using `[div_le_iff₀ hcOne]`. Use polynomial arithmetic with `[hSE, hcLow]`.
-/
theorem aZeroBound : AZeroBound := by
  intro c bb h hs
  have hv0 := vthp_nonneg_of_ok c h
  have hv1 := vthp_le_one_tenth_of_small c h bb hs
  have hW : 0 < 1 + c.vthp := by linarith
  have hE2 : (9:ℝ) / 10 ≤ Real.exp (-(2 * c.m * Real.log bb / c.k)) := by
    have := Real.add_one_le_exp (-(2 * c.m * Real.log bb / c.k))
    linarith [hs.hmu]
  have hE1 : Real.exp c.vth ≤ 10 / 9 := by
    have h1 := Real.add_one_le_exp (-c.vth)
    have h2 : Real.exp c.vth * Real.exp (-c.vth) = 1 := by rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos c.vth
    have h4 := hs.hvth
    nlinarith [mul_le_mul_of_nonneg_left h1 h3.le, mul_nonneg h3.le (by linarith : (0:ℝ) ≤ 1 / 10 - c.vth)]
  have hS : Real.sqrt (14 / 5) ≤ 1.6734 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 14 / 5 by norm_num), Real.sqrt_nonneg (14 / 5)]
  have hSE : Real.sqrt (14 / 5) * Real.exp c.vth ≤ 1.6734 * (10 / 9) :=
    mul_le_mul hS hE1 (Real.exp_pos _).le (by norm_num)
  have hcOne : 0 < cOne c bb := by
    unfold cOne
    exact div_pos (by positivity) hW
  have hcLow : 0.38 * (9 / 10) / (11 / 10) ≤ cOne c bb := by
    unfold cOne
    rw [le_div_iff₀ hW]
    have : 0.38 * (9 / 10) / (11 / 10) * (1 + c.vthp) ≤ 0.38 * (9 / 10) := by
      have : (1 + c.vthp) ≤ 11 / 10 := by linarith
      nlinarith
    linarith
  refine ⟨?_, ?_⟩
  · unfold AZero
    exact div_pos (by positivity) hcOne
  · unfold AZero
    rw [div_le_iff₀ hcOne]
    nlinarith [hSE, hcLow]

/- English proof (translation)
Unfold `Cfg.rho`. Use `split_ifs with ht`. Take `⟨h1, _⟩` from `h.htop ht.1`. Establish `hY' : 5 / 2 ≤ c.v l + Y ∧ c.v l + Y ≤ c.Del / 2` using `hY`. Establish `hD : (1:ℝ) ≤ c.Del` using `h.hDel`.

Establish `hb1 : (1:ℝ) ≤ c.b 1` using `h.hb1`. Establish `hv : 4 * c.Del ≤ c.v l`. Unfold `Cfg.v`. Establish `hkl : (l:ℝ) + 2 ≤ c.k` using `by exact_mod_cast hlk`. Use polynomial arithmetic with `[h.hv0, mul_nonneg (by linarith : (0:ℝ) ≤ c.Del) (by linarith : (0:ℝ) ≤ (c.k:ℝ) - 2 - l)]`.

Conclude with `div_nonneg (Real.sqrt_nonneg _) (by linarith [hY'.2])`. Conclude with `div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)`.
-/
lemma rho_nonneg (c : Cfg) (de de' : ℕ → ℝ) (Y : ℝ) (l i : ℕ) (h : c.Ok)
    (hlk : l + 2 ≤ c.k) (hY : Y ∈ c.cutI l) : 0 ≤ c.rho de de' (-Y) i := by
  unfold Cfg.rho
  split_ifs with ht
  · obtain ⟨h1, _⟩ := h.htop ht.1
    have hY' : 5 / 2 ≤ c.v l + Y ∧ c.v l + Y ≤ c.Del / 2 := hY
    have hD : (1:ℝ) ≤ c.Del := h.hDel
    have hb1 : (1:ℝ) ≤ c.b 1 := h.hb1
    have hv : 4 * c.Del ≤ c.v l := by
      unfold Cfg.v
      have hkl : (l:ℝ) + 2 ≤ c.k := by exact_mod_cast hlk
      nlinarith [h.hv0, mul_nonneg (by linarith : (0:ℝ) ≤ c.Del) (by linarith : (0:ℝ) ≤ (c.k:ℝ) - 2 - l)]
    exact div_nonneg (Real.sqrt_nonneg _) (by linarith [hY'.2])
  · exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro h1`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`.

Introduce `h1 h2`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Simplify using `using h.hb1`. Establish `e1` using `ih hn (by omega)`.

Establish `e2` using `h.hgap n hn (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma one_le_b_of_ok (c : Cfg) (h : c.Ok) : ∀ j : ℕ, 1 ≤ j → j ≤ c.m → 1 ≤ c.b j := by
  intro j
  induction j with
  | zero => intro h1; omega
  | succ n ih =>
    intro h1 h2
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simpa using h.hb1
    · have e1 := ih hn (by omega)
      have e2 := h.hgap n hn (by omega)
      linarith

/- English proof (translation)
Unfold `Cfg.prodb`. Conclude with `Finset.prod_pos (fun j hj => by`. Rewrite `hj` using `[Finset.mem_Icc]`. Combine the linear relations using `[one_le_b_of_ok c h j hj.1 hj.2])`.
-/
lemma prodb_pos (c : Cfg) (h : c.Ok) : 0 < c.prodb := by
  unfold Cfg.prodb
  exact Finset.prod_pos (fun j hj => by
    rw [Finset.mem_Icc] at hj
    linarith [one_le_b_of_ok c h j hj.1 hj.2])

/- English proof (translation)
Take `⟨hU0, hU1, hU2⟩` from `edgeFactorBound c Y l h hl hlk hY`. Establish `hr0` using `rho_nonneg c de de' Y l (c.k - 1) h hlk hY`. Establish `hD : (1:ℝ) ≤ c.Del` using `h.hDel`. Establish `hkR : (4:ℝ) ≤ c.k` using `by exact_mod_cast h.hk`. Establish `hv1 : 0 ≤ c.v 1`.

Unfold `Cfg.v`. Use `push_cast`. Use polynomial arithmetic with `[h.hv0, mul_nonneg (by linarith : (0:ℝ) ≤ c.Del) (by linarith : (0:ℝ) ≤ (c.k:ℝ) - 2)]`. Establish `ha : 4 * c.k * c.Del ≤ c.a - c.v 1` using `h.ha`. Establish `h4 : 0 < 4 * (c.k:ℝ) * c.Del` using `mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)`.

Establish `hapos : 0 < c.a - c.v 1` using `by linarith`. Establish `hapos' : 0 < c.a` using `by linarith`. Consider the cases of `htop : c.top`. Establish `haeff : c.aeff = c.a - c.v 1` using `by simp [Cfg.aeff, htop]`. Rewrite using `[haeff]`.

Use `⟨hapos, ?_⟩` and prove the remaining obligations. Establish `hr1` using `positionAfter c de de' Y l (c.k - 1) h hw hw' hl (by omega) (by omega) (Or.inr htop) hY`. Establish `hx : 0 < 1 / (c.a - c.v 1)` using `one_div_pos.mpr hapos`. Establish `e : 8 / (c.a - c.v 1) = 8 * (1 / (c.a - c.v 1))` using `by ring`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨hbp1, _⟩` from `h.htop htop`. Establish `hb1 : (1:ℝ) ≤ c.b 1` using `h.hb1`. Establish `hbp : 0 < c.bp` using `by linarith`. Establish `hk0 : (c.k:ℝ) ≠ 0` using `(by linarith : (0:ℝ) < c.k).ne'`. Establish `hD0 : c.Del ≠ 0` using `(by linarith : (0:ℝ) < c.Del).ne'`.

Establish `hkD : 0 < (c.k:ℝ) * c.Del` using `mul_pos (by linarith) (by linarith)`. Establish `haeff : c.aeff = c.a * c.bp / (c.k * c.Del)` using `by simp [Cfg.aeff, htop]`. Rewrite using `[haeff]`. Use `⟨div_pos (mul_pos hapos' hbp) hkD, ?_⟩` and prove the remaining obligations. Establish `hr1` using `positionTop c de de' Y l h htop hl hlk hY`.

Establish `ha0` using `hapos'.ne'`. Establish `hb0` using `hbp.ne'`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma edge_bound (c : Cfg) (de de' : ℕ → ℝ) (Y : ℝ) (l : ℕ) (h : c.Ok) (hw : IsWord c.k de)
    (hw' : IsWord c.k de') (hl : 1 ≤ l) (hlk : l + 2 ≤ c.k) (hY : Y ∈ c.cutI l) :
    0 < c.aeff ∧ c.U1 (-Y) * c.rho de de' (-Y) (c.k - 1) ≤ 8 / c.aeff := by
  obtain ⟨hU0, hU1, hU2⟩ := edgeFactorBound c Y l h hl hlk hY
  have hr0 := rho_nonneg c de de' Y l (c.k - 1) h hlk hY
  have hD : (1:ℝ) ≤ c.Del := h.hDel
  have hkR : (4:ℝ) ≤ c.k := by exact_mod_cast h.hk
  have hv1 : 0 ≤ c.v 1 := by
    unfold Cfg.v
    push_cast
    nlinarith [h.hv0, mul_nonneg (by linarith : (0:ℝ) ≤ c.Del) (by linarith : (0:ℝ) ≤ (c.k:ℝ) - 2)]
  have ha : 4 * c.k * c.Del ≤ c.a - c.v 1 := h.ha
  have h4 : 0 < 4 * (c.k:ℝ) * c.Del := mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hapos : 0 < c.a - c.v 1 := by linarith
  have hapos' : 0 < c.a := by linarith
  cases htop : c.top
  · have haeff : c.aeff = c.a - c.v 1 := by simp [Cfg.aeff, htop]
    rw [haeff]
    refine ⟨hapos, ?_⟩
    have hr1 := positionAfter c de de' Y l (c.k - 1) h hw hw' hl (by omega) (by omega)
      (Or.inr htop) hY
    have hx : 0 < 1 / (c.a - c.v 1) := one_div_pos.mpr hapos
    have e : 8 / (c.a - c.v 1) = 8 * (1 / (c.a - c.v 1)) := by ring
    calc c.U1 (-Y) * c.rho de de' (-Y) (c.k - 1) ≤ (1 / (c.a - c.v 1)) * 1 :=
          mul_le_mul hU1 hr1 hr0 hx.le
      _ ≤ 8 / (c.a - c.v 1) := by rw [e]; linarith
  · obtain ⟨hbp1, _⟩ := h.htop htop
    have hb1 : (1:ℝ) ≤ c.b 1 := h.hb1
    have hbp : 0 < c.bp := by linarith
    have hk0 : (c.k:ℝ) ≠ 0 := (by linarith : (0:ℝ) < c.k).ne'
    have hD0 : c.Del ≠ 0 := (by linarith : (0:ℝ) < c.Del).ne'
    have hkD : 0 < (c.k:ℝ) * c.Del := mul_pos (by linarith) (by linarith)
    have haeff : c.aeff = c.a * c.bp / (c.k * c.Del) := by simp [Cfg.aeff, htop]
    rw [haeff]
    refine ⟨div_pos (mul_pos hapos' hbp) hkD, ?_⟩
    have hr1 := positionTop c de de' Y l h htop hl hlk hY
    have ha0 := hapos'.ne'
    have hb0 := hbp.ne'
    calc c.U1 (-Y) * c.rho de de' (-Y) (c.k - 1) ≤ (2 / c.a) * (4 * c.k * c.Del / c.bp) :=
          mul_le_mul (hU1.trans hU2) hr1 hr0 (div_nonneg (by norm_num) hapos'.le)
      _ = 8 / (c.a * c.bp / (c.k * c.Del)) := by
          field_simp
          ring

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, k = n + 1` from `⟨k - 1, by omega⟩`. Establish `e1 : n + 1 - 1 = n` using `by omega`. Rewrite using `[e1]`. Establish `e2 : Icc 1 n = Ico 1 (n + 1)`. Use extensionality with `x`.

Simplify using `only [Finset.mem_Icc, Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e2, ← Finset.prod_Ico_consecutive f hl (by omega : l ≤ n + 1), Finset.prod_eq_prod_Ico_succ_bot (by omega : l < n + 1), Finset.prod_Ico_succ_top (by omega : l + 1 ≤ n)]`.
-/
lemma prod_split (f : ℕ → ℝ) (k l : ℕ) (hl : 1 ≤ l) (hlk : l + 2 ≤ k) :
    ∏ i ∈ Icc 1 (k - 1), f i =
      (∏ i ∈ Ico 1 l, f i) * (f l * ((∏ i ∈ Ico (l + 1) (k - 1), f i) * f (k - 1))) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have e1 : n + 1 - 1 = n := by omega
  rw [e1]
  have e2 : Icc 1 n = Ico 1 (n + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [e2, ← Finset.prod_Ico_consecutive f hl (by omega : l ≤ n + 1),
    Finset.prod_eq_prod_Ico_succ_bot (by omega : l < n + 1),
    Finset.prod_Ico_succ_top (by omega : l + 1 ≤ n)]

/- English proof (translation)
Introduce `c r bb de de' ka rd g VV T T' Y l h hm hs hw hw' hrd hka hg hFD hT hT' hl hlk hne hY`. Establish `hka0 : 0 < ka` using `by rw [hka]; exact div_pos (by positivity) (by linarith)`. Establish `hg0 : 0 < g` using `by linarith [Real.pi_pos]`. Establish `hA : 0 < (ka ^ (c.m - 1))⁻¹` using `inv_pos.mpr (pow_pos hka0 _)`. Establish `hB : 0 < (Real.sqrt (T * T'))⁻¹` using `inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos hT hT'))`.

Establish `hgm : 0 < g ^ c.m` using `pow_pos hg0 _`. Take `⟨haeff, hUR⟩` from `edge_bound c de de' Y l h hw hw' hl hlk hY`. Establish `hP` using `prodb_pos c h`. Establish `hv0` using `vthp_nonneg_of_ok c h`. Establish `hcOne : 0 < cOne c bb`.

Unfold `cOne`. Conclude with `div_pos (by positivity) (by linarith)`. Establish `hfac` using `(betaFactorisation c de de' ka T T' Y l h hw hw' hT hT' hl hlk hne hY).2.2.2`. Establish `hsplit` using `prod_split (c.rho de de' (-Y)) c.k l hl hlk`. Establish `hR0` using `positionsBefore c de de' Y l h hw hw' hl hlk hY`.

Establish `hRl` using `(slotAt_true c de de' Y l h hw hw' hl hlk hne hY).2`. Establish `hN` using `nodeBound c Y l h hl hlk hY`. Establish `hRm : ∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i ≤ 1` using `Finset.prod_le_one (fun i _ => rho_nonneg c de de' Y l i h hlk hY) (fun i hi => by`. Rewrite `hi` using `[Finset.mem_Ico]`. Conclude with `positionAfter c de de' Y l i h hw hw' hl (by omega) (by omega) (Or.inl (by omega)) hY)`.

Establish `hR00 : 0 ≤ ∏ i ∈ Ico 1 l, c.rho de de' (-Y) i` using `Finset.prod_nonneg (fun i _ => rho_nonneg c de de' Y l i h hlk hY)`. Establish `hRm0 : 0 ≤ ∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i` using `Finset.prod_nonneg (fun i _ => rho_nonneg c de de' Y l i h hlk hY)`. Establish `hRl0` using `rho_nonneg c de de' Y l l h hlk hY`. Establish `hRk0` using `rho_nonneg c de de' Y l (c.k - 1) h hlk hY`. Establish `hN0 : 0 ≤ c.Nd (-Y)`.

Unfold `Cfg.Nd`. Conclude with `Finset.prod_nonneg (fun j _ => Real.sqrt_nonneg _)`. Establish `hU0 : 0 < c.U1 (-Y)` using `(edgeFactorBound c Y l h hl hlk hY).1`. Establish `hsq : Real.sqrt (14 * (c.v l + Y) / (5 * c.Del)) = Real.sqrt (14 / 5) * Real.sqrt ((c.v l + Y) / c.Del)`. Rewrite using `[← Real.sqrt_mul (show (0:ℝ) ≤ 14 / 5 by norm_num) ((c.v l + Y) / c.Del)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hRl` using `[hsq]`. Establish `hT1` using `HT c r bb de ka rd g VV h hm hs hw hrd hka hg hFD`. Establish `hT2` using `HT c r bb de' ka rd g VV h hm hs hw' hrd hka hg hFD`.

Establish `hQ0 : 0 < cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff` using `div_pos (mul_pos (mul_pos (mul_pos hcOne hgm) hA) hP) haeff`. Establish `htv : cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff * (Real.sqrt (T * T'))⁻¹ ≤ tv c de de' ka rd g VV T T'`. Unfold `tv`. Rewrite using `[Real.le_sqrt' (mul_pos hQ0 hB), mul_pow, inv_pow, Real.sq_sqrt (mul_pos hT hT').le, div_eq_mul_inv (Tcrit c.k c.m ka rd g VV (Vand c.k (c.u de)) * Tcrit c.k c.m ka rd g VV (Vand c.k (c.u de')))]`. Use `mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (mul_pos hT hT').le)` and prove the remaining obligations.

Rewrite using `[pow_two]`. Conclude with `mul_le_mul hT1 hT2 hQ0.le (hQ0.le.trans hT1)`. Establish `hEP : 0 < Real.exp c.vth * c.prodb` using `mul_pos (Real.exp_pos _) hP`. Establish `hsk : 0 ≤ Real.sqrt c.k` using `Real.sqrt_nonneg _`. Establish `hsx : 0 ≤ Real.sqrt ((c.v l + Y) / c.Del)` using `Real.sqrt_nonneg _`.

Establish `hs5 : 0 ≤ Real.sqrt (14 / 5)` using `Real.sqrt_nonneg _`. Establish `b1` using `mul_le_mul hN hR0 hR00 hEP.le`. Establish `b2` using `mul_le_mul b1 hRl hRl0 (mul_nonneg hEP.le (mul_nonneg (by norm_num) hsk))`. Establish `b3` using `mul_le_mul b2 hRm hRm0 (mul_nonneg (mul_nonneg hEP.le (mul_nonneg (by norm_num) hsk)) (mul_nonneg hs5 hsx))`. Establish `b4` using `mul_le_mul b3 hUR (mul_nonneg hU0.le hRk0) (mul_nonneg (mul_nonneg (mul_nonneg hEP.le (mul_nonneg (by norm_num) hsk)) (mul_nonneg hs5 hsx)) (by norm_num))`.

Establish `hK : 0 ≤ g ^ c.m * (ka ^ (c.m - 1))⁻¹ * (Real.sqrt (T * T'))⁻¹` using `(mul_pos (mul_pos hgm hA) hB).le`. Establish `hAZ : 0 ≤ 8 * 3.3 * Real.sqrt (14 / 5) * Real.exp c.vth / cOne c bb` using `div_nonneg (by positivity) hcOne.le`. Establish `hae` using `haeff.ne'`. Establish `hco` using `hcOne.ne'`. Rewrite using `[hfac, hsplit]`.

Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ 8 * 3.3 * Real.sqrt (14 / 5) * Real.exp c.vth / cOne c bb * tv c de de' ka rd g VV T T' * Real.sqrt c.k * Real.sqrt ((c.v l + Y) / c.Del) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htv hAZ) hsk) hsx`. Use `_ = AZero c bb * tv c de de' ka rd g VV T T' * Real.sqrt c.k * Real.sqrt ((c.v l + Y) / c.Del) := rfl`.
-/
theorem betaOnCut_of_tcritLower (HT : TcritLower) : BetaOnCut := by
  intro c r bb de de' ka rd g VV T T' Y l h hm hs hw hw' hrd hka hg hFD hT hT' hl hlk hne hY
  have hka0 : 0 < ka := by rw [hka]; exact div_pos (by positivity) (by linarith)
  have hg0 : 0 < g := by linarith [Real.pi_pos]
  have hA : 0 < (ka ^ (c.m - 1))⁻¹ := inv_pos.mpr (pow_pos hka0 _)
  have hB : 0 < (Real.sqrt (T * T'))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos hT hT'))
  have hgm : 0 < g ^ c.m := pow_pos hg0 _
  obtain ⟨haeff, hUR⟩ := edge_bound c de de' Y l h hw hw' hl hlk hY
  have hP := prodb_pos c h
  have hv0 := vthp_nonneg_of_ok c h
  have hcOne : 0 < cOne c bb := by
    unfold cOne
    exact div_pos (by positivity) (by linarith)
  have hfac := (betaFactorisation c de de' ka T T' Y l h hw hw' hT hT' hl hlk hne hY).2.2.2
  have hsplit := prod_split (c.rho de de' (-Y)) c.k l hl hlk
  have hR0 := positionsBefore c de de' Y l h hw hw' hl hlk hY
  have hRl := (slotAt_true c de de' Y l h hw hw' hl hlk hne hY).2
  have hN := nodeBound c Y l h hl hlk hY
  have hRm : ∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i ≤ 1 :=
    Finset.prod_le_one (fun i _ => rho_nonneg c de de' Y l i h hlk hY)
      (fun i hi => by
        rw [Finset.mem_Ico] at hi
        exact positionAfter c de de' Y l i h hw hw' hl (by omega) (by omega)
          (Or.inl (by omega)) hY)
  have hR00 : 0 ≤ ∏ i ∈ Ico 1 l, c.rho de de' (-Y) i :=
    Finset.prod_nonneg (fun i _ => rho_nonneg c de de' Y l i h hlk hY)
  have hRm0 : 0 ≤ ∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i :=
    Finset.prod_nonneg (fun i _ => rho_nonneg c de de' Y l i h hlk hY)
  have hRl0 := rho_nonneg c de de' Y l l h hlk hY
  have hRk0 := rho_nonneg c de de' Y l (c.k - 1) h hlk hY
  have hN0 : 0 ≤ c.Nd (-Y) := by
    unfold Cfg.Nd
    exact Finset.prod_nonneg (fun j _ => Real.sqrt_nonneg _)
  have hU0 : 0 < c.U1 (-Y) := (edgeFactorBound c Y l h hl hlk hY).1
  have hsq : Real.sqrt (14 * (c.v l + Y) / (5 * c.Del)) =
      Real.sqrt (14 / 5) * Real.sqrt ((c.v l + Y) / c.Del) := by
    rw [← Real.sqrt_mul (show (0:ℝ) ≤ 14 / 5 by norm_num) ((c.v l + Y) / c.Del)]
    congr 1
    ring
  rw [hsq] at hRl
  have hT1 := HT c r bb de ka rd g VV h hm hs hw hrd hka hg hFD
  have hT2 := HT c r bb de' ka rd g VV h hm hs hw' hrd hka hg hFD
  have hQ0 : 0 < cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff :=
    div_pos (mul_pos (mul_pos (mul_pos hcOne hgm) hA) hP) haeff
  have htv : cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff *
      (Real.sqrt (T * T'))⁻¹ ≤ tv c de de' ka rd g VV T T' := by
    unfold tv
    rw [Real.le_sqrt' (mul_pos hQ0 hB), mul_pow, inv_pow, Real.sq_sqrt (mul_pos hT hT').le,
      div_eq_mul_inv (Tcrit c.k c.m ka rd g VV (Vand c.k (c.u de)) *
        Tcrit c.k c.m ka rd g VV (Vand c.k (c.u de')))]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (mul_pos hT hT').le)
    rw [pow_two]
    exact mul_le_mul hT1 hT2 hQ0.le (hQ0.le.trans hT1)
  have hEP : 0 < Real.exp c.vth * c.prodb := mul_pos (Real.exp_pos _) hP
  have hsk : 0 ≤ Real.sqrt c.k := Real.sqrt_nonneg _
  have hsx : 0 ≤ Real.sqrt ((c.v l + Y) / c.Del) := Real.sqrt_nonneg _
  have hs5 : 0 ≤ Real.sqrt (14 / 5) := Real.sqrt_nonneg _
  have b1 := mul_le_mul hN hR0 hR00 hEP.le
  have b2 := mul_le_mul b1 hRl hRl0 (mul_nonneg hEP.le (mul_nonneg (by norm_num) hsk))
  have b3 := mul_le_mul b2 hRm hRm0
    (mul_nonneg (mul_nonneg hEP.le (mul_nonneg (by norm_num) hsk)) (mul_nonneg hs5 hsx))
  have b4 := mul_le_mul b3 hUR (mul_nonneg hU0.le hRk0)
    (mul_nonneg (mul_nonneg (mul_nonneg hEP.le (mul_nonneg (by norm_num) hsk))
      (mul_nonneg hs5 hsx)) (by norm_num))
  have hK : 0 ≤ g ^ c.m * (ka ^ (c.m - 1))⁻¹ * (Real.sqrt (T * T'))⁻¹ :=
    (mul_pos (mul_pos hgm hA) hB).le
  have hAZ : 0 ≤ 8 * 3.3 * Real.sqrt (14 / 5) * Real.exp c.vth / cOne c bb :=
    div_nonneg (by positivity) hcOne.le
  have hae := haeff.ne'
  have hco := hcOne.ne'
  rw [hfac, hsplit]
  calc g ^ c.m * ((ka ^ (c.m - 1))⁻¹ * (Real.sqrt (T * T'))⁻¹ * c.Nd (-Y) * c.U1 (-Y) *
        ((∏ i ∈ Ico 1 l, c.rho de de' (-Y) i) * (c.rho de de' (-Y) l *
          ((∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i) * c.rho de de' (-Y) (c.k - 1)))))
      = g ^ c.m * (ka ^ (c.m - 1))⁻¹ * (Real.sqrt (T * T'))⁻¹ *
        (c.Nd (-Y) * (∏ i ∈ Ico 1 l, c.rho de de' (-Y) i) * c.rho de de' (-Y) l *
          (∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i) *
          (c.U1 (-Y) * c.rho de de' (-Y) (c.k - 1))) := by ring
    _ ≤ g ^ c.m * (ka ^ (c.m - 1))⁻¹ * (Real.sqrt (T * T'))⁻¹ *
        (Real.exp c.vth * c.prodb * (3.3 * Real.sqrt c.k) *
          (Real.sqrt (14 / 5) * Real.sqrt ((c.v l + Y) / c.Del)) * 1 * (8 / c.aeff)) :=
        mul_le_mul_of_nonneg_left b4 hK
    _ = 8 * 3.3 * Real.sqrt (14 / 5) * Real.exp c.vth / cOne c bb *
        (cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff * (Real.sqrt (T * T'))⁻¹) *
        Real.sqrt c.k * Real.sqrt ((c.v l + Y) / c.Del) := by
        field_simp
    _ ≤ 8 * 3.3 * Real.sqrt (14 / 5) * Real.exp c.vth / cOne c bb *
        tv c de de' ka rd g VV T T' * Real.sqrt c.k * Real.sqrt ((c.v l + Y) / c.Del) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htv hAZ) hsk) hsx
    _ = AZero c bb * tv c de de' ka rd g VV T T' * Real.sqrt c.k *
        Real.sqrt ((c.v l + Y) / c.Del) := rfl

end Formalism.FourierDecayAlt.P.Sz7

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `Sz7.aZeroBound`.
-/
theorem a_zero_le_one_sixty : Formalism.FourierDecayAlt.Sz.AZeroBound := Sz7.aZeroBound

/- English proof (translation)
The claim follows from `Sz7.betaOnCut_of_tcritLower critical_threshold_lower_bound`.
-/
theorem beta_bound_on_boundary : Formalism.FourierDecayAlt.Sz.BetaOnCut := Sz7.betaOnCut_of_tcritLower critical_threshold_lower_bound

end Formalism.FourierDecayAlt.P
