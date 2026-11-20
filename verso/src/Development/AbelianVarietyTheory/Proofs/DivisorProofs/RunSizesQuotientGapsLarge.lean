import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp

namespace GlobalTheory.RunSizes

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Use `set d := f * (r * (r - 1) / 2) with hd`. Establish `hr1 : 5 ≤ r - 1` using `by linarith`. Establish `hrr : 5 * r ≤ r * (r - 1)` using `by nlinarith`. Establish `hd5 : 5 * r ≤ d` using `by rw [hd]; nlinarith`. Establish `hd30 : 30 ≤ d` using `by linarith`.

Establish `hdr2 : d ≤ f * r ^ 2 / 2` using `by rw [hd]; nlinarith`. Establish `hPP1 : 1 ≤ PP` using `by nlinarith`. Establish `hkm' : 1 ≤ k / m` using `(one_le_div hm).2 hkm`. Use `set A := PP ^ 2 * d ^ 2 * k / m with hA`. Establish `hA' : A = PP ^ 2 * d ^ 2 * (k / m)` using `by rw [hA]; ring`.

Establish `hPP2 : 1 ≤ PP ^ 2` using `by nlinarith`. Establish `hAd : d ^ 2 ≤ A`. Rewrite using `[hA']`. Establish `h0 : 0 ≤ d ^ 2` using `by positivity`. Establish `: d ^ 2 ≤ PP ^ 2 * d ^ 2` using `by nlinarith`.

Combine the equalities or inequalities in the displayed calculation. Establish `hTO' : PP ^ 2 * d * A ≤ TO`. Establish `: PP ^ 4 * d ^ 3 * k / m = PP ^ 2 * d * A` using `by rw [hA]; ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hG : (d + 3) * ((d + 1) * d / 2 + 4 * r + d + 3) ≤ d ^ 3` using `by nlinarith`.

Establish `hT2 : T + d + 1 ≤ 2 * A` using `by nlinarith`. Establish `hGnn : 0 ≤ (d + 3) * ((d + 1) * d / 2 + 4 * r + d + 3)`. Establish `: 0 ≤ r` using `by linarith`. Check the signs of the components of the expression. Establish `h3d : 3 * d ^ 2 ≤ PP ^ 2` using `by nlinarith`.

Establish `hA0 : 0 ≤ A` using `by nlinarith`. Establish `hd1 : d + 1 ≤ d ^ 2` using `by nlinarith`. Use `⟨?_, ?_, by linarith⟩` and prove the remaining obligations. Establish `h1 : (d + 3) * ((d + 1) * d / 2 + 4 * r + d + 3) * (T + d + 1) ≤ d ^ 3 * (2 * A)` using `mul_le_mul hG hT2 (by linarith) (by positivity)`. Establish `h4 : 4 ≤ d ^ 3 * A` using `by nlinarith`.

Establish `h2 : d ^ 3 * (2 * A) + 4 ≤ PP ^ 2 * d * A`. Establish `: 3 * d ^ 2 * (d * A) ≤ PP ^ 2 * (d * A)`. Apply `mul_le_mul_of_nonneg_right h3d` to reduce the goal to its premises. Check the signs of the components of the expression. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hP2 : (f * r ^ 2) ^ 2 ≤ PP ^ 2`. Apply `pow_le_pow_left₀ (by positivity) hPP` to reduce the goal to its premises. Establish `hd900 : (30 : ℝ) ^ 2 ≤ d ^ 2` using `pow_le_pow_left₀ (by norm_num) hd30 2`. Establish `hA1 : 1 ≤ A` using `by linarith`.

Establish `hdA : 30 ≤ d * A`. Combine the equalities or inequalities in the displayed calculation. Establish `hr4 : r * 216 ≤ r ^ 4`. Establish `h3 : (6 : ℝ) ^ 3 ≤ r ^ 3` using `pow_le_pow_left₀ (by norm_num) hr 3`. Establish `: r ^ 4 = r * r ^ 3` using `by ring`.

Rewrite using `[this]`. Establish `h216 : (216 : ℝ) ≤ r ^ 3` using `by norm_num at h3; linarith`. Establish `hr0 : (0 : ℝ) ≤ r` using `by linarith`. Conclude with `mul_le_mul_of_nonneg_left h216 hr0`. Establish `hf2 : (2 : ℝ) ^ 2 ≤ f ^ 2` using `pow_le_pow_left₀ (by norm_num) hf 2`.

Evaluate the numerical expressions using `at hf2`. Establish `hfr : 2 * r + 1 ≤ f ^ 2 * r ^ 4`. Establish `: 4 * (r * 216) ≤ f ^ 2 * r ^ 4` using `mul_le_mul hf2 hr4 (by positivity) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h30 : (f * r ^ 2) ^ 2 * 30 ≤ PP ^ 2 * (d * A)`.

Apply `mul_le_mul hP2 hdA (by norm_num) (by positivity)` to reduce the goal to its premises. Establish `e1 : (f * r ^ 2) ^ 2 = f ^ 2 * r ^ 4` using `by ring`. Establish `e2 : PP ^ 2 * (d * A) = PP ^ 2 * d * A` using `by ring`. Rewrite `h30` using `[e1, e2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem core (f r k m PP TO T : ℝ) (hf : 2 ≤ f) (hr : 6 ≤ r) (hm : 0 < m) (hkm : m ≤ k)
    (hPP : f * r ^ 2 ≤ PP) (hTO : PP ^ 4 * (f * (r * (r - 1) / 2)) ^ 3 * k / m ≤ TO) (hT0 : 0 ≤ T)
    (hT : T ≤ PP ^ 2 * (f * (r * (r - 1) / 2)) ^ 2 * k / m + 1) :
    (f * (r * (r - 1) / 2) + 3) * ((f * (r * (r - 1) / 2) + 1) * (f * (r * (r - 1) / 2)) / 2 + 4 * r +
        f * (r * (r - 1) / 2) + 3) * (T + f * (r * (r - 1) / 2) + 1) + 4 ≤ TO ∧
      22 * f ^ 2 * r ^ 4 + 2 * r + 1 ≤ TO ∧
      f * (r * (r - 1) / 2) + 1 ≤ PP ^ 2 * (f * (r * (r - 1) / 2)) ^ 2 * k / m := by
  set d := f * (r * (r - 1) / 2) with hd
  have hr1 : 5 ≤ r - 1 := by linarith
  have hrr : 5 * r ≤ r * (r - 1) := by nlinarith
  have hd5 : 5 * r ≤ d := by rw [hd]; nlinarith
  have hd30 : 30 ≤ d := by linarith
  have hdr2 : d ≤ f * r ^ 2 / 2 := by rw [hd]; nlinarith
  have hPP1 : 1 ≤ PP := by nlinarith
  have hkm' : 1 ≤ k / m := (one_le_div hm).2 hkm
  set A := PP ^ 2 * d ^ 2 * k / m with hA
  have hA' : A = PP ^ 2 * d ^ 2 * (k / m) := by rw [hA]; ring
  have hPP2 : 1 ≤ PP ^ 2 := by nlinarith
  have hAd : d ^ 2 ≤ A := by
    rw [hA']
    have h0 : 0 ≤ d ^ 2 := by positivity
    have : d ^ 2 ≤ PP ^ 2 * d ^ 2 := by nlinarith
    calc d ^ 2 ≤ PP ^ 2 * d ^ 2 := this
      _ = PP ^ 2 * d ^ 2 * 1 := by ring
      _ ≤ PP ^ 2 * d ^ 2 * (k / m) := by gcongr
  have hTO' : PP ^ 2 * d * A ≤ TO := by
    have : PP ^ 4 * d ^ 3 * k / m = PP ^ 2 * d * A := by rw [hA]; ring
    linarith
  have hG : (d + 3) * ((d + 1) * d / 2 + 4 * r + d + 3) ≤ d ^ 3 := by nlinarith
  have hT2 : T + d + 1 ≤ 2 * A := by nlinarith
  have hGnn : 0 ≤ (d + 3) * ((d + 1) * d / 2 + 4 * r + d + 3) := by
    have : 0 ≤ r := by linarith
    positivity
  have h3d : 3 * d ^ 2 ≤ PP ^ 2 := by nlinarith
  have hA0 : 0 ≤ A := by nlinarith
  have hd1 : d + 1 ≤ d ^ 2 := by nlinarith
  refine ⟨?_, ?_, by linarith⟩
  · have h1 : (d + 3) * ((d + 1) * d / 2 + 4 * r + d + 3) * (T + d + 1) ≤ d ^ 3 * (2 * A) :=
      mul_le_mul hG hT2 (by linarith) (by positivity)
    have h4 : 4 ≤ d ^ 3 * A := by nlinarith
    have h2 : d ^ 3 * (2 * A) + 4 ≤ PP ^ 2 * d * A := by
      have : 3 * d ^ 2 * (d * A) ≤ PP ^ 2 * (d * A) := by
        apply mul_le_mul_of_nonneg_right h3d; positivity
      nlinarith
    linarith
  · have hP2 : (f * r ^ 2) ^ 2 ≤ PP ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hPP
    have hd900 : (30 : ℝ) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by norm_num) hd30 2
    have hA1 : 1 ≤ A := by linarith
    have hdA : 30 ≤ d * A := by
      calc (30 : ℝ) = 30 * 1 := by ring
        _ ≤ d * A := mul_le_mul hd30 hA1 (by norm_num) (by linarith)
    have hr4 : r * 216 ≤ r ^ 4 := by
      have h3 : (6 : ℝ) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ (by norm_num) hr 3
      have : r ^ 4 = r * r ^ 3 := by ring
      rw [this]
      have h216 : (216 : ℝ) ≤ r ^ 3 := by norm_num at h3; linarith
      have hr0 : (0 : ℝ) ≤ r := by linarith
      exact mul_le_mul_of_nonneg_left h216 hr0
    have hf2 : (2 : ℝ) ^ 2 ≤ f ^ 2 := pow_le_pow_left₀ (by norm_num) hf 2
    norm_num at hf2
    have hfr : 2 * r + 1 ≤ f ^ 2 * r ^ 4 := by
      have : 4 * (r * 216) ≤ f ^ 2 * r ^ 4 := mul_le_mul hf2 hr4 (by positivity) (by positivity)
      linarith
    have h30 : (f * r ^ 2) ^ 2 * 30 ≤ PP ^ 2 * (d * A) := by
      apply mul_le_mul hP2 hdA (by norm_num) (by positivity)
    have e1 : (f * r ^ 2) ^ 2 = f ^ 2 * r ^ 4 := by ring
    have e2 : PP ^ 2 * (d * A) = PP ^ 2 * d * A := by ring
    rw [e1, e2] at h30
    linarith

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Establish `hf : 2 ≤ D.R.f`. Establish `h1 : 0 < D.R.ord` using `D.R.ord_pos`. Establish `h2 : D.R.f = 2 * D.R.ord` using `rfl`. Use linear arithmetic over natural numbers and integers. Establish `hr : 6 ≤ D.R.r`.

Establish `h1` using `D.R.two_le_m`. Establish `h2` using `D.R.m_add_three_le_k`. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers. Establish `hm : 2 ≤ D.R.m` using `D.R.two_le_m`.

Establish `hmk : D.R.m ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `hfR : (2 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf`. Establish `hrR : (6 : ℝ) ≤ D.R.r` using `by exact_mod_cast hr`. Establish `hmR : (0 : ℝ) < D.R.m`. Establish `: (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkmR : (D.R.m : ℝ) ≤ D.R.k` using `by exact_mod_cast hmk`. Establish `hDd : ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)`. Move the coercions through the operations in `[Nat.cast_choose_two]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hdpos : (0 : ℝ) ≤ (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)`. Rewrite using `[← hDd]`. Check the signs of the components of the expression. Establish `hx1 : 1 ≤ L.sc.x` using `L.sc.one_lt_alt.le`. Establish `hL : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow hx1 L.sc.eps_pos.le`.

Establish `hZ : 1 ≤ zBase L`. Unfold `zBase`. Establish `: (12 : ℝ) ≤ (D.R.f : ℝ) * D.R.r` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hPP : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ Tp.PP`.

Rewrite using `[Tp.PP_eq]`. Establish `h1 : zBase L ^ (2 : ℝ) ≤ zBase L ^ Tp.eP` using `Real.rpow_le_rpow_of_exponent_le hZ (by linarith [Tp.eP_ge])`. Rewrite `h1` using `[Real.rpow_two]`. Establish `hL2 : 1 ≤ L.sc.L ^ 2` using `one_le_pow₀ hL`. Establish `hff : (D.R.f : ℝ) ≤ (D.R.f : ℝ) ^ 2 * L.sc.L ^ 2` using `by nlinarith`.

Establish `h3 : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ zBase L ^ 2`. Unfold `zBase`. Combine the equalities or inequalities in the displayed calculation. Establish `hCP` using `Tp.one_le_CP`. Establish `h4 : 0 ≤ zBase L ^ Tp.eP` using `Real.rpow_nonneg (by linarith) _`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hTO : Tp.PP ^ 4 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 3 * D.R.k / D.R.m ≤ (Tp.TO : ℝ)`. Establish `hTOg` using `Tp.TO_ge`. Rewrite `hTOg` using `[Tp.Dp_eq, hDd]`. Use `le_trans ?_ hTOg` and prove the remaining obligations.

Establish `hxc : 1 ≤ L.sc.x ^ Tp.Cp` using `Real.one_le_rpow hx1 Tp.Cp_nonneg`. Establish `hde` using `L.thickDensity_pos`. Establish `hde1` using `L.thickDensity_le_one`. Rewrite using `[div_le_div_iff₀ hmR (mul_pos hmR hde)]`. Establish `hB : 0 ≤ Tp.PP ^ 4 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 3 * D.R.k`.

Establish `: (0 : ℝ) ≤ D.R.k` using `by positivity`. Check the signs of the components of the expression. Establish `hfx : L.de2 ≤ (D.R.f : ℝ) * L.sc.x ^ Tp.Cp` using `by nlinarith`. Use `mul_le_mul_of_nonneg_left hfx (mul_nonneg hB hmR.le)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hPPnn : 0 ≤ Tp.PP` using `le_trans (by positivity) hPP`. Establish `hA0 : 0 ≤ Tp.PP ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)` using `by positivity`. Establish `hT0` using `Nat.ceil_lt_add_one hA0`. Rewrite `hT0`, `hA0` using `[hDd]`. Take `⟨c1, c2, c3⟩` from `core (D.R.f : ℝ) (D.R.r : ℝ) (D.R.k : ℝ) (D.R.m : ℝ) Tp.PP (Tp.TO : ℝ) (⌈Tp.PP ^ 2 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ) hfR hrR hmR hkmR hPP hTO (Nat.cast_nonneg _) hT0.le`.

Establish `hTOt : Tp.TO ≤ D.R.t`. Establish `hs` using `Tp.split`. Establish `h40` using `Tp.nW_40`. Establish `hn0` using `Tp.order_ge_rank_bound`. Establish `: Tp.TO * 40 ≤ Tp.TO * Tp.nWn` using `Nat.mul_le_mul_left _ h40`.

Establish `: D.R.r ≤ Tp.TO` using `le_trans (Nat.le_add_right _ _) hn0`. Use linear arithmetic over natural numbers and integers. Establish `hTON : Tp.TO ≤ D.R.N D.R.m`. Unfold `Ranks.N`. Establish `: D.R.t ≤ D.R.m * (D.R.t + 1)` using `by nlinarith`.

Use linear arithmetic over natural numbers and integers. Establish `hgap : (Tp.TO : ℝ) ≤ LevelStarExponents.gapS D P.Cgap`. Unfold `LevelStarExponents.gapS`. Establish `h1 : ((Tp.TO : ℕ) : ℝ) ≤ (D.R.N D.R.m : ℝ)` using `by exact_mod_cast hTON`. Establish `h2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10` using `one_le_pow₀ (by exact_mod_cast (show 1 ≤ D.R.m by omega))`.

Establish `h3 : 0 ≤ P.Cgap * D.R.k * (D.R.m : ℝ) ^ 4`. Use `P.Cgap_pos` as an intermediate fact. Check the signs of the components of the expression. Establish `h4 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10`. Establish `: (0 : ℝ) ≤ D.R.N D.R.m` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hTO1 : (1 : ℝ) ≤ Tp.TO`. Use `Tp.TO_40` as an intermediate fact. Establish `: 1 ≤ Tp.TO` using `by omega`.

Conclude with `this` after adjusting the coercions. Establish `hh0 : 2 * (Tp.TO : ℝ) ≤ LevelStarExponents.h0 L`. Use `Tp.heightBound_ge_order_sq` as an intermediate fact. Establish `: (0 : ℝ) ≤ D.R.t` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Use `⟨Nat.mul_pos (by omega) (Nat.choose_pos (by omega)), ?_, ?_⟩` and prove the remaining obligations. Establish `h : ((D.R.f * D.R.r.choose 2 + 1 : ℕ) : ℝ) ≤ Tp.PP ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)`. Rewrite using `[Nat.cast_add, Nat.cast_one, hDd]`. Conclude with `c3`. Conclude with `h.trans (Nat.le_ceil _)` after adjusting the coercions.

Introduce `G T hG hT`. Substitute `hG hT` using the available equality. Rewrite using `[hDd]`. Establish `e : ((((D.R.f * D.R.r.choose 2 + 3) * ((D.R.f * D.R.r.choose 2 + 1).choose 2 + 4 * D.R.r + D.R.f * D.R.r.choose 2 + 3)) * (⌈Tp.PP ^ 2 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ + D.R.f * D.R.r.choose 2 + 1) : ℕ) : ℝ) = ((D.R.f : ℝ) * …`. Move the coercions through the operations in `[Nat.cast_choose_two]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `⟨le_min (by linarith) (by linarith), by linarith⟩` and prove the remaining obligations.
-/
theorem at_point {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Tp : ParamsT D L P) :
    1 ≤ D.R.f * D.R.r.choose 2 ∧
    D.R.f * D.R.r.choose 2 + 1 ≤
      ⌈Tp.PP ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ ∧
    ∀ G T : ℕ, G = (D.R.f * D.R.r.choose 2 + 3) *
        ((D.R.f * D.R.r.choose 2 + 1).choose 2 + 4 * D.R.r + D.R.f * D.R.r.choose 2 + 3) →
      T = ⌈Tp.PP ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ →
      ((G * (T + D.R.f * D.R.r.choose 2 + 1) : ℕ) : ℝ) + 4 ≤ min (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L) ∧
      ((G * (T + D.R.f * D.R.r.choose 2 + 1) : ℕ) : ℝ) + 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 +
        2 * D.R.r + 1 ≤ LevelStarExponents.h0 L := by
  have hf : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.ord := D.R.ord_pos
    have h2 : D.R.f = 2 * D.R.ord := rfl
    omega
  have hr : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hmk : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hfR : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hrR : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hmR : (0 : ℝ) < D.R.m := by
    have : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
    linarith
  have hkmR : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast hmk
  have hDd : ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) := by
    push_cast [Nat.cast_choose_two]; ring
  have hdpos : (0 : ℝ) ≤ (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) := by
    rw [← hDd]; positivity

  have hx1 : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hL : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1 L.sc.eps_pos.le
  have hZ : 1 ≤ zBase L := by
    unfold zBase
    have : (12 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    nlinarith
  have hPP : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ Tp.PP := by
    rw [Tp.PP_eq]
    have h1 : zBase L ^ (2 : ℝ) ≤ zBase L ^ Tp.eP :=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith [Tp.eP_ge])
    rw [Real.rpow_two] at h1
    have hL2 : 1 ≤ L.sc.L ^ 2 := one_le_pow₀ hL
    have hff : (D.R.f : ℝ) ≤ (D.R.f : ℝ) ^ 2 * L.sc.L ^ 2 := by nlinarith
    have h3 : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ zBase L ^ 2 := by
      unfold zBase
      calc (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ ((D.R.f : ℝ) ^ 2 * L.sc.L ^ 2) * (D.R.r : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hff (sq_nonneg _)
        _ = ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 2 := by ring
    have hCP := Tp.one_le_CP
    have h4 : 0 ≤ zBase L ^ Tp.eP := Real.rpow_nonneg (by linarith) _
    nlinarith

  have hTO : Tp.PP ^ 4 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 3 * D.R.k / D.R.m ≤ (Tp.TO : ℝ) := by
    have hTOg := Tp.TO_ge
    rw [Tp.Dp_eq, hDd] at hTOg
    refine le_trans ?_ hTOg
    have hxc : 1 ≤ L.sc.x ^ Tp.Cp := Real.one_le_rpow hx1 Tp.Cp_nonneg
    have hde := L.thickDensity_pos
    have hde1 := L.thickDensity_le_one
    rw [div_le_div_iff₀ hmR (mul_pos hmR hde)]
    have hB : 0 ≤ Tp.PP ^ 4 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 3 * D.R.k := by
      have : (0 : ℝ) ≤ D.R.k := by positivity
      positivity
    have hfx : L.de2 ≤ (D.R.f : ℝ) * L.sc.x ^ Tp.Cp := by nlinarith
    have := mul_le_mul_of_nonneg_left hfx (mul_nonneg hB hmR.le)
    nlinarith
  have hPPnn : 0 ≤ Tp.PP := le_trans (by positivity) hPP
  have hA0 : 0 ≤ Tp.PP ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by positivity
  have hT0 := Nat.ceil_lt_add_one hA0
  rw [hDd] at hT0 hA0
  obtain ⟨c1, c2, c3⟩ := core (D.R.f : ℝ) (D.R.r : ℝ) (D.R.k : ℝ) (D.R.m : ℝ) Tp.PP (Tp.TO : ℝ)
    (⌈Tp.PP ^ 2 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ)
    hfR hrR hmR hkmR hPP hTO (Nat.cast_nonneg _) hT0.le

  have hTOt : Tp.TO ≤ D.R.t := by
    have hs := Tp.split
    have h40 := Tp.nW_40
    have hn0 := Tp.order_ge_rank_bound
    have : Tp.TO * 40 ≤ Tp.TO * Tp.nWn := Nat.mul_le_mul_left _ h40
    have : D.R.r ≤ Tp.TO := le_trans (Nat.le_add_right _ _) hn0
    omega
  have hTON : Tp.TO ≤ D.R.N D.R.m := by
    unfold Ranks.N
    have : D.R.t ≤ D.R.m * (D.R.t + 1) := by nlinarith
    omega
  have hgap : (Tp.TO : ℝ) ≤ LevelStarExponents.gapS D P.Cgap := by
    unfold LevelStarExponents.gapS
    have h1 : ((Tp.TO : ℕ) : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hTON
    have h2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ D.R.m by omega))
    have h3 : 0 ≤ P.Cgap * D.R.k * (D.R.m : ℝ) ^ 4 := by
      have := P.Cgap_pos
      positivity
    have h4 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 := by
      have : (0 : ℝ) ≤ D.R.N D.R.m := by positivity
      nlinarith
    linarith
  have hTO1 : (1 : ℝ) ≤ Tp.TO := by
    have := Tp.TO_40
    have : 1 ≤ Tp.TO := by omega
    exact_mod_cast this
  have hh0 : 2 * (Tp.TO : ℝ) ≤ LevelStarExponents.h0 L := by
    have := Tp.heightBound_ge_order_sq
    have : (0 : ℝ) ≤ D.R.t := by positivity
    nlinarith
  refine ⟨Nat.mul_pos (by omega) (Nat.choose_pos (by omega)), ?_, ?_⟩
  · have h : ((D.R.f * D.R.r.choose 2 + 1 : ℕ) : ℝ) ≤
        Tp.PP ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one, hDd]; exact c3
    exact_mod_cast h.trans (Nat.le_ceil _)
  · intro G T hG hT
    subst hG hT
    rw [hDd]
    have e : ((((D.R.f * D.R.r.choose 2 + 3) * ((D.R.f * D.R.r.choose 2 + 1).choose 2 + 4 * D.R.r +
          D.R.f * D.R.r.choose 2 + 3)) *
        (⌈Tp.PP ^ 2 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ +
          D.R.f * D.R.r.choose 2 + 1) : ℕ) : ℝ) =
        ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) + 3) *
          (((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) + 1) * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) / 2 +
            4 * (D.R.r : ℝ) + (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) + 3) *
          ((⌈Tp.PP ^ 2 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ) +
            (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) + 1) := by
      push_cast [Nat.cast_choose_two]; ring
    rw [e]
    refine ⟨le_min (by linarith) (by linarith), by linarith⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨0, fun x hx _ ι => at_point (Fm.parT x hx ι)⟩⟩⟩`.
-/
theorem gaps_large : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x,
    1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 ∧
    (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1 ≤
      ⌈(Fm.parT x hx ι).PP ^ 2 * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) /
        ((Fm.D x ι).R.m : ℝ)⌉₊ ∧
    ∀ G T : ℕ, G = ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) →
      T = ⌈(Fm.parT x hx ι).PP ^ 2 * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) /
        ((Fm.D x ι).R.m : ℝ)⌉₊ →
      ((G * (T + (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1) : ℕ) : ℝ) + 4 ≤
          min (LevelStarExponents.gapS (Fm.D x ι) (Fm.params x hx ι).Cgap) (LevelStarExponents.h0 (Fm.L x ι)) ∧
        ((G * (T + (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1) : ℕ) : ℝ) + 22 * ((Fm.D x ι).R.f : ℝ) ^ 2 * ((Fm.D x ι).R.r : ℝ) ^ 4 +
          2 * (Fm.D x ι).R.r + 1 ≤ LevelStarExponents.h0 (Fm.L x ι) :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun x hx _ ι => at_point (Fm.parT x hx ι)⟩⟩⟩

end GlobalTheory.RunSizes
