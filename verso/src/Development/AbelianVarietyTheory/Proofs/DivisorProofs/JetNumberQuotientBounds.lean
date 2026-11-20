import Mathlib
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientWeightGapBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthUnitSizeBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultAddMultConj

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.NumPt

/- English proof (translation)
Establish `ht1 : (1 : ℝ) ≤ t` using `by linarith`. Establish `hp : ∀ n : ℕ, n ≤ 7 → t ^ n ≤ b` using `fun n hn => (pow_le_pow_right₀ ht1 hn).trans hb`. Establish `h100 : 100 ≤ b` using `by nlinarith [hp 2 (by norm_num)]`. Establish `hb1 : (1 : ℝ) ≤ b` using `by linarith`. Establish `hfr : f * r ≤ t ^ 2` using `by rw [sq]; exact mul_le_mul hf hr hr0 (by linarith)`.

Establish `hfm : f * m ≤ t ^ 2` using `by rw [sq]; exact mul_le_mul hf hm hm0 (by linarith)`. Establish `ht2 : 0 ≤ t ^ 2` using `by positivity`. Establish `h5 : 5 * t ^ 2 ≤ b`. Establish `: t ^ 3 = t * t ^ 2` using `by ring`. Use polynomial arithmetic with `[hp 3 (by norm_num)]`.

Establish `hdb : dF ≤ b ^ 2`. Establish `h1 : f * r * (2 * (2 * b) + 1) ≤ t ^ 2 * (5 * b)` using `mul_le_mul hfr (by linarith) (by linarith) ht2`. Use the polynomial consequences of the given equalities and inequalities. Establish `hN0 : 0 ≤ 2 * f * m` using `by positivity`. Establish `hN : 2 * f * m ≤ b` using `by nlinarith`.

Establish `hN3 : (2 * f * m) ^ 3 ≤ b`. Establish `h1 : (2 * f * m) ^ 3 ≤ (2 * t ^ 2) ^ 3` using `pow_le_pow_left₀ hN0 (by linarith) 3`. Establish `h2 : t ^ 7 = t * t ^ 6` using `by ring`. Establish `h3 : (2 * t ^ 2) ^ 3 = 8 * t ^ 6` using `by ring`. Establish `h4 : 0 ≤ t ^ 6` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hrb : r ≤ b` using `hr.trans (by simpa using hp 1 (by norm_num))`. Establish `hs : Real.sqrt (2 * f * m) ≤ b` using `Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩`. Establish `hq : ∀ n : ℕ, 100 * b ^ n ≤ b ^ (n + 1)` using `fun n => by`. Rewrite using `[pow_succ, mul_comm]; exact mul_le_mul_of_nonneg_left h100 (by positivity)`.

Establish `e2 : 1 ≤ b ^ 2` using `one_le_pow₀ hb1`. Establish `q2` using `hq 2`. Establish `q3` using `hq 3`. Establish `q4` using `hq 4`. Establish `q5` using `hq 5`.

Establish `q6` using `hq 6`. Establish `q7` using `hq 7`. Evaluate the numerical expressions using `at q2 q3 q4 q5 q6 q7`. Use `⟨by linarith, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : dF * (2 * Real.sqrt (2 * f * m)) ≤ b ^ 2 * (2 * b)` using `mul_le_mul hdb (by linarith) (by positivity) (by positivity)`.

Establish `h2 : b ^ 2 * (2 * b) = 2 * b ^ 3` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[div_le_iff₀ (by linarith)]`. Establish `h1 : r * (2 * f * m) ≤ b ^ 2` using `by rw [sq]; exact mul_le_mul hrb hN hN0 (by linarith)`. Establish `h2 : dF ^ 2 ≤ b ^ 4`.

Use `pow_le_pow_left₀ hd0 hdb 2` as an intermediate fact. Rewrite `this` using `[← pow_mul]`. Then use the resulting hypothesis. Establish `h3 : R * (2 * f * m) ^ 3 ≤ b * b` using `mul_le_mul hR hN3 (by positivity) (by linarith)`. Establish `h4 : R * (2 * f * m) ^ 3 * (r * (2 * f * m) / 4 + 2 * dF ^ 2) ≤ b * b * (3 * b ^ 4)` using `mul_le_mul h3 (by linarith) (by positivity) (by positivity)`. Establish `h5 : b * b * (3 * b ^ 4) = 3 * b ^ 6` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem jet_real {f m r t b g dF R : ℝ} (hf0 : 0 ≤ f) (hm0 : 0 ≤ m) (hr0 : 0 ≤ r) (hd0 : 0 ≤ dF)
    (ht : 11 ≤ t) (hf : f ≤ t) (hm : m ≤ t) (hr : r ≤ t) (hb : t ^ 7 ≤ b) (hd : dF ≤ f * r * (2 * (2 * b) + 1))
    (hR : R ≤ b) (hg : b ^ 8 ≤ g) :
    4 * dF + 4 ≤ g ∧ dF * (2 * Real.sqrt (2 * f * m)) < g ∧
      R * (2 * f * m) ^ 3 * (r * (2 * f * m) / 4 + 2 * dF ^ 2) / g ≤ 1 / 2500 := by
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hp : ∀ n : ℕ, n ≤ 7 → t ^ n ≤ b := fun n hn => (pow_le_pow_right₀ ht1 hn).trans hb
  have h100 : 100 ≤ b := by nlinarith [hp 2 (by norm_num)]
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hfr : f * r ≤ t ^ 2 := by rw [sq]; exact mul_le_mul hf hr hr0 (by linarith)
  have hfm : f * m ≤ t ^ 2 := by rw [sq]; exact mul_le_mul hf hm hm0 (by linarith)
  have ht2 : 0 ≤ t ^ 2 := by positivity
  have h5 : 5 * t ^ 2 ≤ b := by
    have : t ^ 3 = t * t ^ 2 := by ring
    nlinarith [hp 3 (by norm_num)]
  have hdb : dF ≤ b ^ 2 := by
    have h1 : f * r * (2 * (2 * b) + 1) ≤ t ^ 2 * (5 * b) := mul_le_mul hfr (by linarith) (by linarith) ht2
    nlinarith
  have hN0 : 0 ≤ 2 * f * m := by positivity
  have hN : 2 * f * m ≤ b := by nlinarith
  have hN3 : (2 * f * m) ^ 3 ≤ b := by
    have h1 : (2 * f * m) ^ 3 ≤ (2 * t ^ 2) ^ 3 := pow_le_pow_left₀ hN0 (by linarith) 3
    have h2 : t ^ 7 = t * t ^ 6 := by ring
    have h3 : (2 * t ^ 2) ^ 3 = 8 * t ^ 6 := by ring
    have h4 : 0 ≤ t ^ 6 := by positivity
    nlinarith
  have hrb : r ≤ b := hr.trans (by simpa using hp 1 (by norm_num))
  have hs : Real.sqrt (2 * f * m) ≤ b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hq : ∀ n : ℕ, 100 * b ^ n ≤ b ^ (n + 1) := fun n => by
    rw [pow_succ, mul_comm]; exact mul_le_mul_of_nonneg_left h100 (by positivity)
  have e2 : 1 ≤ b ^ 2 := one_le_pow₀ hb1
  have q2 := hq 2
  have q3 := hq 3
  have q4 := hq 4
  have q5 := hq 5
  have q6 := hq 6
  have q7 := hq 7
  norm_num at q2 q3 q4 q5 q6 q7
  refine ⟨by linarith, ?_, ?_⟩
  · have h1 : dF * (2 * Real.sqrt (2 * f * m)) ≤ b ^ 2 * (2 * b) :=
      mul_le_mul hdb (by linarith) (by positivity) (by positivity)
    have h2 : b ^ 2 * (2 * b) = 2 * b ^ 3 := by ring
    linarith
  · rw [div_le_iff₀ (by linarith)]
    have h1 : r * (2 * f * m) ≤ b ^ 2 := by rw [sq]; exact mul_le_mul hrb hN hN0 (by linarith)
    have h2 : dF ^ 2 ≤ b ^ 4 := by
      have := pow_le_pow_left₀ hd0 hdb 2
      rwa [← pow_mul] at this
    have h3 : R * (2 * f * m) ^ 3 ≤ b * b := mul_le_mul hR hN3 (by positivity) (by linarith)
    have h4 : R * (2 * f * m) ^ 3 * (r * (2 * f * m) / 4 + 2 * dF ^ 2) ≤ b * b * (3 * b ^ 4) :=
      mul_le_mul h3 (by linarith) (by positivity) (by positivity)
    have h5 : b * b * (3 * b ^ 4) = 3 * b ^ 6 := by ring
    linarith

/- English proof (translation)
The claim follows from `D.host.finrank_E'`.
-/
theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := D.host.finrank_E'

/- English proof (translation)
Take `⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩` from `S`. Take `⟨-, -, -, -, -, -, h1, h2⟩` from `sQD`. Establish `a1` using `D.R.two_le_m`. Establish `a2` using `D.R.m_add_three_le_k`. Establish `a3 : D.R.r + 5 ≤ D.R.t` using `D.R.rank_add_five_le`.

Establish `a4 : D.R.f ≤ D.R.k` using `D.R.f_le_k`. Establish `a5 : D.R.k ≤ D.R.r ∧ D.R.m ≤ D.R.r ∧ 6 ≤ D.R.r` using `by unfold Ranks.r; omega`. Establish `ht : (11 : ℝ) ≤ D.R.t` using `by exact_mod_cast (by omega : 11 ≤ D.R.t)`. Establish `hf : (D.R.f : ℝ) ≤ D.R.t` using `by exact_mod_cast (by omega : D.R.f ≤ D.R.t)`. Establish `hm : (D.R.m : ℝ) ≤ D.R.t` using `by exact_mod_cast (by omega : D.R.m ≤ D.R.t)`.

Establish `hr : (D.R.r : ℝ) ≤ D.R.t` using `by exact_mod_cast (by omega : D.R.r ≤ D.R.t)`. Establish `hk : (1 : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : 1 ≤ D.R.k)`. Establish `hL : 0 ≤ L.sc.L` using `Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _`. Establish `hb1 : 1 ≤ L.sc.b` using `Real.one_le_exp hL`. Establish `hsb : Real.sqrt L.sc.b ≤ L.sc.b` using `Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩`.

Establish `hq : (1 : ℝ) ≤ D.host.q` using `by exact_mod_cast D.host.hyp.1.one_lt.le`. Establish `hd' : (1 : ℝ) ≤ D.host.d` using `by exact_mod_cast D.host.hyp.2.1.one_lt.le`. Establish `hn : (1 : ℝ) ≤ D.R.n` using `by exact_mod_cast D.R.ord_pos`. Establish `hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d` using `by nlinarith`. Establish `hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d`.

Rewrite using `[Real.sqrt_le_left (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hc : D.host.rdE ≤ szCond L`. Unfold `szCond`. Establish `h0 : (0 : ℝ) ≤ D.host.QS` using `Nat.cast_nonneg _`.

Establish `: (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.QS * ((D.host.q : ℝ) * D.host.d)` using `mul_le_mul_of_nonneg_left hs h0`. Use polynomial arithmetic with `[mul_nonneg h0 (Real.sqrt_nonneg ((D.host.q : ℝ) * D.host.d))]`. Establish `hc1 : (1 : ℝ) ≤ szCond L` using `h1.trans hc`. Establish `ht1 : (1 : ℝ) ≤ D.R.t` using `by linarith`. Establish `sC' : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ L.sc.b` using `le_trans sC hsb`.

Establish `hb : (D.R.t : ℝ) ^ 7 ≤ L.sc.b` using `((pow_le_pow_right₀ ht1 (by norm_num)).trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1))).trans sC'`. Establish `hrd : D.host.rdE ^ 2 ≤ L.sc.b` using `(((pow_le_pow_left₀ (by linarith) hc 2).trans (pow_le_pow_right₀ hc1 (by norm_num))).trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1))).trans sC'`. Establish `hR : rr0 D ≤ L.sc.b`. Establish `hn1 : (1 : ℝ) ≤ Module.finrank ℚ D.host.E` using `by exact_mod_cast Module.finrank_pos`. Establish `e : |(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E) = D.host.rdE ^ 2`.

Unfold `Formalism.BasicNotions.Host.rdE`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Unfold `rr0`. Rewrite using `[e]`. Conclude with `(div_le_self (by positivity) (by linarith)).trans hrd`. Introduce `k`. Establish `hg : L.sc.b ^ 8 ≤ (D.host.g k : ℝ)` using `(pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1`.

Take `⟨c1, c2, c3⟩` from `jet_real (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) ht hf hm hr hb hd hR hg`. Conclude with `⟨by exact_mod_cast c1, c2, c3⟩`.
-/
theorem jetNum_of_sizes {D : D7} {L : SizeData₂ D} (S : SizesAt L) {dF : ℕ}
    (hd : (dF : ℝ) ≤ D.R.f * D.R.r * (2 * (2 * L.sc.b) + 1)) : JetNum D dF (1 / 2500) := by
  obtain ⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩ := S
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := sQD
  have a1 := D.R.two_le_m
  have a2 := D.R.m_add_three_le_k
  have a3 : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have a4 : D.R.f ≤ D.R.k := D.R.f_le_k
  have a5 : D.R.k ≤ D.R.r ∧ D.R.m ≤ D.R.r ∧ 6 ≤ D.R.r := by unfold Ranks.r; omega
  have ht : (11 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 11 ≤ D.R.t)
  have hf : (D.R.f : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.f ≤ D.R.t)
  have hm : (D.R.m : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.m ≤ D.R.t)
  have hr : (D.R.r : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.r ≤ D.R.t)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hL : 0 ≤ L.sc.L := Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp hL
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd' : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.ord_pos
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hc : D.host.rdE ≤ szCond L := by
    unfold szCond
    have h0 : (0 : ℝ) ≤ D.host.QS := Nat.cast_nonneg _
    have : (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.QS * ((D.host.q : ℝ) * D.host.d) :=
      mul_le_mul_of_nonneg_left hs h0
    nlinarith [mul_nonneg h0 (Real.sqrt_nonneg ((D.host.q : ℝ) * D.host.d))]
  have hc1 : (1 : ℝ) ≤ szCond L := h1.trans hc
  have ht1 : (1 : ℝ) ≤ D.R.t := by linarith
  have sC' : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ L.sc.b := le_trans sC hsb
  have hb : (D.R.t : ℝ) ^ 7 ≤ L.sc.b :=
    ((pow_le_pow_right₀ ht1 (by norm_num)).trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1))).trans sC'
  have hrd : D.host.rdE ^ 2 ≤ L.sc.b :=
    (((pow_le_pow_left₀ (by linarith) hc 2).trans (pow_le_pow_right₀ hc1 (by norm_num))).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1))).trans sC'
  have hR : rr0 D ≤ L.sc.b := by
    have hn1 : (1 : ℝ) ≤ Module.finrank ℚ D.host.E := by exact_mod_cast Module.finrank_pos
    have e : |(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E) = D.host.rdE ^ 2 := by
      unfold Formalism.BasicNotions.Host.rdE
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      push_cast
      ring
    unfold rr0
    rw [e]
    exact (div_le_self (by positivity) (by linarith)).trans hrd
  intro k
  have hg : L.sc.b ^ 8 ≤ (D.host.g k : ℝ) :=
    (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1
  obtain ⟨c1, c2, c3⟩ := jet_real (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    ht hf hm hr hb hd hR hg
  exact ⟨by exact_mod_cast c1, c2, c3⟩

section Cols

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

/- English proof (translation)
The claim follows from `_root_.GlobalTheory.ConjugateMultiplicitySum.mult_add_mult_conj D τ`.
-/
theorem mult_add_mult_conj (D : Datum H) (τ : E →+* ℂ) :
    D.mult τ + D.mult (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ) = D.p + D.q :=
  _root_.GlobalTheory.ConjugateMultiplicitySum.mult_add_mult_conj D τ

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h` using `mult_add_mult_conj Dw τ`. Establish `hle : ∀ σ, Dw.mult σ ≤ Fintype.card (Lt1 Dw)` using `fun σ => by`. Use `Fintype.card_le_of_injective (fun i : Fin (Dw.mult σ) => (⟨σ, i⟩ : Lt1 Dw)) (@sigma_mk_injective _ (fun τ => Fin (Dw.mult τ)) σ)` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`. Then use the resulting hypothesis.

Establish `h1` using `hle τ`. Establish `h2` using `hle (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ)`. Unfold `nCol`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_mul_rank_le_nCol (Dw : Datum H) : 2 * (Dw.p + Dw.q) ≤ nCol Dw := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h := mult_add_mult_conj Dw τ
  have hle : ∀ σ, Dw.mult σ ≤ Fintype.card (Lt1 Dw) := fun σ => by
    have := Fintype.card_le_of_injective (fun i : Fin (Dw.mult σ) => (⟨σ, i⟩ : Lt1 Dw))
      (@sigma_mk_injective _ (fun τ => Fin (Dw.mult τ)) σ)
    rwa [Fintype.card_fin] at this
  have h1 := hle τ
  have h2 := hle (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ)
  unfold nCol
  omega

end Cols

/- English proof (translation)
Take `⟨Y, h1, -, h3, h4⟩` from `P.g_Y`. Establish `hk : (0 : ℝ) < D.R.k` using `by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : 0 < D.R.k)`. Establish `hb : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hY : 0 < Y` using `lt_of_lt_of_le (by positivity) h1`. Establish `hg : ∀ i, Real.log (D.host.g i) ≤ L.sc.L + P.CYL * L.sc.L` using `fun i => by`.

Establish `a` using `Real.log_le_log (hY.trans_le (h4 i).1) (h4 i).2`. Rewrite `a` using `[Real.log_mul two_ne_zero hY.ne']`. Use `Real.log_two_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf' : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf`.

Establish `hr' : (1 : ℝ) ≤ D.R.r` using `by exact_mod_cast hr`. Establish `hZ : L.sc.L ≤ zBase L` using `le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hf' hr')`. Establish `hZ' : L.sc.L ≤ zBase L ^ 12` using `hZ.trans (le_self_pow₀ (hL.trans hZ) (by norm_num))`. Use `mul_le_mul_of_nonneg_left hZ' (show 0 ≤ 2 + 2 * P.CYL by linarith [P.CYL_pos])` as an intermediate fact. Combine the linear relations using `[hg 0, hg 1]`.
-/
theorem log_g_le {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (hL : 1 ≤ L.sc.L) (hf : 1 ≤ D.R.f) (hr : 1 ≤ D.R.r) :
    Real.log (D.host.g 0) + Real.log (D.host.g 1) ≤ (2 + 2 * P.CYL) * zBase L ^ 12 := by
  obtain ⟨Y, h1, -, h3, h4⟩ := P.g_Y
  have hk : (0 : ℝ) < D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : 0 < D.R.k)
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) h1
  have hg : ∀ i, Real.log (D.host.g i) ≤ L.sc.L + P.CYL * L.sc.L := fun i => by
    have a := Real.log_le_log (hY.trans_le (h4 i).1) (h4 i).2
    rw [Real.log_mul two_ne_zero hY.ne'] at a
    have := Real.log_two_lt_d9
    linarith
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hZ : L.sc.L ≤ zBase L := le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hf' hr')
  have hZ' : L.sc.L ≤ zBase L ^ 12 := hZ.trans (le_self_pow₀ (hL.trans hZ) (by norm_num))
  have := mul_le_mul_of_nonneg_left hZ' (show 0 ≤ 2 + 2 * P.CYL by linarith [P.CYL_pos])
  linarith [hg 0, hg 1]

/- English proof (translation)
Introduce `hS`. Use `Closed.imp (Closed.and (GlobalTheory.T.quotient_weight_gap_bounds hS) (GlobalTheory.T.length_unit_size_bounds hS)) ?_` and prove the remaining obligations. Introduce and unpack `eps Fm CH - ⟨⟨_, _, hA⟩, ⟨_, _, hB⟩⟩`. Take `⟨x0, h⟩` from `EvTied.and hA hB`. Use `⟨max 0 (2 + 2 * Fm.CYL), le_max_left _ _, x0, fun x hx hle ι p hp i hi u1 hu => ?_⟩` and prove the remaining obligations.

Take `⟨hA, hB⟩` from `h x hx hle ι p hp`. Take `⟨a1, -, a3, a4, a5, a6, -⟩` from `hA i hi u1 hu`. Take `⟨b1, b2, -, -, b5, b6⟩` from `hB i`. Use `⟨jetNum_of_sizes (Fm.sizes x hx ι) ?_, a3 ▸ two_mul_rank_le_nCol _, ?_⟩` and prove the remaining obligations. Establish `hev : Even (nCol (dat p i))` using `even_iff_two_dvd.2 (Dvd.dvd.trans (by norm_num) eight_dvd_nCol)`.

Use `(GlobalTheory.T.thetaExponents_dominant_lastEntry_one_degree _ _ (dat p i) u1 (nCol (dat p i)) _ a1 hev a4 a5 a6).2.2.2.2` as an intermediate fact. Rewrite `this` using `[finrank_host, a3, Nat.mul_div_cancel_left _ two_pos]`. Conclude with `this`. Establish `hg` using `log_g_le (Fm.params x hx ι) b2 b5 b6`. Rewrite `hg` using `[Fm.params_CYL x hx ι]`.

Establish `hZ : 0 ≤ zBase (Fm.L x ι) ^ 12` using `by positivity`. Establish `hT : (0 : ℝ) ≤ lenT p i (Fm.parT x hx ι).PP` using `Nat.cast_nonneg _`. Establish `hg'` using `hg.trans (mul_le_mul_of_nonneg_right (le_max_right 0 _) hZ)`. Establish `h1` using `mul_le_mul_of_nonneg_left hg' hT`. Establish `h2` using `mul_le_mul_of_nonneg_left b1 (le_max_left 0 (2 + 2 * Fm.CYL))`.

Combine the linear relations using `[mul_left_comm (lenT p i (Fm.parT x hx ι).PP : ℝ) (max 0 (2 + 2 * Fm.CYL)) (zBase (Fm.L x ι) ^ 12)]`.
-/
theorem numbers_at_point : Size → Lifts fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → JetNum (Fm.D x ι) (DF (dat p i) (aOf p i u1)) (1 / 2500) ∧ 2 * (Fm.D x ι).R.r ≤ nCol (dat p i) ∧ (lenT p i PP : ℝ) * (Real.log ((Fm.D x ι).host.g 0) + Real.log ((Fm.D x ι).host.g 1)) ≤ C * unitE p := by
  intro hS
  refine Closed.imp (Closed.and (GlobalTheory.T.quotient_weight_gap_bounds hS) (GlobalTheory.T.length_unit_size_bounds hS)) ?_
  rintro eps Fm CH - ⟨⟨_, _, hA⟩, ⟨_, _, hB⟩⟩
  obtain ⟨x0, h⟩ := EvTied.and hA hB
  refine ⟨max 0 (2 + 2 * Fm.CYL), le_max_left _ _, x0, fun x hx hle ι p hp i hi u1 hu => ?_⟩
  obtain ⟨hA, hB⟩ := h x hx hle ι p hp
  obtain ⟨a1, -, a3, a4, a5, a6, -⟩ := hA i hi u1 hu
  obtain ⟨b1, b2, -, -, b5, b6⟩ := hB i
  refine ⟨jetNum_of_sizes (Fm.sizes x hx ι) ?_, a3 ▸ two_mul_rank_le_nCol _, ?_⟩
  · have hev : Even (nCol (dat p i)) := even_iff_two_dvd.2 (Dvd.dvd.trans (by norm_num) eight_dvd_nCol)
    have := (GlobalTheory.T.thetaExponents_dominant_lastEntry_one_degree _ _ (dat p i) u1 (nCol (dat p i)) _ a1 hev a4 a5 a6).2.2.2.2
    rw [finrank_host, a3, Nat.mul_div_cancel_left _ two_pos] at this
    exact this
  · have hg := log_g_le (Fm.params x hx ι) b2 b5 b6
    rw [Fm.params_CYL x hx ι] at hg
    have hZ : 0 ≤ zBase (Fm.L x ι) ^ 12 := by positivity
    have hT : (0 : ℝ) ≤ lenT p i (Fm.parT x hx ι).PP := Nat.cast_nonneg _
    have hg' := hg.trans (mul_le_mul_of_nonneg_right (le_max_right 0 _) hZ)
    have h1 := mul_le_mul_of_nonneg_left hg' hT
    have h2 := mul_le_mul_of_nonneg_left b1 (le_max_left 0 (2 + 2 * Fm.CYL))
    linarith [mul_left_comm (lenT p i (Fm.parT x hx ι).PP : ℝ) (max 0 (2 + 2 * Fm.CYL)) (zBase (Fm.L x ι) ^ 12)]

end GlobalTheory.RefSum.NumPt
