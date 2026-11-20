import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafIPOfTwoConstants
import Formalism.LocalToGlobal.Divisibility.EigenvalueSumLeClosedOf
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FourMulQLeCondN
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.HalfNorm

open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.BigTop.Fun.IPbProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hx` using `L.sc.one_lt_alt`. Establish `h0 : 0 ≤ L.sc.L` using `Real.rpow_nonneg (by linarith) _`. Unfold `Scale.b`. Conclude with `Real.one_le_exp h0`.
-/
theorem one_le_b {D : D7} (L : SizeData₂ D) : 1 ≤ L.sc.b := by
  have hx := L.sc.one_lt_alt
  have h0 : 0 ≤ L.sc.L := Real.rpow_nonneg (by linarith) _
  unfold Scale.b
  exact Real.one_le_exp h0

/- English proof (translation)
Take `⟨hN, -, -, -, hT, hC, hQ, -⟩` from `hS`. Take `⟨-, -, -, -, -, -, hr1, hr2⟩` from `hQ`. Establish `hx` using `L.sc.one_lt_alt`. Establish `hn : (1 : ℝ) ≤ (D.R.n : ℝ)`. Establish `: 1 ≤ D.R.n` using `D.R.n_pos'`.

Conclude with `this` after adjusting the coercions. Establish `hq : (1 : ℝ) ≤ (D.host.q : ℝ)` using `by exact_mod_cast D.host.hyp.1.one_le`. Establish `hd : (1 : ℝ) ≤ (D.host.d : ℝ)` using `by exact_mod_cast D.host.hyp.2.1.one_le`. Establish `hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d` using `by nlinarith`. Establish `hb` using `one_le_b L`.

Establish `hnc : (D.R.n : ℝ) ≤ szCond L`. Establish `h` using `D.host.four_ord_le_condN`. Establish `h' : D.R.n ≤ D.host.QS * D.host.q * D.host.d` using `by rw [D.R.n_eq_ord]; omega`. Unfold `szCond`. Conclude with `h'` after adjusting the coercions.

Establish `hc1 : 1 ≤ szCond L` using `hn.trans hnc`. Establish `hcb : szCond L ≤ L.sc.b`. Establish `h1 : szCond L ≤ szCond L ^ 36` using `le_self_pow₀ hc1 (by norm_num)`. Establish `h2 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150` using `one_le_pow₀ hT.1`. Establish `h3 : Real.sqrt L.sc.b ≤ L.sc.b` using `Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩`.

Establish `h4 : szCond L ^ 36 ≤ szCond L ^ 36 * (D.R.t : ℝ) ^ 150` using `le_mul_of_one_le_right (by positivity) h2`. Establish `h5 : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b` using `hC`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hxn : L.sc.x ≤ (D.R.n : ℝ)`. Use `le_trans ?_ hN.1` and prove the remaining obligations.

Establish `he` using `L.sc.eps_pos`. Combine the equalities or inequalities in the displayed calculation. Establish `hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d` using `Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩`. Establish `hxb : L.sc.x ≤ L.sc.b` using `(hxn.trans hnc).trans hcb`. Establish `hrb : D.host.rdE ≤ L.sc.b` using `(UpperTheory.Ram.Rd.rdE_le_cond D.host).trans hcb`.

Establish `hlb : Real.log L.sc.b = L.sc.L` using `Real.log_exp _`. Establish `l1` using `Real.log_le_log (by linarith) hxb`. Establish `l2` using `Real.log_le_log (by linarith) hrb`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hr0 : 0 < D.host.rdE` using `by linarith`.

Establish `e : L.La = Real.log L.sc.x + L.sc.L + Real.log D.host.rdE`. Unfold `SizeData₂.La Scale.a Scale.b`. Rewrite using `[Real.log_mul (by positivity) hr0.ne', Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem La_le_three {D : D7} (L : SizeData₂ D) (hS : SizesAt L) : L.La ≤ 3 * L.sc.L := by
  obtain ⟨hN, -, -, -, hT, hC, hQ, -⟩ := hS
  obtain ⟨-, -, -, -, -, -, hr1, hr2⟩ := hQ
  have hx := L.sc.one_lt_alt
  have hn : (1 : ℝ) ≤ (D.R.n : ℝ) := by
    have : 1 ≤ D.R.n := D.R.n_pos'
    exact_mod_cast this
  have hq : (1 : ℝ) ≤ (D.host.q : ℝ) := by exact_mod_cast D.host.hyp.1.one_le
  have hd : (1 : ℝ) ≤ (D.host.d : ℝ) := by exact_mod_cast D.host.hyp.2.1.one_le
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hb := one_le_b L
  have hnc : (D.R.n : ℝ) ≤ szCond L := by
    have h := D.host.four_ord_le_condN
    have h' : D.R.n ≤ D.host.QS * D.host.q * D.host.d := by rw [D.R.n_eq_ord]; omega
    unfold szCond; exact_mod_cast h'
  have hc1 : 1 ≤ szCond L := hn.trans hnc
  have hcb : szCond L ≤ L.sc.b := by
    have h1 : szCond L ≤ szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
    have h2 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ hT.1
    have h3 : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have h4 : szCond L ^ 36 ≤ szCond L ^ 36 * (D.R.t : ℝ) ^ 150 := le_mul_of_one_le_right (by positivity) h2
    have h5 : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b := hC
    linarith
  have hxn : L.sc.x ≤ (D.R.n : ℝ) := by
    refine le_trans ?_ hN.1
    have he := L.sc.eps_pos
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by unfold szTh; linarith)
  have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hxb : L.sc.x ≤ L.sc.b := (hxn.trans hnc).trans hcb
  have hrb : D.host.rdE ≤ L.sc.b := (UpperTheory.Ram.Rd.rdE_le_cond D.host).trans hcb
  have hlb : Real.log L.sc.b = L.sc.L := Real.log_exp _
  have l1 := Real.log_le_log (by linarith) hxb
  have l2 := Real.log_le_log (by linarith) hrb
  have hx0 : 0 < L.sc.x := by linarith
  have hr0 : 0 < D.host.rdE := by linarith
  have e : L.La = Real.log L.sc.x + L.sc.L + Real.log D.host.rdE := by
    unfold SizeData₂.La Scale.a Scale.b
    rw [Real.log_mul (by positivity) hr0.ne', Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [e]
  linarith

end GlobalTheory.BigTop.Fun.IPbProof

namespace GlobalTheory.BigTop.Fun

open GlobalTheory.BigTop.Fun.IPbProof

/- English proof (translation)
Introduce `hL`. Use `⟨0, fun CF _ => hL.imp fun Fm CH _ h _ => ?_⟩` and prove the remaining obligations. Use `⟨max 0 (max Fm.Csz 0 * (3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3))), fun C hC => ?_⟩` and prove the remaining obligations. Take `⟨x0, hx0⟩` from `h`. Use `⟨max x0 9, fun x hx hle i p hp d _ => ?_⟩` and prove the remaining obligations.

Establish `h6` using `hx0 x hx (le_of_max_le_left hle) i p hp C`. Establish `hC0 : 0 ≤ C` using `(le_max_left _ _).trans hC`. Establish `hC1 : max Fm.Csz 0 * (3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3)) ≤ C` using `(le_max_right _ _).trans hC`. Establish `hb : 1 ≤ p.Z.b` using `one_le_b (Fm.L x i)`. Establish `hlb : Real.log p.Z.b = (Fm.L x i).sc.L` using `Real.log_exp _`.

Establish `hL0 : 0 ≤ (Fm.L x i).sc.L` using `by rw [← hlb]; exact Real.log_nonneg hb`. Use `set P5 := Fm.params x hx i`. Establish `hS` using `Fm.sizes x hx i`. Establish `hx9 : 9 ≤ (Fm.L x i).sc.x` using `by rw [Fm.L_x x i hx]; exact le_of_max_le_right hle`. Establish `hLp` using `Formalism.L2.DIV.Arith4S.Lp_le_La (Fm.L x i) p.Del p.h0 P5 hS hx9`.

Rewrite `hLp` using `[Formalism.L2.DIV.ofRecord_La, Fm.params_CYL x hx i, Fm.Ct_eq x i]`. Establish `hLa` using `La_le_three (Fm.L x i) hS`. Establish `hY : 0 < Fm.CYL` using `(Fm.params_CYL x hx i) ▸ P5.CYL_pos`. Use `set c : ℝ := 3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3) with hc`. Establish `hc0 : 0 ≤ c` using `by have := le_max_right Fm.Ct 5; rw [hc]; linarith`.

Use `set Lp := (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).Lp`. Establish `hLp0 : 0 ≤ Lp` using `Formalism.L2.DIV.NumDatum.Lp_nonneg _`. Establish `hLp3 : Lp ≤ 3 * c * (Fm.L x i).sc.L` using `by nlinarith`. Establish `hNV : ((Fm.D x i).R.nV : ℝ) ≤ (d.O.N : ℝ)`. Establish `hm` using `(Fm.D x i).R.two_le_m`.

Establish `h1 : (Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1 ≤ (Fm.D x i).R.m * ((Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1)` using `Nat.le_mul_of_pos_left _ (by omega)`. Establish `h2 : (Fm.D x i).R.nV ≤ d.O.N` using `by show (Fm.D x i).R.k + (Fm.D x i).R.m - 1 + (Fm.D x i).R.t ≤ (Fm.D x i).R.k + (Fm.D x i).R.m * ((Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1)`. Use linear arithmetic over natural numbers and integers. Conclude with `h2` after adjusting the coercions. Establish `hf0 : (0 : ℝ) ≤ ((Fm.D x i).R.f : ℝ)` using `Nat.cast_nonneg _`.

Establish `hnv0 : (0 : ℝ) ≤ ((Fm.D x i).R.nV : ℝ)` using `Nat.cast_nonneg _`. Establish `hsq : ((Fm.D x i).R.nV : ℝ) ^ 2 ≤ (d.O.N : ℝ) ^ 2` using `pow_le_pow_left₀ hnv0 hNV 2`. Establish `hA0 : 0 ≤ ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp` using `by positivity`. Establish `hA : ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp ≤ ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (3 * c * (Fm.L x i).sc.L)` using `by gcongr`. Establish `hB0 : 0 ≤ ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L` using `by positivity`.

Establish `hcs : Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤ 3 * C * ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L`. Establish `e1 : Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤ max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp)` using `mul_le_mul_of_nonneg_right (le_max_left _ _) hA0`. Establish `e2 : max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤ max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (3 * c * (Fm.L x i).sc.L))` using `mul_le_mul_of_nonneg_left hA (le_max_right _ _)`. Establish `e3 : max Fm.Csz 0 * c * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L) ≤ C * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L)` using `mul_le_mul_of_nonneg_right hC1 hB0`. Use the polynomial consequences of the given equalities and inequalities.

Use `GlobalTheory.InfinitePlacesProbe.clauseB_of_lifts (p.S false) (p.S true) (p.N C CH) d.O hC0 hb ⟨rfl, rfl, rfl⟩ h6 (by simp; rfl) fun j => ?_` and prove the remaining obligations. Establish `hm0 : 0 ≤ ∑ ρ : Formalism.L2.DIV.RPl (Fm.D x i).R, (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).logHook (((Equiv.refl _ : p.P.A3.fam3.base3.J ≃ Fin (Fm.D x i).R.m) j).1 + 1) ρ` using `Finset.sum_nonneg fun ρ _ => Real.log_natCast_nonneg _`. Establish `e : (p.N C CH).l6 j = (∑ ρ : Formalism.L2.DIV.RPl (Fm.D x i).R, (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).logHook (((Equiv.refl _ : p.P.A3.fam3.base3.J ≃ Fin (Fm.D x i).R.m) j).1 + 1) ρ) - Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) - C * 0` using `rfl`. Rewrite using `[e, hlb]`. Use `show -(3 * C * ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L) ≤ _`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ipb_of_lamLow : GlobalTheory.BigTop.LamLow → IPb := by
  intro hL
  refine ⟨0, fun CF _ => hL.imp fun Fm CH _ h _ => ?_⟩
  refine ⟨max 0 (max Fm.Csz 0 * (3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3))), fun C hC => ?_⟩
  obtain ⟨x0, hx0⟩ := h
  refine ⟨max x0 9, fun x hx hle i p hp d _ => ?_⟩
  have h6 := hx0 x hx (le_of_max_le_left hle) i p hp C
  have hC0 : 0 ≤ C := (le_max_left _ _).trans hC
  have hC1 : max Fm.Csz 0 * (3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3)) ≤ C := (le_max_right _ _).trans hC
  have hb : 1 ≤ p.Z.b := one_le_b (Fm.L x i)
  have hlb : Real.log p.Z.b = (Fm.L x i).sc.L := Real.log_exp _
  have hL0 : 0 ≤ (Fm.L x i).sc.L := by rw [← hlb]; exact Real.log_nonneg hb
  set P5 := Fm.params x hx i
  have hS := Fm.sizes x hx i
  have hx9 : 9 ≤ (Fm.L x i).sc.x := by rw [Fm.L_x x i hx]; exact le_of_max_le_right hle
  have hLp := Formalism.L2.DIV.Arith4S.Lp_le_La (Fm.L x i) p.Del p.h0 P5 hS hx9
  rw [Formalism.L2.DIV.ofRecord_La, Fm.params_CYL x hx i, Fm.Ct_eq x i] at hLp
  have hLa := La_le_three (Fm.L x i) hS
  have hY : 0 < Fm.CYL := (Fm.params_CYL x hx i) ▸ P5.CYL_pos
  set c : ℝ := 3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3) with hc
  have hc0 : 0 ≤ c := by have := le_max_right Fm.Ct 5; rw [hc]; linarith
  set Lp := (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).Lp
  have hLp0 : 0 ≤ Lp := Formalism.L2.DIV.NumDatum.Lp_nonneg _
  have hLp3 : Lp ≤ 3 * c * (Fm.L x i).sc.L := by nlinarith
  have hNV : ((Fm.D x i).R.nV : ℝ) ≤ (d.O.N : ℝ) := by
    have hm := (Fm.D x i).R.two_le_m
    have h1 : (Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1 ≤
        (Fm.D x i).R.m * ((Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h2 : (Fm.D x i).R.nV ≤ d.O.N := by
      show (Fm.D x i).R.k + (Fm.D x i).R.m - 1 + (Fm.D x i).R.t ≤
        (Fm.D x i).R.k + (Fm.D x i).R.m * ((Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1)
      omega
    exact_mod_cast h2
  have hf0 : (0 : ℝ) ≤ ((Fm.D x i).R.f : ℝ) := Nat.cast_nonneg _
  have hnv0 : (0 : ℝ) ≤ ((Fm.D x i).R.nV : ℝ) := Nat.cast_nonneg _
  have hsq : ((Fm.D x i).R.nV : ℝ) ^ 2 ≤ (d.O.N : ℝ) ^ 2 := pow_le_pow_left₀ hnv0 hNV 2
  have hA0 : 0 ≤ ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp := by positivity
  have hA : ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp ≤
      ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (3 * c * (Fm.L x i).sc.L) := by
    gcongr
  have hB0 : 0 ≤ ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L := by positivity
  have hcs : Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤
      3 * C * ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L := by
    have e1 : Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤
        max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hA0
    have e2 : max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤
        max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (3 * c * (Fm.L x i).sc.L)) :=
      mul_le_mul_of_nonneg_left hA (le_max_right _ _)
    have e3 : max Fm.Csz 0 * c * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L) ≤
        C * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L) :=
      mul_le_mul_of_nonneg_right hC1 hB0
    nlinarith
  refine GlobalTheory.InfinitePlacesProbe.clauseB_of_lifts (p.S false) (p.S true) (p.N C CH) d.O hC0 hb ⟨rfl, rfl, rfl⟩ h6
    (by simp; rfl) fun j => ?_
  have hm0 : 0 ≤ ∑ ρ : Formalism.L2.DIV.RPl (Fm.D x i).R,
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).logHook
        (((Equiv.refl _ : p.P.A3.fam3.base3.J ≃ Fin (Fm.D x i).R.m) j).1 + 1) ρ :=
    Finset.sum_nonneg fun ρ _ => Real.log_natCast_nonneg _
  have e : (p.N C CH).l6 j = (∑ ρ : Formalism.L2.DIV.RPl (Fm.D x i).R,
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).logHook
        (((Equiv.refl _ : p.P.A3.fam3.base3.J ≃ Fin (Fm.D x i).R.m) j).1 + 1) ρ) -
      Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) - C * 0 := rfl
  rw [e, hlb]
  show -(3 * C * ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L) ≤ _
  linarith

end GlobalTheory.BigTop.Fun

end
