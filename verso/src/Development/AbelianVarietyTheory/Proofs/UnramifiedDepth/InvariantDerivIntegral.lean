import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SigmaDefectEvalPhaseOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PderivEvSecond

set_option autoImplicit false

noncomputable section

open MvPowerSeries Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
  ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.GaugeGermIntegral

variable {K : Type} [Field K]

def intRing (V : VF K) : Subring K where
  carrier := {a | V.Ge 0 a}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `ig_of_intAA fun n => ⟨⟨_, h n⟩, rfl⟩`. Introduce `h n`. Take `⟨r, hr⟩` from `intAA_of_ig h n`.

Rewrite using `[← hr]`. Conclude with `r.2`.
-/
theorem intS_iff (V : VF K) {σ : Type} (f : MvPowerSeries σ K) :
    IntS V f ↔ f ∈ Ig (intRing V) K σ := by
  constructor
  · intro h
    exact ig_of_intAA fun n => ⟨⟨_, h n⟩, rfl⟩
  · intro h n
    obtain ⟨r, hr⟩ := intAA_of_ig h n
    rw [← hr]
    exact r.2

/- English proof (translation)
Use extensionality with `n`. Simplify using `[coeff_map]`.
-/
theorem map_self {σ : Type} (f : MvPowerSeries σ K) :
    MvPowerSeries.map (algebraMap K K) f = f := by
  ext n
  simp [coeff_map]

variable [CharZero K] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

omit [CharZero K] in
/- English proof (translation)
The claim follows from `funext fun _ => map_self _`.
-/
theorem FK_self (B : FB K d O) : B.FK K = B.G.F := funext fun _ => map_self _

open GlobalTheory.GaugeSecondDeriv in

/- English proof (translation)
Establish `hA : ∀ c, constantCoeff (addOf B.G.F (pt K (n` using `3) d 1) (pt K d 2) c) = 0 := fun c => constantCoeff_ev LogPf.cz12 (B.G.const c)`. Establish `c02 : CZ (![pt K (n` using `3) d 0, pt K d 2] : Fin 2 → Pt K 3 d) := CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)`. Establish `cA : CZ (![pt K (n` using `3) d 0, addOf B.G.F (pt K (n := 3) d 1) (pt K d 2)] : Fin 2 → Pt K 3 d) := CZ.cons (cc_pt 0) (CZ.cons hA CZ.nil)`. Establish `hH0 : constantCoeff (ev (n` using `3) ![pt K d 0, pt K d 1] h + ev (n := 3) ![pt K d 0, pt K d 2] h - ev (n := 3) ![pt K d 0, addOf B.G.F (pt K d 1) (pt K d 2)] h) = 0 := by`. Rewrite using `[map_sub, map_add, cc_ev' cz01, cc_ev' c02, cc_ev' cA, cc_h hc]`.

Simplify using the standard rewrite rules. Establish `hE` using `hc.ph2`. Rewrite `hE` using `[FB.toK, map_self, FK_self]`. Establish `hH` using `pderiv_expS hH0 ((2 : Fin 3), b)`. Rewrite `hH` using `[← hE]`.

Apply the tactic sequence `have t1 : pderiv K ((2 : Fin 3), b) (ev (n := 3) ![pt K d 0, pt K d 1] h) = 0 := pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])`. Establish `t2 : ev (n` using `2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), b) (ev (n := 3) ![pt K d 0, pt K d 2] h)) = ev (n := 2) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), b) h) := by`. Rewrite using `[pderiv_ev_second h _ (cc_pt 2)]`. Simplify using `only [pderiv_pt, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[ev_ev czZ c02]`.

Use `congr 1`. Use function extensionality and compare the values at `j c`. Apply the tactic sequence `fin_cases j <;> simp [pt_apply, ev_X czZ]`. Establish `t3 : ev (n` using `2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), b) (ev (n := 3) ![pt K d 0, addOf B.G.F (pt K d 1) (pt K d 2)] h)) = ∑ j, ev (n := 2) ![pt K d 1, 0] (pderiv K ((1 : Fin 2), b) (B.G.F j)) * pderiv K ((1 : Fin 2), j) h := by`. Rewrite using `[pderiv_ev_second h _ hA, ev_sum czZ]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `e : (fun i c => ev (n` using `2) ![pt K d 0, pt K d 1, 0] ((![pt K (n := 3) d 0, addOf B.G.F (pt K (n := 3) d 1) (pt K d 2)] : Fin 2 → Pt K 3 d) i c)) = fun i => pt K (n := 2) d i := by`. Use function extensionality and compare the values at `i c`. Use `fin_cases i`. Simplify using `[pt_apply, ev_X czZ]`.

Conclude with `ev_add_axis B.G c`. Rewrite using `[ev_mul czZ, ev_ev czZ cA, e, ev_pt, mul_comm]`. Use `congr 1`. Conclude with `ev_pderiv_add (B.G.F j) b`. Rewrite using `[hH, ev_mul czZ, B.cocycleRight_zero_thd, one_mul, map_sub, map_add, t1, zero_add, ev_sub czZ, t2, t3]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem second_deriv (B : FB K d O) (h : PS K 2 d) (hc : B.IsCanonGauge K h) (b : Fin d) :
    ∑ j, ev (n := 2) ![pt K d 1, 0] (pderiv K ((1 : Fin 2), b) (B.G.F j)) *
        pderiv K ((1 : Fin 2), j) h =
      ev (n := 2) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), b) h) -
        ev (n := 2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), b) B.ph2) := by
  have hA : ∀ c, constantCoeff (addOf B.G.F (pt K (n := 3) d 1) (pt K d 2) c) = 0 :=
    fun c => constantCoeff_ev LogPf.cz12 (B.G.const c)
  have c02 : CZ (![pt K (n := 3) d 0, pt K d 2] : Fin 2 → Pt K 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)
  have cA : CZ (![pt K (n := 3) d 0, addOf B.G.F (pt K (n := 3) d 1) (pt K d 2)] :
      Fin 2 → Pt K 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons hA CZ.nil)
  have hH0 : constantCoeff (ev (n := 3) ![pt K d 0, pt K d 1] h +
      ev (n := 3) ![pt K d 0, pt K d 2] h -
      ev (n := 3) ![pt K d 0, addOf B.G.F (pt K d 1) (pt K d 2)] h) = 0 := by
    rw [map_sub, map_add, cc_ev' cz01, cc_ev' c02, cc_ev' cA, cc_h hc]
    simp
  have hE := hc.ph2
  rw [FB.toK, map_self, FK_self] at hE
  have hH := pderiv_expS hH0 ((2 : Fin 3), b)
  rw [← hE] at hH
  have t1 : pderiv K ((2 : Fin 3), b) (ev (n := 3) ![pt K d 0, pt K d 1] h) = 0 :=
    pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
  have t2 : ev (n := 2) ![pt K d 0, pt K d 1, 0]
      (pderiv K ((2 : Fin 3), b) (ev (n := 3) ![pt K d 0, pt K d 2] h)) =
      ev (n := 2) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), b) h) := by
    rw [pderiv_ev_second h _ (cc_pt 2)]
    simp only [pderiv_pt, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [ev_ev czZ c02]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X czZ]
  have t3 : ev (n := 2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), b)
      (ev (n := 3) ![pt K d 0, addOf B.G.F (pt K d 1) (pt K d 2)] h)) =
      ∑ j, ev (n := 2) ![pt K d 1, 0] (pderiv K ((1 : Fin 2), b) (B.G.F j)) *
        pderiv K ((1 : Fin 2), j) h := by
    rw [pderiv_ev_second h _ hA, ev_sum czZ]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : (fun i c => ev (n := 2) ![pt K d 0, pt K d 1, 0]
        ((![pt K (n := 3) d 0, addOf B.G.F (pt K (n := 3) d 1) (pt K d 2)] :
          Fin 2 → Pt K 3 d) i c)) = fun i => pt K (n := 2) d i := by
      funext i c
      fin_cases i
      · simp [pt_apply, ev_X czZ]
      · exact ev_add_axis B.G c
    rw [ev_mul czZ, ev_ev czZ cA, e, ev_pt, mul_comm]
    congr 1
    exact ev_pderiv_add (B.G.F j) b
  rw [hH, ev_mul czZ, B.cocycleRight_zero_thd, one_mul, map_sub, map_add, t1, zero_add, ev_sub czZ, t2, t3]
  ring

variable {V : VF K}

/- English proof (translation)
Establish `h1 : CZ (![a] : Fin 1 → Pt K n d)` using `CZ.cons ha CZ.nil`. Rewrite using `[FBChart.sgP, ev_neg h1, ev_sum h1, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `e : sgOf K Y.h i = -ev (n` using `1) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), i) Y.h) := rfl`. Rewrite using `[ev_mul h1, ev_C h1, e, ev_neg h1, mul_neg]`.
-/
theorem ev_sgP (Y : FBChart K V O d) (v : Fin d → K) {n : ℕ} (a : Pt K n d)
    (ha : ∀ i, constantCoeff (a i) = 0) :
    ev ![a] (Y.sgP v) = ∑ i, C (v i) * ev ![a] (sgOf K Y.h i) := by
  have h1 : CZ (![a] : Fin 1 → Pt K n d) := CZ.cons ha CZ.nil
  rw [FBChart.sgP, ev_neg h1, ev_sum h1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : sgOf K Y.h i = -ev (n := 1) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), i) Y.h) := rfl
  rw [ev_mul h1, ev_C h1, e, ev_neg h1, mul_neg]

omit [CharZero K] in
/- English proof (translation)
The claim follows from `sum_mem fun i _ => mul_mem (ig_C (R := intRing V) ⟨v i, hv i⟩) (ig_ev czZ integral_family_pair_zero (ig_pderiv ((intS_iff V f).1 hf) _))`.
-/
theorem int_comb (v : Fin d → K) (hv : ∀ i, V.Ge 0 (v i)) (f : PS K 3 d) (hf : IntS V f) :
    (∑ i, C (v i) * ev (n := 2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), i) f)) ∈
      Ig (intRing V) K (Fin 2 × Fin d) :=
  sum_mem fun i _ => mul_mem (ig_C (R := intRing V) ⟨v i, hv i⟩)
    (ig_ev czZ integral_family_pair_zero (ig_pderiv ((intS_iff V f).1 hf) _))

/- English proof (translation)
Introduce `v hv`. Establish `hadd : addOf Y.B.G.F (pt K (n` using `2) d 0) (pt K d 1) = Y.B.G.F := by`. Use function extensionality and compare the values at `i`. Establish `e : (![pt K (n` using `2) d 0, pt K d 1] : Fin 2 → Pt K 2 d) = fun j => pt K d j := by`. Use function extensionality and compare the values at `j`.

Apply the tactic sequence `fin_cases j <;> rfl`. Rewrite using `[addOf, e, ev_pt]`. Rewrite using `[intS_iff, hadd, ev_sgP Y v _ Y.B.G.const, ev_sgP Y v _ (cc_pt 0), ev_sgP Y v _ (cc_pt 1), ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]`. Use `int_comb v hv _ Y.intPh1 using 2 with i` and compare the differences between its conclusion and the goal. Establish `e` using `GlobalTheory.SigmaDefect.sgOf_defect Y.B Y.h Y.gauge i`.

Rewrite `e` using `[FB.toK, map_self, FK_self]`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cocycle_integral (Y : FBChart K V O d) : GermISt Y := by
  intro v hv
  have hadd : addOf Y.B.G.F (pt K (n := 2) d 0) (pt K d 1) = Y.B.G.F := by
    funext i
    have e : (![pt K (n := 2) d 0, pt K d 1] : Fin 2 → Pt K 2 d) = fun j => pt K d j := by
      funext j
      fin_cases j <;> rfl
    rw [addOf, e, ev_pt]
  rw [intS_iff, hadd, ev_sgP Y v _ Y.B.G.const, ev_sgP Y v _ (cc_pt 0), ev_sgP Y v _ (cc_pt 1),
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  convert int_comb v hv _ Y.intPh1 using 2 with i
  have e := GlobalTheory.SigmaDefect.sgOf_defect Y.B Y.h Y.gauge i
  rw [FB.toK, map_self, FK_self] at e
  rw [e]
  ring

/- English proof (translation)
Introduce `v hv`. Rewrite using `[intS_iff, ev_sgP Y v _ (cc_pt 0)]`. Use `neg_mem (int_comb v hv _ Y.intPh2) using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Finset.sum_mul]`. Rewrite using `[Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `e` using `second_deriv Y.B Y.h Y.gauge i`. Rewrite using `[GlobalTheory.SigmaDefect.ev_sgOf _ _ _ (cc_pt 0)]`. Simplify using `only [mul_assoc]`. Rewrite using `[← Finset.mul_sum, e]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem invariant_deriv_integral (Y : FBChart K V O d) : GermIISt Y := by
  intro v hv
  rw [intS_iff, ev_sgP Y v _ (cc_pt 0)]
  convert neg_mem (int_comb v hv _ Y.intPh2) using 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := second_deriv Y.B Y.h Y.gauge i
  rw [GlobalTheory.SigmaDefect.ev_sgOf _ _ _ (cc_pt 0)]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, e]
  ring

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ Y` and use `⟨cocycle_integral Y, invariant_deriv_integral Y⟩`.
-/
theorem main : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O]
    (dd : ℕ) (Y : FBChart C V O dd), GermISt Y ∧ GermIISt Y :=
  fun _ _ _ _ _ _ _ _ Y => ⟨cocycle_integral Y, invariant_deriv_integral Y⟩

end GlobalTheory.GaugeGermIntegral
