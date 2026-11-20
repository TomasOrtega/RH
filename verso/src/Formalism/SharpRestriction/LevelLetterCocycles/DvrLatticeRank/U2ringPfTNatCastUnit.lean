import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfSSplit
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfC

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section U2T

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

local notation "mkI" y => Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y)

/- English proof (translation)
Establish `: CharP (IsLocalRing.ResidueField O) p` using `(CharP.charP_iff_prime_eq_zero hp.out).mpr (by`. Rewrite using `[← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]`. Conclude with `hpm)`. Assume the negation of the conclusion as `h`. Establish `hm : (s : O) ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 h`.

Rewrite `hm` using `[← IsLocalRing.residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero_iff _ p]`. Conclude with `absurd (Nat.le_of_dvd (by omega) hm) (by omega)`.
-/
theorem u2ringPfT_natCast_unit [IsLocalRing O] (p : ℕ) [hp : Fact p.Prime]
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) {s : ℕ} (hs1 : 1 ≤ s) (hsp : s < p) : IsUnit (s : O) := by
  have : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
      rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact hpm)
  by_contra h
  have hm : (s : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 h
  rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero_iff _ p] at hm
  exact absurd (Nat.le_of_dvd (by omega) hm) (by omega)

/- English proof (translation)
Establish `: Fact PD.p.Prime` using `⟨PD.hp⟩`. Take `⟨-, -, ⟨w, hw⟩, -, ⟨w₁, hq⟩, -, -, -⟩` from `hR`. Use `set p := PD.p with hpdef`. Establish `hp2 : 2 ≤ p` using `PD.hp.two_le`. Use `set π := π' c with hπdef`.

Use `set u := (w : LetA O n) c with hudef`. Establish `hu : IsUnit u` using `w.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)`. Establish `hπu : π = u * PowerSeries.X ^ s'` using `by rw [hπdef, hw]; rfl`. Use `set wq := (w₁ : LetA O n) c with hwqdef`. Establish `hwq : IsUnit wq` using `w₁.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)`.

Use `set Ec := E c with hEcdef`. Establish `hQ : W.q₀ = wq * Polynomial.aeval π Ec` using `congrFun hq c`. Use `set D := PowerSeries.derivative O with hD`. Take `⟨uv, huv⟩` from `DualFramesAlt.eigenRingInvariants.ev_exists hxm u`. Take `⟨duv, hduv⟩` from `DualFramesAlt.eigenRingInvariants.ev_exists hxm (D u)`.

Take `⟨wv, hwv⟩` from `DualFramesAlt.eigenRingInvariants.ev_exists hxm wq`. Take `⟨dwv, hdwv⟩` from `DualFramesAlt.eigenRingInvariants.ev_exists hxm (D wq)`. Take `⟨qv, hqv⟩` from `DualFramesAlt.eigenRingInvariants.ev_exists hxm W.q₀`. Take `⟨dqv, hdqv⟩` from `DualFramesAlt.eigenRingInvariants.ev_exists hxm (D W.q₀)`. Establish `hwvu : IsUnit wv` using `u2ringPfE_val_unit hxm ((PowerSeries.isUnit_iff_constantCoeff).1 hwq) hwv`.

Establish `huvu : IsUnit uv` using `u2ringPfE_val_unit hxm ((PowerSeries.isUnit_iff_constantCoeff).1 hu) huv`. Establish `hqv0 : qv = 0`. Establish `h1` using `congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia x)) W.q₀_def`. Establish `e1 : (mkI x) (PowerSeries.X * W.q₀) = (mkI x) (PowerSeries.C (x * qv))`. Rewrite using `[map_mul, DualFramesAlt.eigenRingInvariants.mk_X, hqv, ← map_mul, ← map_mul]`.

Establish `e2 : (mkI x) ((1 + PowerSeries.X) ^ p - 1) = (mkI x) (PowerSeries.C ((1 + x) ^ p - 1))`. Simplify using `only [map_sub, map_pow, map_add, map_one, DualFramesAlt.eigenRingInvariants.mk_X]`. Rewrite `h1` using `[e1, e2, hx1, sub_self]`. Conclude with `(mul_eq_zero.1 (DualFramesAlt.eigenRingInvariants.ev_inj hxm h1)).resolve_left hx0`. Establish `hyu : y = uv * x ^ s'`.

Apply `DualFramesAlt.eigenRingInvariants.ev_inj hxm` to reduce the goal to its premises. Rewrite using `[← hy, hπu, map_mul, map_pow, huv, DualFramesAlt.eigenRingInvariants.mk_X, ← map_pow, ← map_mul]`. Use `congr 1`. Rewrite using `[map_mul, map_pow]`. Establish `hEy : Ec.eval y = 0`.

Establish `h4 : (mkI x) W.q₀ = (mkI x) (PowerSeries.C (wv * Ec.eval y))`. Rewrite using `[hQ, map_mul, hwv, u2ringPfE_mk_aeval hy, ← map_mul]`. Use `congr 1`. Rewrite using `[map_mul]`. Rewrite `h4` using `[hqv, hqv0]`.

Conclude with `(mul_eq_zero.1 (DualFramesAlt.eigenRingInvariants.ev_inj hxm h4).symm).resolve_left hwvu.ne_zero`. Establish `hdX : D PowerSeries.X = 1` using `PowerSeries.derivative_X`. Establish `hd1` using `congrArg D W.q₀_def`. Rewrite `hd1` using `[Derivation.leibniz, map_sub, Derivation.leibniz_pow, Derivation.map_one_eq_zero, sub_zero, map_add, Derivation.map_one_eq_zero, zero_add, hdX]`. Establish `hd2` using `congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia x)) hd1`.

Simplify using `only [smul_eq_mul, mul_one, nsmul_eq_mul, map_add, map_mul, map_pow, map_natCast, DualFramesAlt.eigenRingInvariants.mk_X, hqv, hdqv, hqv0, map_one] at hd2`. Establish `hDπ : D π = u * ((s' : PowerSeries O) * PowerSeries.X ^ (s' - 1)) + PowerSeries.X ^ s' * D u`. Rewrite using `[hπu, Derivation.leibniz, Derivation.leibniz_pow, hdX]`. Simplify using `only [smul_eq_mul, nsmul_eq_mul, mul_one]`. Apply the tactic sequence `try ring`.

Establish `hdq` using `congrArg D hQ`. Rewrite `hdq` using `[Derivation.leibniz, Derivation.map_aeval, hDπ]`. Establish `hdq2` using `congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia x)) hdq`. Simplify using `only [smul_eq_mul, map_add, map_mul, map_pow, map_natCast, DualFramesAlt.eigenRingInvariants.mk_X, hdqv, hwv, hduv, huv, u2ringPfE_mk_aeval hy, hEy] at hdq2`. Establish `e1 : x * dqv = (p : O) * (1 + x) ^ (p - 1)`.

Apply `DualFramesAlt.eigenRingInvariants.ev_inj hxm` to reduce the goal to its premises. Simplify using `only [map_mul, map_pow, map_add, map_one, map_natCast]`. Simplify using `only [map_zero, add_zero] at hd2`. Take the linear combination `hd2`. Establish `e2 : dqv = wv * ((Ec.derivative.eval y) * (uv * ((s' : O) * x ^ (s' - 1)) + x ^ s' * duv))`.

Apply `DualFramesAlt.eigenRingInvariants.ev_inj hxm` to reduce the goal to its premises. Simplify using `only [map_mul, map_pow, map_add, map_natCast]`. Simplify using `only [map_zero, zero_mul, add_zero] at hdq2`. Take the linear combination `hdq2`. Establish `hs'u : IsUnit (s' : O)` using `u2ringPfT_natCast_unit p hpm hs (by`.

Establish `: 1 ≤ e`. Break down `Nat.eq_zero_or_pos e with h | h` into its components or cases. Rewrite `hes` using `[h, zero_mul]`. Use linear arithmetic over natural numbers and integers. Conclude with `h`.

Establish `: s' ≤ e * s'` using `Nat.le_mul_of_pos_left s' this`. Use the proof step `omega)`. Establish `hD0 : IsUnit (wv * (uv * (s' : O) + x * duv))`. Use `hwvu.mul ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`.

Establish `hm : uv * (s' : O) + x * duv ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 hn`. Establish `hm2 : uv * (s' : O) ∈ IsLocalRing.maximalIdeal O`. Use `Ideal.sub_mem _ hm (Ideal.mul_mem_right duv _ hxm)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right]`. Then use the resulting hypothesis. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 hm2 (huvu.mul hs'u)`.

Establish `h1xe : (1 + x) * (1 + x) ^ (p - 1) = 1`. Rewrite using `[← pow_succ', Nat.sub_add_cancel (by omega), hx1]`. Establish `h1x : IsUnit (1 + x)` using `⟨⟨1 + x, (1 + x) ^ (p - 1), h1xe, by rw [mul_comm]; exact h1xe⟩, rfl⟩`. Take `⟨Du, hDu⟩` from `hD0`. Use `⟨uv * (1 + x) ^ (p - 1) * ((Du⁻¹ : Oˣ) : O), (huvu.mul (h1x.pow _)).mul (Du⁻¹).isUnit, ?_⟩` and prove the remaining obligations.

Establish `key : y * Ec.derivative.eval y * (wv * (uv * (s' : O) + x * duv)) = (p : O) * (uv * (1 + x) ^ (p - 1))`. Take `⟨s'', rfl⟩ : ∃ s'', s' = s'' + 1` from `⟨s' - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel] at e2`. Take the linear combination `(Ec.derivative.eval y * (wv * (uv * ((s'' + 1 : ℕ) : O) + x * duv))) * hyu - (uv * x) * e2 + uv * e1`. Establish `hDuinv : ((Du : Oˣ) : O) * ((Du⁻¹ : Oˣ) : O) = 1` using `Units.mul_inv Du`.

Rewrite `hDuinv` using `[hDu]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem u2ringPfT_deriv [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hes : e * s' = PD.p - 1)
    (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (c : ZMod n) {x y : O}
    (hxm : x ∈ IsLocalRing.maximalIdeal O) (hx1 : (1 + x) ^ PD.p = 1) (hx0 : x ≠ 0)
    (hy : (mkI x) (π' c) = (mkI x) (PowerSeries.C y)) :
    ∃ ε : O, IsUnit ε ∧ y * (E c).derivative.eval y = (PD.p : O) * ε := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨-, -, ⟨w, hw⟩, -, ⟨w₁, hq⟩, -, -, -⟩ := hR
  set p := PD.p with hpdef
  have hp2 : 2 ≤ p := PD.hp.two_le
  set π := π' c with hπdef
  set u := (w : LetA O n) c with hudef
  have hu : IsUnit u := w.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)
  have hπu : π = u * PowerSeries.X ^ s' := by rw [hπdef, hw]; rfl
  set wq := (w₁ : LetA O n) c with hwqdef
  have hwq : IsUnit wq := w₁.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)
  set Ec := E c with hEcdef
  have hQ : W.q₀ = wq * Polynomial.aeval π Ec := congrFun hq c
  set D := PowerSeries.derivative O with hD
  obtain ⟨uv, huv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm u
  obtain ⟨duv, hduv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm (D u)
  obtain ⟨wv, hwv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm wq
  obtain ⟨dwv, hdwv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm (D wq)
  obtain ⟨qv, hqv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm W.q₀
  obtain ⟨dqv, hdqv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm (D W.q₀)
  have hwvu : IsUnit wv := u2ringPfE_val_unit hxm ((PowerSeries.isUnit_iff_constantCoeff).1 hwq) hwv
  have huvu : IsUnit uv := u2ringPfE_val_unit hxm ((PowerSeries.isUnit_iff_constantCoeff).1 hu) huv

  have hqv0 : qv = 0 := by
    have h1 := congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia x)) W.q₀_def
    have e1 : (mkI x) (PowerSeries.X * W.q₀) = (mkI x) (PowerSeries.C (x * qv)) := by
      rw [map_mul, DualFramesAlt.eigenRingInvariants.mk_X, hqv, ← map_mul, ← map_mul]
    have e2 : (mkI x) ((1 + PowerSeries.X) ^ p - 1) = (mkI x) (PowerSeries.C ((1 + x) ^ p - 1)) := by
      simp only [map_sub, map_pow, map_add, map_one, DualFramesAlt.eigenRingInvariants.mk_X]
    rw [e1, e2, hx1, sub_self] at h1
    exact (mul_eq_zero.1 (DualFramesAlt.eigenRingInvariants.ev_inj hxm h1)).resolve_left hx0

  have hyu : y = uv * x ^ s' := by
    apply DualFramesAlt.eigenRingInvariants.ev_inj hxm
    rw [← hy, hπu, map_mul, map_pow, huv, DualFramesAlt.eigenRingInvariants.mk_X, ← map_pow, ← map_mul]
    congr 1
    rw [map_mul, map_pow]
  have hEy : Ec.eval y = 0 := by
    have h4 : (mkI x) W.q₀ = (mkI x) (PowerSeries.C (wv * Ec.eval y)) := by
      rw [hQ, map_mul, hwv, u2ringPfE_mk_aeval hy, ← map_mul]
      congr 1
      rw [map_mul]
    rw [hqv, hqv0] at h4
    exact (mul_eq_zero.1 (DualFramesAlt.eigenRingInvariants.ev_inj hxm h4).symm).resolve_left hwvu.ne_zero

  have hdX : D PowerSeries.X = 1 := PowerSeries.derivative_X
  have hd1 := congrArg D W.q₀_def
  rw [Derivation.leibniz, map_sub, Derivation.leibniz_pow, Derivation.map_one_eq_zero, sub_zero, map_add,
    Derivation.map_one_eq_zero, zero_add, hdX] at hd1
  have hd2 := congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia x)) hd1
  simp only [smul_eq_mul, mul_one, nsmul_eq_mul, map_add, map_mul, map_pow, map_natCast,
    DualFramesAlt.eigenRingInvariants.mk_X, hqv, hdqv, hqv0, map_one] at hd2
  have hDπ : D π = u * ((s' : PowerSeries O) * PowerSeries.X ^ (s' - 1)) + PowerSeries.X ^ s' * D u := by
    rw [hπu, Derivation.leibniz, Derivation.leibniz_pow, hdX]
    simp only [smul_eq_mul, nsmul_eq_mul, mul_one]
    try ring
  have hdq := congrArg D hQ
  rw [Derivation.leibniz, Derivation.map_aeval, hDπ] at hdq
  have hdq2 := congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia x)) hdq
  simp only [smul_eq_mul, map_add, map_mul, map_pow, map_natCast, DualFramesAlt.eigenRingInvariants.mk_X, hdqv, hwv, hduv, huv,
    u2ringPfE_mk_aeval hy, hEy] at hdq2

  have e1 : x * dqv = (p : O) * (1 + x) ^ (p - 1) := by
    apply DualFramesAlt.eigenRingInvariants.ev_inj hxm
    simp only [map_mul, map_pow, map_add, map_one, map_natCast]
    simp only [map_zero, add_zero] at hd2
    linear_combination hd2
  have e2 : dqv = wv * ((Ec.derivative.eval y) * (uv * ((s' : O) * x ^ (s' - 1)) + x ^ s' * duv)) := by
    apply DualFramesAlt.eigenRingInvariants.ev_inj hxm
    simp only [map_mul, map_pow, map_add, map_natCast]
    simp only [map_zero, zero_mul, add_zero] at hdq2
    linear_combination hdq2
  have hs'u : IsUnit (s' : O) := u2ringPfT_natCast_unit p hpm hs (by
    have : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · rw [h, zero_mul] at hes; omega
      · exact h
    have : s' ≤ e * s' := Nat.le_mul_of_pos_left s' this
    omega)
  have hD0 : IsUnit (wv * (uv * (s' : O) + x * duv)) := by
    refine hwvu.mul ?_
    by_contra hn
    have hm : uv * (s' : O) + x * duv ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hn
    have hm2 : uv * (s' : O) ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ hm (Ideal.mul_mem_right duv _ hxm)
      rwa [add_sub_cancel_right] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 hm2 (huvu.mul hs'u)
  have h1xe : (1 + x) * (1 + x) ^ (p - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega), hx1]
  have h1x : IsUnit (1 + x) := ⟨⟨1 + x, (1 + x) ^ (p - 1), h1xe, by rw [mul_comm]; exact h1xe⟩, rfl⟩
  obtain ⟨Du, hDu⟩ := hD0
  refine ⟨uv * (1 + x) ^ (p - 1) * ((Du⁻¹ : Oˣ) : O), (huvu.mul (h1x.pow _)).mul (Du⁻¹).isUnit, ?_⟩
  have key : y * Ec.derivative.eval y * (wv * (uv * (s' : O) + x * duv)) = (p : O) * (uv * (1 + x) ^ (p - 1)) := by
    obtain ⟨s'', rfl⟩ : ∃ s'', s' = s'' + 1 := ⟨s' - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at e2
    linear_combination (Ec.derivative.eval y * (wv * (uv * ((s'' + 1 : ℕ) : O) + x * duv))) * hyu -
      (uv * x) * e2 + uv * e1
  have hDuinv : ((Du : Oˣ) : O) * ((Du⁻¹ : Oˣ) : O) = 1 := Units.mul_inv Du
  rw [hDu] at hDuinv
  calc y * Ec.derivative.eval y = y * Ec.derivative.eval y * ((wv * (uv * (s' : O) + x * duv)) *
        ((Du⁻¹ : Oˣ) : O)) := by rw [hDuinv, mul_one]
    _ = (p : O) * (uv * (1 + x) ^ (p - 1) * ((Du⁻¹ : Oˣ) : O)) := by rw [← mul_assoc, key]; ring

/- English proof (translation)
Establish `: Fact PD.p.Prime` using `⟨PD.hp⟩`. Take `⟨a, r, ha, hrm, hsplit, hpt⟩` from `u2ringPfS_split W hR hs hes hpm c ζ hζ`. Use `⟨a, r, ha, hrm, hsplit, ?_⟩` and prove the remaining obligations. Introduce `j w₀ hw₀ t ht`. Take `⟨x, hxm, hx1, hx0, hxy⟩` from `hpt j`.

Take `⟨ε, hε, hyE⟩` from `u2ringPfT_deriv W hR hs hes hpm c hxm hx1 hx0 hxy`. Establish `hder : (E c).derivative.eval (r j) = a * ∏ j' ∈ Finset.univ.erase j, (r j - r j')`. Rewrite using `[hsplit, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add, Polynomial.derivative_prod_finset, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finset_sum]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single j]`.

Simplify using `[Polynomial.eval_prod]`. Introduce `b _ hb`. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_prod]`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_erase.2 ⟨fun h => hb h.symm, Finset.mem_univ j⟩) (by simp)]`. Simplify using the standard rewrite rules.

Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`. Rewrite `hyE` using `[hder]`. Establish `hxt : (1 + r j * w₀ * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j')) - 1 = ((PD.p : ℕ) : O) * (w₀ * ε)`. Take the linear combination `w₀ * hyE`.

Take `⟨ε', hε', he'⟩` from `gradNPf_lte v (algebraMap O LL) hι hRv PD.p hp2 W.v_l _ (w₀ * ε) (hw₀.mul hε) hxt t (by omega)`. Introduce `h1`. Rewrite `he'` using `[h1, sub_self]`. Establish `hp0 : ((PD.p : ℕ) : O) ≠ 0` using `Nat.cast_ne_zero.2 PD.hp.ne_zero`. Conclude with `(mul_ne_zero (pow_ne_zero _ hp0) hε'.ne_zero) he'.symm`.
-/
theorem u2ringPfT_split [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hes : e * s' = PD.p - 1)
    (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (c : ZMod n) (ζ : O)
    (hζ : IsPrimitiveRoot ζ PD.p) (hp2 : PD.p ≠ 2) (hι : Function.Injective (algebraMap O LL))
    (hRv : ∀ x : LL, 0 ≤ v x ↔ ∃ a : O, algebraMap O LL a = x) :
    ∃ (a : O) (r : Fin e → O), IsUnit a ∧ (∀ j, r j ∈ IsLocalRing.maximalIdeal O) ∧
      E c = Polynomial.C a * ∏ j, (Polynomial.X - Polynomial.C (r j)) ∧
      ∀ (j : Fin e) (w₀ : O), IsUnit w₀ → ∀ t : ℕ, 0 < t →
        (1 + r j * w₀ * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j')) ^ t ≠ 1 := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨a, r, ha, hrm, hsplit, hpt⟩ := u2ringPfS_split W hR hs hes hpm c ζ hζ
  refine ⟨a, r, ha, hrm, hsplit, ?_⟩
  intro j w₀ hw₀ t ht
  obtain ⟨x, hxm, hx1, hx0, hxy⟩ := hpt j
  obtain ⟨ε, hε, hyE⟩ := u2ringPfT_deriv W hR hs hes hpm c hxm hx1 hx0 hxy
  have hder : (E c).derivative.eval (r j) = a * ∏ j' ∈ Finset.univ.erase j, (r j - r j') := by
    rw [hsplit, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
      Polynomial.derivative_prod_finset, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finset_sum]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp [Polynomial.eval_prod]
    · intro b _ hb
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨fun h => hb h.symm, Finset.mem_univ j⟩) (by simp)]
      simp
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hder] at hyE
  have hxt : (1 + r j * w₀ * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j')) - 1 = ((PD.p : ℕ) : O) * (w₀ * ε) := by
    linear_combination w₀ * hyE
  obtain ⟨ε', hε', he'⟩ := gradNPf_lte v (algebraMap O LL) hι hRv PD.p hp2 W.v_l _ (w₀ * ε) (hw₀.mul hε) hxt t
    (by omega)
  intro h1
  rw [h1, sub_self] at he'
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.2 PD.hp.ne_zero
  exact (mul_ne_zero (pow_ne_zero _ hp0) hε'.ne_zero) he'.symm

end U2T

end Formalism.MainNotions.N.Ln34
