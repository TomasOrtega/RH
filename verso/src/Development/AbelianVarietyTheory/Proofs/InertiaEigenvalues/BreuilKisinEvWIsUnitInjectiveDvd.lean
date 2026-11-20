import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.BK

section Red

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

def evRed : bk.S →+* OCb l := (WittVector.constantCoeff (p := l) (R := OCb l)).comp bk.ev

/- English proof (translation)
Simplify using `[evRed, bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`.
-/
theorem evRed_X : bk.evRed X = bk.flat := by
  simp [evRed, bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

/- English proof (translation)
Introduce `h0`. Establish `hX : bk.ev X = 0` using `by rw [bk.ev_X, h0]; exact WittVector.teichmuller_zero l`. Take `⟨w, hw⟩` from `bk.coeff_zero`. Establish `hE : bk.ev bk.E = (l : Ainf l) * wA l bk.a (w : Wq l bk.a)` using `by conv_lhs => rw [eq_X_mul_shift_add_const bk.E]`. Rewrite using `[map_add, map_mul, hX, zero_mul, zero_add, bk.ev_C, Polynomial.constantCoeff_coe, hw, map_mul, map_natCast]`.

Establish `hl' : (l : Ainf l) ∈ RingHom.ker (Per.θ l)`. Rewrite using `[← bk.span_ev, hE, Ideal.span_singleton_mul_right_unit ((w.isUnit).map (wA l bk.a))]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `hl'` using `[RingHom.mem_ker, map_natCast]`. Conclude with `Nat.cast_ne_zero.2 hl.out.ne_zero hl'`.
-/
theorem flat_ne_zero : bk.flat ≠ 0 := by
  intro h0
  have hX : bk.ev X = 0 := by rw [bk.ev_X, h0]; exact WittVector.teichmuller_zero l
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hE : bk.ev bk.E = (l : Ainf l) * wA l bk.a (w : Wq l bk.a) := by
    conv_lhs => rw [eq_X_mul_shift_add_const bk.E]
    rw [map_add, map_mul, hX, zero_mul, zero_add, bk.ev_C, Polynomial.constantCoeff_coe, hw, map_mul,
      map_natCast]
  have hl' : (l : Ainf l) ∈ RingHom.ker (Per.θ l) := by
    rw [← bk.span_ev, hE, Ideal.span_singleton_mul_right_unit ((w.isUnit).map (wA l bk.a))]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_natCast] at hl'
  exact Nat.cast_ne_zero.2 hl.out.ne_zero hl'

/- English proof (translation)
Use `set r := WittVector.constantCoeff (p := l) (R := Fq l bk.a) with hr`. Distinguish the cases in `h : PowerSeries.map r x = 0`. Conclude with `dvd_of_map_eq_zero l bk.a x h`. It suffices to derive a contradiction. Use `set xb := PowerSeries.map r x with hxb`.

Use `set m := xb.order.toNat`. Use `set vb := divXPowOrder xb`. Establish `hvb : constantCoeff vb ≠ 0` using `fun h' => h (constantCoeff_divXPowOrder_eq_zero_iff.1 h')`. Set `v : bk.S` to `PowerSeries.mk fun n => WittVector.teichmuller l (coeff n vb)`. Establish `hv : PowerSeries.map r v = vb`.

Use extensionality with `n`. Simplify using `[v, hr, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`. Establish `hvu : IsUnit v`. Rewrite using `[isUnit_iff_constantCoeff]`. Establish `: constantCoeff v = WittVector.teichmuller l (constantCoeff vb)`.

Simplify using `[v, ← coeff_zero_eq_constantCoeff]`. Rewrite using `[this]`. Conclude with `(Ne.isUnit hvb).map _`. Take `⟨y, hy⟩` from `dvd_of_map_eq_zero l bk.a (x - X ^ m * v) (by`. Rewrite using `[map_sub, map_mul, map_pow, PowerSeries.map_X, hv, X_pow_order_mul_divXPowOrder, sub_self])`.

Establish `h1 : bk.evRed x = bk.flat ^ m * bk.evRed v`. Establish `: x = X ^ m * v + (l : bk.S) * y` using `by linear_combination hy`. Rewrite using `[this, map_add, map_mul, map_mul, map_pow, evRed_X, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]`. Rewrite `h1` using `[hx]`. Conclude with `mul_ne_zero (pow_ne_zero _ bk.flat_ne_zero) (hvu.map bk.evRed).ne_zero h1.symm`.
-/
theorem dvd_of_evRed_eq_zero (x : bk.S) (hx : bk.evRed x = 0) : (l : bk.S) ∣ x := by
  set r := WittVector.constantCoeff (p := l) (R := Fq l bk.a) with hr
  by_cases h : PowerSeries.map r x = 0
  · exact dvd_of_map_eq_zero l bk.a x h
  exfalso
  set xb := PowerSeries.map r x with hxb
  set m := xb.order.toNat
  set vb := divXPowOrder xb
  have hvb : constantCoeff vb ≠ 0 := fun h' => h (constantCoeff_divXPowOrder_eq_zero_iff.1 h')
  let v : bk.S := PowerSeries.mk fun n => WittVector.teichmuller l (coeff n vb)
  have hv : PowerSeries.map r v = vb := by
    ext n
    simp [v, hr, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  have hvu : IsUnit v := by
    rw [isUnit_iff_constantCoeff]
    have : constantCoeff v = WittVector.teichmuller l (constantCoeff vb) := by
      simp [v, ← coeff_zero_eq_constantCoeff]
    rw [this]
    exact (Ne.isUnit hvb).map _
  obtain ⟨y, hy⟩ := dvd_of_map_eq_zero l bk.a (x - X ^ m * v) (by
    rw [map_sub, map_mul, map_pow, PowerSeries.map_X, hv, X_pow_order_mul_divXPowOrder, sub_self])
  have h1 : bk.evRed x = bk.flat ^ m * bk.evRed v := by
    have : x = X ^ m * v + (l : bk.S) * y := by linear_combination hy
    rw [this, map_add, map_mul, map_mul, map_pow, evRed_X, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
  rw [hx] at h1
  exact mul_ne_zero (pow_ne_zero _ bk.flat_ne_zero) (hvu.map bk.evRed).ne_zero h1.symm

/- English proof (translation)
Apply `bk.dvd_of_evRed_eq_zero` to reduce the goal to its premises. Take `⟨z, hz⟩` from `h`. Simplify using `only [evRed, RingHom.comp_apply, hz, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]`.
-/
theorem dvd_of_dvd_ev (x : bk.S) (h : (l : Ainf l) ∣ bk.ev x) : (l : bk.S) ∣ x := by
  apply bk.dvd_of_evRed_eq_zero
  obtain ⟨z, hz⟩ := h
  simp only [evRed, RingHom.comp_apply, hz, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

/- English proof (translation)
Assume the negation of the conclusion as `hw`. Take `⟨m, b, hb0, hb⟩` from `WittVector.exists_eq_pow_p_mul w hw`. Take `⟨c, hc⟩` from `h (m + 1)`. Establish `hbc : b = (l : Wq l bk.a) * c`. Apply `mul_left_cancel₀ (pow_ne_zero m (WittVector.p_nonzero l (Fq l bk.a)))` to reduce the goal to its premises.

Rewrite using `[← hb, hc]`. Expand and normalize the polynomial expressions, which then agree. Apply `hb0` to reduce the goal to its premises. Use `congrArg (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) hbc` as an intermediate fact. Rewrite `this` using `[map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, WittVector.constantCoeff_apply]`. Then use the resulting hypothesis.
-/
theorem eq_zero_of_forall_pow_dvd (w : Wq l bk.a) (h : ∀ n : ℕ, (l : Wq l bk.a) ^ n ∣ w) : w = 0 := by
  by_contra hw
  obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul w hw
  obtain ⟨c, hc⟩ := h (m + 1)
  have hbc : b = (l : Wq l bk.a) * c := by
    apply mul_left_cancel₀ (pow_ne_zero m (WittVector.p_nonzero l (Fq l bk.a)))
    rw [← hb, hc]; ring
  apply hb0
  have := congrArg (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) hbc
  rwa [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, WittVector.constantCoeff_apply] at this

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `key : ∀ n : ℕ, ∀ x : bk.S, bk.ev x = 0 → (l : bk.S) ^ n ∣ x`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro x _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `x hx`. Take `⟨x', rfl⟩` from `bk.dvd_of_dvd_ev x (by rw [hx]; exact dvd_zero _)`.

Establish `h2 : bk.ev x' = 0` using `ainf_torsionFree _ (by rw [← map_natCast bk.ev, ← map_mul]; exact hx)`. Take `⟨z, hz⟩` from `ih x' h2`. Conclude with `⟨z, by rw [hz, pow_succ]; ring⟩`. Use `PowerSeries.ext fun k => ?_` and prove the remaining obligations. Rewrite using `[map_zero]`.

Use `bk.eq_zero_of_forall_pow_dvd _ fun n => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `key n x hx`. Use `⟨coeff k z, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, ← map_natCast (C : Wq l bk.a →+* (Wq l bk.a)⟦X⟧), ← map_pow, coeff_C_mul]`.
-/
theorem ev_injective : Function.Injective bk.ev := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have key : ∀ n : ℕ, ∀ x : bk.S, bk.ev x = 0 → (l : bk.S) ^ n ∣ x := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      obtain ⟨x', rfl⟩ := bk.dvd_of_dvd_ev x (by rw [hx]; exact dvd_zero _)
      have h2 : bk.ev x' = 0 := ainf_torsionFree _ (by rw [← map_natCast bk.ev, ← map_mul]; exact hx)
      obtain ⟨z, hz⟩ := ih x' h2
      exact ⟨z, by rw [hz, pow_succ]; ring⟩
  refine PowerSeries.ext fun k => ?_
  rw [map_zero]
  refine bk.eq_zero_of_forall_pow_dvd _ fun n => ?_
  obtain ⟨z, hz⟩ := key n x hx
  refine ⟨coeff k z, ?_⟩
  rw [hz, ← map_natCast (C : Wq l bk.a →+* (Wq l bk.a)⟦X⟧), ← map_pow, coeff_C_mul]

end Red

/- English proof (translation)
Introduce `_ _ _ bk` and use `⟨isUnit_inclW_of_span bk.span_ev, GlobalTheory.Prism.inclW_injective.comp bk.ev_injective, bk.dvd_of_dvd_ev⟩`.
-/
theorem evW_isUnit_injective_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    IsUnit (bk.evW bk.E) ∧ Function.Injective bk.evW ∧
      ∀ x : bk.S, ((l : ℕ) : Ainf l) ∣ bk.ev x → ((l : ℕ) : bk.S) ∣ x :=
  fun _ _ _ bk => ⟨isUnit_inclW_of_span bk.span_ev, GlobalTheory.Prism.inclW_injective.comp bk.ev_injective,
    bk.dvd_of_dvd_ev⟩

end GlobalTheory.BSP.BK
