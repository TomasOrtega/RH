import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Establish `key : ∀ f : W⟦X⟧, Ideal.Quotient.mk (Ideal.span {E}) (X : W⟦X⟧) ∣ Ideal.Quotient.mk (Ideal.span {E}) f ↔ p ∣ constantCoeff f`. Introduce `f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective c`.

Rewrite `hc` using `[← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Take `⟨d, hd⟩` from `hc`. Establish `h` using `congrArg constantCoeff hd`. Simplify using `only [map_sub, map_mul, constantCoeff_X, zero_mul, sub_zero, hE] at h`. Conclude with `⟨w * constantCoeff d, by rw [h, mul_assoc]⟩`.

Introduce and unpack `⟨c, hc⟩`. Establish `h0 : constantCoeff (f - E * C (((w⁻¹ : Wˣ) : W) * c)) = 0`. Simplify using `only [map_sub, map_mul, constantCoeff_C, hE, hc]`. Rewrite using `[mul_assoc, ← mul_assoc (w : W), Units.mul_inv, one_mul, sub_self]`. Take `⟨g, hg⟩` from `X_dvd_iff.2 h0`.

Use `⟨Ideal.Quotient.mk _ g, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Conclude with `⟨C (((w⁻¹ : Wˣ) : W) * c), by rw [← hg]; ring⟩`. Use `⟨fun h => ?_, fun h => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Rewrite `h` using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`.

Take `⟨c, hc⟩` from `h`. Establish `h1` using `congrArg constantCoeff hc`. Simplify using `only [map_mul, constantCoeff_X, hE] at h1`. Establish `h2 : constantCoeff c = 0` using `(mul_eq_zero.1 h1.symm).resolve_left (mul_ne_zero hp.ne_zero w.ne_zero)`. Take `⟨g, rfl⟩` from `X_dvd_iff.2 h2`.

Establish `h3 : (1 : W⟦X⟧) = E * g`. Apply `mul_left_cancel₀ (X_ne_zero (R := W))` to reduce the goal to its premises. Rewrite using `[mul_one]`. Take the linear combination `hc`. Establish `h4` using `congrArg constantCoeff h3`.

Simplify using `only [map_mul, map_one, hE] at h4`. Conclude with `hp.not_isUnit (isUnit_of_dvd_one ⟨w * constantCoeff g, by rw [h4, mul_assoc]⟩)`. Establish `h1` using `(key 1).1 h.dvd`. Rewrite `h1` using `[map_one]`. Conclude with `hp.not_isUnit (isUnit_of_dvd_one h1)`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Rewrite `hab` using `[← map_mul, key, map_mul]`. Rewrite using `[key, key]`. Conclude with `hp.dvd_or_dvd hab`.
-/
theorem prime_mk_X_of_constantCoeff {W : Type} [CommRing W] [IsDomain W] {p : W} (hp : Prime p) (E : W⟦X⟧)
    (w : Wˣ) (hE : constantCoeff E = p * w) :
    Prime (Ideal.Quotient.mk (Ideal.span {E}) (X : W⟦X⟧)) := by
  have key : ∀ f : W⟦X⟧, Ideal.Quotient.mk (Ideal.span {E}) (X : W⟦X⟧) ∣ Ideal.Quotient.mk (Ideal.span {E}) f ↔
      p ∣ constantCoeff f := by
    intro f
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
      obtain ⟨d, hd⟩ := hc
      have h := congrArg constantCoeff hd
      simp only [map_sub, map_mul, constantCoeff_X, zero_mul, sub_zero, hE] at h
      exact ⟨w * constantCoeff d, by rw [h, mul_assoc]⟩
    · rintro ⟨c, hc⟩
      have h0 : constantCoeff (f - E * C (((w⁻¹ : Wˣ) : W) * c)) = 0 := by
        simp only [map_sub, map_mul, constantCoeff_C, hE, hc]
        rw [mul_assoc, ← mul_assoc (w : W), Units.mul_inv, one_mul, sub_self]
      obtain ⟨g, hg⟩ := X_dvd_iff.2 h0
      refine ⟨Ideal.Quotient.mk _ g, ?_⟩
      rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact ⟨C (((w⁻¹ : Wˣ) : W) * c), by rw [← hg]; ring⟩
  refine ⟨fun h => ?_, fun h => ?_, fun a b hab => ?_⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    have h1 := congrArg constantCoeff hc
    simp only [map_mul, constantCoeff_X, hE] at h1
    have h2 : constantCoeff c = 0 :=
      (mul_eq_zero.1 h1.symm).resolve_left (mul_ne_zero hp.ne_zero w.ne_zero)
    obtain ⟨g, rfl⟩ := X_dvd_iff.2 h2
    have h3 : (1 : W⟦X⟧) = E * g := by
      apply mul_left_cancel₀ (X_ne_zero (R := W))
      rw [mul_one]
      linear_combination hc
    have h4 := congrArg constantCoeff h3
    simp only [map_mul, map_one, hE] at h4
    exact hp.not_isUnit (isUnit_of_dvd_one ⟨w * constantCoeff g, by rw [h4, mul_assoc]⟩)
  · have h1 := (key 1).1 h.dvd
    rw [map_one] at h1
    exact hp.not_isUnit (isUnit_of_dvd_one h1)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, key, map_mul] at hab
    rw [key, key]
    exact hp.dvd_or_dvd hab

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Take `⟨w, hw⟩` from `bk.coeff_zero`. Establish `hp : Prime (l : Wq l bk.a)` using `(WittVector.irreducible l).prime`. Establish `hE : constantCoeff bk.E = (l : Wq l bk.a) * w`. Rewrite using `[← hw]`.

Conclude with `Polynomial.constantCoeff_coe _`. Conclude with `(MulEquiv.prime_iff bk.str.symm).2 (prime_mk_X_of_constantCoeff hp bk.E w hE)`. Rewrite using `[← bk.θ_ev _ X (bk.str.apply_symm_apply _).symm, bk.ev_X]`. Conclude with `WittVector.fontaineTheta_teichmuller _`.
-/
theorem BK.prime_unif (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) :
    Prime (bk.str.symm (Ideal.Quotient.mk _ (X : bk.S))) ∧
      intToOC K (bk.str.symm (Ideal.Quotient.mk _ (X : bk.S))) = bk.flat.untilt := by
  constructor
  · obtain ⟨w, hw⟩ := bk.coeff_zero
    have hp : Prime (l : Wq l bk.a) := (WittVector.irreducible l).prime
    have hE : constantCoeff bk.E = (l : Wq l bk.a) * w := by
      rw [← hw]; exact Polynomial.constantCoeff_coe _
    exact (MulEquiv.prime_iff bk.str.symm).2 (prime_mk_X_of_constantCoeff hp bk.E w hE)
  · rw [← bk.θ_ev _ X (bk.str.apply_symm_apply _).symm, bk.ev_X]
    exact WittVector.fontaineTheta_teichmuller _

end GlobalTheory.BSP
