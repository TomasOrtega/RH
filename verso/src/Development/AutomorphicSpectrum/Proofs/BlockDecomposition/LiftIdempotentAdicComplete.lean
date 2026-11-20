import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.IdemLift

/- English proof (translation)
Establish `ha' : a * a = a` using `ha`. Establish `hb' : b * b = b` using `hb`. Take the linear combination `(a + 1 - 3 * b) * ha' + (3 * a - b - 1) * hb'`.
-/
theorem sub_pow_three_eq {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : (a - b) ^ 3 = a - b := by
  have ha' : a * a = a := ha
  have hb' : b * b = b := hb
  linear_combination (a + 1 - 3 * b) * ha' + (3 * a - b - 1) * hb'

/- English proof (translation)
Take `⟨n, hn⟩` from `h`. Establish `h3` using `sub_pow_three_eq ha hb`. Establish `hpow : ∀ m : ℕ, (a - b) ^ (2 * m + 1) = a - b`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simp`. Consider the case `succ m ih`. Combine the equalities or inequalities in the displayed calculation. Establish `h0 : a - b = 0`. Rewrite using `[← hpow n, show 2 * n + 1 = n + (n + 1) by ring, pow_add, hn, zero_mul]`.

Conclude with `sub_eq_zero.1 h0`.
-/
theorem eq_of_isNilpotent_sub {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) (h : IsNilpotent (a - b)) : a = b := by
  obtain ⟨n, hn⟩ := h
  have h3 := sub_pow_three_eq ha hb
  have hpow : ∀ m : ℕ, (a - b) ^ (2 * m + 1) = a - b := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc (a - b) ^ (2 * (m + 1) + 1) = (a - b) ^ (2 * m + 1) * (a - b) ^ 2 := by ring
        _ = (a - b) ^ 3 := by rw [ih]; ring
        _ = a - b := h3
  have h0 : a - b = 0 := by
    rw [← hpow n, show 2 * n + 1 = n + (n + 1) by ring, pow_add, hn, zero_mul]
  exact sub_eq_zero.1 h0

/- English proof (translation)
Establish `hu : IsUnit ((a - b) * (-(a - b)) + 1)` using `Ideal.mem_jacobson_bot.1 h _`. Establish `h3` using `sub_pow_three_eq ha hb`. Establish `hz : (a - b) * ((a - b) * (-(a - b)) + 1) = 0`. Take the linear combination `-h3`. Conclude with `sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hz)`.
-/
theorem eq_of_sub_mem_jacobson {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : a - b ∈ Ideal.jacobson (⊥ : Ideal R)) : a = b := by
  have hu : IsUnit ((a - b) * (-(a - b)) + 1) := Ideal.mem_jacobson_bot.1 h _
  have h3 := sub_pow_three_eq ha hb
  have hz : (a - b) * ((a - b) * (-(a - b)) + 1) = 0 := by
    linear_combination -h3
  exact sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hz)

/- English proof (translation)
Establish `hJI : Ideal.span {ϖ ^ k} ≤ Ideal.span {ϖ}`. Rewrite using `[Ideal.span_singleton_le_span_singleton]`. Conclude with `dvd_pow_self ϖ hk`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective e`. Establish `haJ : a * a - a ∈ Ideal.span {ϖ ^ k}`.

Apply `Ideal.Quotient.eq_zero_iff_mem.1` to reduce the goal to its premises. Establish `he' : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) a * Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ a` using `he`. Rewrite using `[map_sub, map_mul, he', sub_self]`. Establish `haI : a * a - a ∈ Ideal.span {ϖ}` using `hJI haJ`. Establish `hH : HenselianRing S (Ideal.span {ϖ})` using `IsAdicComplete.henselianRing S _`.

Establish `hmon : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).Monic`. Apply `Polynomial.monic_X_pow_sub` to reduce the goal to its premises. Simplify using `using lt_of_le_of_lt Polynomial.degree_X_le (by norm_num : (1 : WithBot ℕ) < 2)`. Establish `heval : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).eval a ∈ Ideal.span {ϖ}`. Establish `: ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).eval a = a * a - a`.

Simplify using `[sq]`. Rewrite using `[this]` and apply the resulting hypothesis. Establish `hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {ϖ}) (Polynomial.derivative ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X) |>.eval a))`. Establish `hd : (Polynomial.derivative ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X)).eval a = 2 * a - 1`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hd]`. Establish `hsq : Ideal.Quotient.mk (Ideal.span {ϖ}) (2 * a - 1) * Ideal.Quotient.mk (Ideal.span {ϖ}) (2 * a - 1) = 1`. Rewrite using `[← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {ϖ}))]`. Apply `Ideal.Quotient.eq.2` to reduce the goal to its premises.

Establish `: (2 * a - 1) * (2 * a - 1) - 1 = 4 * (a * a - a)` using `by ring`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ haI`. Conclude with `IsUnit.of_mul_eq_one _ hsq`. Take `⟨y, hy, hya⟩` from `hH.is_henselian _ hmon a heval hunit`.

Establish `hyid : IsIdempotentElem y`. Establish `: y ^ 2 - y = 0` using `by simpa [Polynomial.IsRoot] using hy`. Establish `h2 : y * y - y = 0` using `by rw [← sq]; exact this`. Conclude with `sub_eq_zero.1 h2`. Establish `hlift : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) y = Ideal.Quotient.mk _ a`.

Apply `eq_of_isNilpotent_sub (hyid.map (Ideal.Quotient.mk _)) he` to reduce the goal to its premises. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_sub, ← map_pow]`. Apply `Ideal.Quotient.eq_zero_iff_mem.2` to reduce the goal to its premises. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton.1 hya`.

Rewrite using `[hc, mul_pow]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Use `⟨y, ⟨hyid, hlift⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨hz, hza⟩`. Apply `eq_of_sub_mem_jacobson hz hyid` to reduce the goal to its premises.

Apply `IsAdicComplete.le_jacobson_bot (Ideal.span {ϖ})` to reduce the goal to its premises. Apply `hJI` to reduce the goal to its premises. Apply `Ideal.Quotient.eq.1` to reduce the goal to its premises. Rewrite using `[hza, hlift]`.
-/
theorem existsUnique_idempotent_lift {S : Type} [CommRing S] (ϖ : S)
    [IsAdicComplete (Ideal.span {ϖ}) S] (k : ℕ) (hk : k ≠ 0)
    (e : S ⧸ Ideal.span {ϖ ^ k}) (he : IsIdempotentElem e) :
    ∃! e' : S, IsIdempotentElem e' ∧ Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) e' = e := by
  have hJI : Ideal.span {ϖ ^ k} ≤ Ideal.span {ϖ} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact dvd_pow_self ϖ hk
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
  have haJ : a * a - a ∈ Ideal.span {ϖ ^ k} := by
    apply Ideal.Quotient.eq_zero_iff_mem.1
    have he' : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) a * Ideal.Quotient.mk _ a
        = Ideal.Quotient.mk _ a := he
    rw [map_sub, map_mul, he', sub_self]
  have haI : a * a - a ∈ Ideal.span {ϖ} := hJI haJ
  have hH : HenselianRing S (Ideal.span {ϖ}) := IsAdicComplete.henselianRing S _
  have hmon : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).Monic := by
    apply Polynomial.monic_X_pow_sub
    simpa using lt_of_le_of_lt Polynomial.degree_X_le (by norm_num : (1 : WithBot ℕ) < 2)
  have heval : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).eval a ∈ Ideal.span {ϖ} := by
    have : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).eval a = a * a - a := by
      simp [sq]
    rwa [this]
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {ϖ})
      (Polynomial.derivative ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X) |>.eval a)) := by
    have hd : (Polynomial.derivative ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X)).eval a
        = 2 * a - 1 := by
      simp
      ring
    rw [hd]
    have hsq : Ideal.Quotient.mk (Ideal.span {ϖ}) (2 * a - 1)
        * Ideal.Quotient.mk (Ideal.span {ϖ}) (2 * a - 1) = 1 := by
      rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {ϖ}))]
      apply Ideal.Quotient.eq.2
      have : (2 * a - 1) * (2 * a - 1) - 1 = 4 * (a * a - a) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ haI
    exact IsUnit.of_mul_eq_one _ hsq
  obtain ⟨y, hy, hya⟩ := hH.is_henselian _ hmon a heval hunit
  have hyid : IsIdempotentElem y := by
    have : y ^ 2 - y = 0 := by simpa [Polynomial.IsRoot] using hy
    have h2 : y * y - y = 0 := by rw [← sq]; exact this
    exact sub_eq_zero.1 h2
  have hlift : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) y = Ideal.Quotient.mk _ a := by
    apply eq_of_isNilpotent_sub (hyid.map (Ideal.Quotient.mk _)) he
    refine ⟨k, ?_⟩
    rw [← map_sub, ← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hya
    rw [hc, mul_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨y, ⟨hyid, hlift⟩, ?_⟩
  rintro z ⟨hz, hza⟩
  apply eq_of_sub_mem_jacobson hz hyid
  apply IsAdicComplete.le_jacobson_bot (Ideal.span {ϖ})
  apply hJI
  apply Ideal.Quotient.eq.1
  rw [hza, hlift]

end GlobalTheory.CompanionTheory.IdemLift
