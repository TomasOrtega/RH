import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

noncomputable section

open NumberField nonZeroDivisors

namespace UpperTheory.Gal.W2.Seed

/- English proof (translation)
Establish `h1ne : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `one_ne_zero`. Use `set D : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.dual ℤ ℚ 1 with hDdef`. Establish `hD : D ≠ 0` using `FractionalIdeal.dual_ne_zero ℤ ℚ h1ne`. Establish `hmem : ∀ z : E, InCodiff z ↔ z ∈ D`. Introduce `z`.

Unfold `InCodiff`. Rewrite using `[hDdef, FractionalIdeal.mem_dual h1ne]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `h b hb`. Take `⟨x, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hb`.

Take `⟨m, hm⟩` from `h x`. Conclude with `⟨m, by simpa [Algebra.traceForm_apply] using hm.symm⟩`. Introduce `h x`. Take `⟨m, hm⟩` from `h (x : E) ((FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩)`. Conclude with `⟨m, by simpa [Algebra.traceForm_apply] using hm.symm⟩`.

Use `set d : E := algebraMap (𝓞 E) E (D.den : 𝓞 E) with hddef`. Establish `hd0 : d ≠ 0`. Rewrite using `[hddef]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.coe_ne_zero _)`. Establish `key` using `FractionalIdeal.den_mul_self_eq_num' (𝓞 E)⁰ E D`.

Establish `key2 : D = FractionalIdeal.spanSingleton (𝓞 E)⁰ d⁻¹ * (D.num : FractionalIdeal (𝓞 E)⁰ E)`. Rewrite using `[← key, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hd0, FractionalIdeal.spanSingleton_one, one_mul]`. Use `⟨(D.den : 𝓞 E), D.num, nonZeroDivisors.coe_ne_zero _, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hD` to reduce the goal to its premises.

Rewrite using `[← FractionalIdeal.num_eq_zero_iff]`. Conclude with `h`. Introduce `z`. Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion.

Introduce `hz`. Establish `h1 : d * z ∈ (D.num : FractionalIdeal (𝓞 E)⁰ E)`. Rewrite using `[← key]`. Conclude with `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hz`. Take `⟨j, hj, hjeq⟩` from `(FractionalIdeal.mem_coeIdeal _).1 h1`.

Use `⟨j, hj, ?_⟩` and prove the remaining obligations. Establish `h2 : (j : E) = d * z` using `hjeq`. Establish `h3 : ((D.den : 𝓞 E) : E) = d` using `rfl`. Rewrite using `[h3, h2, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]`. Introduce and unpack `⟨j, hj, hz⟩`.

Establish `h4 : d⁻¹ * (j : E) ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ d⁻¹ * (D.num : FractionalIdeal (𝓞 E)⁰ E)` using `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) ((FractionalIdeal.mem_coeIdeal _).2 ⟨j, hj, rfl⟩)`. Rewrite `h4` using `[← key2]`. Rewrite using `[hz]`. Conclude with `h4`.
-/
private theorem exists_ideal (E : Type) [Field E] [NumberField E] :
    ∃ (a : 𝓞 E) (J : Ideal (𝓞 E)), a ≠ 0 ∧ J ≠ ⊥ ∧
      ∀ z : E, InCodiff z ↔ ∃ j ∈ J, z = (a : E)⁻¹ * (j : E) := by
  classical
  have h1ne : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  set D : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.dual ℤ ℚ 1 with hDdef
  have hD : D ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ h1ne
  have hmem : ∀ z : E, InCodiff z ↔ z ∈ D := by
    intro z
    unfold InCodiff
    rw [hDdef, FractionalIdeal.mem_dual h1ne]
    constructor
    · rintro h b hb
      obtain ⟨x, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
      obtain ⟨m, hm⟩ := h x
      exact ⟨m, by simpa [Algebra.traceForm_apply] using hm.symm⟩
    · intro h x
      obtain ⟨m, hm⟩ := h (x : E) ((FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩)
      exact ⟨m, by simpa [Algebra.traceForm_apply] using hm.symm⟩
  set d : E := algebraMap (𝓞 E) E (D.den : 𝓞 E) with hddef
  have hd0 : d ≠ 0 := by
    rw [hddef]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.coe_ne_zero _)
  have key := FractionalIdeal.den_mul_self_eq_num' (𝓞 E)⁰ E D
  have key2 : D = FractionalIdeal.spanSingleton (𝓞 E)⁰ d⁻¹ * (D.num : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [← key, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hd0,
      FractionalIdeal.spanSingleton_one, one_mul]
  refine ⟨(D.den : 𝓞 E), D.num, nonZeroDivisors.coe_ne_zero _, ?_, ?_⟩
  · intro h
    apply hD
    rw [← FractionalIdeal.num_eq_zero_iff]
    exact h
  · intro z
    rw [hmem]
    constructor
    · intro hz
      have h1 : d * z ∈ (D.num : FractionalIdeal (𝓞 E)⁰ E) := by
        rw [← key]
        exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hz
      obtain ⟨j, hj, hjeq⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
      refine ⟨j, hj, ?_⟩
      have h2 : (j : E) = d * z := hjeq
      have h3 : ((D.den : 𝓞 E) : E) = d := rfl
      rw [h3, h2, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
    · rintro ⟨j, hj, hz⟩
      have h4 : d⁻¹ * (j : E) ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ d⁻¹ * (D.num : FractionalIdeal (𝓞 E)⁰ E) :=
        FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
          ((FractionalIdeal.mem_coeIdeal _).2 ⟨j, hj, rfl⟩)
      rw [← key2] at h4
      rw [hz]
      exact h4

/- English proof (translation)
Unfold `CodiffGen`. Introduce `E _ _ M hM`. Take `⟨a, J, ha, hJ, hcod⟩` from `exists_ideal E`. Establish `hM0 : ((M : 𝓞 E)) ≠ 0` using `Nat.cast_ne_zero.2 hM.ne'`. Establish `hI0 : J * Ideal.span {(M : 𝓞 E)} ≠ 0`.

Use `mul_ne_zero (show J ≠ 0 from hJ) ?_` and prove the remaining obligations. Introduce `h`. Conclude with `hM0 (Ideal.span_singleton_eq_bot.1 h)`. Establish `hle : J * Ideal.span {(M : 𝓞 E)} ≤ J` using `Ideal.mul_le.2 fun r hr s _ => J.mul_mem_right s hr`. Take `⟨j, hj⟩` from `IsDedekindDomain.exists_sup_span_eq hle hI0`.

Establish `hjJ : j ∈ J`. Rewrite using `[← hj]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self j)`. Take `⟨K, hK⟩ : J ∣ Ideal.span {j}` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hjJ)`. Establish `hKM : K ⊔ Ideal.span {(M : 𝓞 E)} = ⊤`.

Establish `h1 : J * (Ideal.span {(M : 𝓞 E)} ⊔ K) = J * ⊤`. Rewrite using `[Ideal.mul_sup, ← hK, hj, Ideal.mul_top]`. Rewrite using `[sup_comm]`. Conclude with `mul_left_cancel₀ (show J ≠ 0 from hJ) h1`. Use `set e := Ideal.absNorm K with hedef`.

Establish `heK : (e : 𝓞 E) ∈ K` using `Ideal.absNorm_mem K`. Use `⟨(a : E)⁻¹ * (j : E), (hcod _).2 ⟨j, hjJ, rfl⟩, e, ?_, ?_⟩` and prove the remaining obligations. Use `Nat.coprime_of_dvd fun q hq hqe hqM => ?_` and prove the remaining obligations. Establish `hMq : (M : 𝓞 E) ∈ Ideal.span {(q : 𝓞 E)}` using `Ideal.mem_span_singleton.2 (Nat.cast_dvd_cast hqM)`. Establish `hKq : K ⊔ Ideal.span {(q : 𝓞 E)} = ⊤`.

Rewrite using `[eq_top_iff, ← hKM]`. Conclude with `sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 hMq) K`. Establish `h1 : (1 : 𝓞 E) ∈ K ⊔ Ideal.span {(q : 𝓞 E)}` using `by rw [hKq]; trivial`. Take `⟨k, hk, m, hm, hkm⟩` from `Submodule.mem_sup.1 h1`. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.1 hm`.

Distinguish the cases in `hK0 : K = ⊥`. Substitute `hK0` using the available equality. Establish `hk0 : k = 0` using `(Submodule.mem_bot _).1 hk`. Rewrite `hkm` using `[hk0, zero_add]`. Establish `hunit : IsUnit (q : 𝓞 E)` using `isUnit_iff_exists_inv.2 ⟨t, by rw [mul_comm]; exact hkm⟩`.

Establish `htop : Ideal.span {(q : 𝓞 E)} = ⊤` using `Ideal.span_singleton_eq_top.2 hunit`. Establish `hn` using `Ideal.absNorm_span_natCast (S := 𝓞 E) q`. Rewrite `hn` using `[htop, Ideal.absNorm_top]`. Establish `hpos : 0 < Module.finrank ℤ (𝓞 E)` using `Module.finrank_pos`. Break down `(Nat.pow_eq_one.1 hn.symm) with h | h` into its components or cases.

Conclude with `hq.ne_one h`. Use linear arithmetic over natural numbers and integers. Use `haveI : Finite (𝓞 E ⧸ K) := Ideal.finiteQuotientOfFreeOfNeBot K hK0 haveI : Fact q.Prime := ⟨hq⟩`. Establish `hcard : q ∣ Nat.card (𝓞 E ⧸ K)`. Rewrite using `[← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]`.

Conclude with `hqe`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' q hcard`. Establish `hqx : (q : 𝓞 E ⧸ K) * x = 0`. Rewrite using `[← nsmul_eq_mul, ← hx]`. Conclude with `addOrderOf_nsmul_eq_zero x`.

Establish `hu : (q : 𝓞 E ⧸ K) * Ideal.Quotient.mk K t = 1`. Use `congrArg (Ideal.Quotient.mk K) hkm` as an intermediate fact. Rewrite `this` using `[map_add, Ideal.Quotient.eq_zero_iff_mem.2 hk, zero_add, map_mul, map_one, map_natCast]`. Rewrite using `[mul_comm]`. Conclude with `this`.

Establish `hx0 : x = 0`. Take the linear combination `(-x) * hu + (Ideal.Quotient.mk K t) * hqx`. Rewrite `hx` using `[hx0, addOrderOf_zero]`. Conclude with `hq.one_lt.ne hx`. Introduce `z hz`.

Take `⟨j', hj', rfl⟩` from `(hcod z).1 hz`. Establish `hmem : j' * (e : 𝓞 E) ∈ Ideal.span {j}`. Rewrite using `[hK]`. Conclude with `Ideal.mul_mem_mul hj' heK`. Take `⟨x, hx⟩` from `Ideal.mem_span_singleton'.1 hmem`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `hcast : ((x : E) * (j : E)) = (j' : E) * (e : E)`. Use `congrArg (fun w : 𝓞 E => (w : E)) hx` as an intermediate fact. Simplify using `using this`. Take the linear combination `(-(a : E)⁻¹) * hcast`.
-/
theorem pCodiffGen : CodiffGen := by
  unfold CodiffGen
  intro E _ _ M hM
  classical
  obtain ⟨a, J, ha, hJ, hcod⟩ := exists_ideal E
  have hM0 : ((M : 𝓞 E)) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hI0 : J * Ideal.span {(M : 𝓞 E)} ≠ 0 := by
    refine mul_ne_zero (show J ≠ 0 from hJ) ?_
    intro h
    exact hM0 (Ideal.span_singleton_eq_bot.1 h)
  have hle : J * Ideal.span {(M : 𝓞 E)} ≤ J := Ideal.mul_le.2 fun r hr s _ => J.mul_mem_right s hr
  obtain ⟨j, hj⟩ := IsDedekindDomain.exists_sup_span_eq hle hI0
  have hjJ : j ∈ J := by
    rw [← hj]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self j)
  obtain ⟨K, hK⟩ : J ∣ Ideal.span {j} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hjJ)
  have hKM : K ⊔ Ideal.span {(M : 𝓞 E)} = ⊤ := by
    have h1 : J * (Ideal.span {(M : 𝓞 E)} ⊔ K) = J * ⊤ := by
      rw [Ideal.mul_sup, ← hK, hj, Ideal.mul_top]
    rw [sup_comm]
    exact mul_left_cancel₀ (show J ≠ 0 from hJ) h1
  set e := Ideal.absNorm K with hedef
  have heK : (e : 𝓞 E) ∈ K := Ideal.absNorm_mem K
  refine ⟨(a : E)⁻¹ * (j : E), (hcod _).2 ⟨j, hjJ, rfl⟩, e, ?_, ?_⟩
  · refine Nat.coprime_of_dvd fun q hq hqe hqM => ?_
    have hMq : (M : 𝓞 E) ∈ Ideal.span {(q : 𝓞 E)} :=
      Ideal.mem_span_singleton.2 (Nat.cast_dvd_cast hqM)
    have hKq : K ⊔ Ideal.span {(q : 𝓞 E)} = ⊤ := by
      rw [eq_top_iff, ← hKM]
      exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 hMq) K
    have h1 : (1 : 𝓞 E) ∈ K ⊔ Ideal.span {(q : 𝓞 E)} := by rw [hKq]; trivial
    obtain ⟨k, hk, m, hm, hkm⟩ := Submodule.mem_sup.1 h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hm
    by_cases hK0 : K = ⊥
    · subst hK0
      have hk0 : k = 0 := (Submodule.mem_bot _).1 hk
      rw [hk0, zero_add] at hkm
      have hunit : IsUnit (q : 𝓞 E) := isUnit_iff_exists_inv.2 ⟨t, by rw [mul_comm]; exact hkm⟩
      have htop : Ideal.span {(q : 𝓞 E)} = ⊤ := Ideal.span_singleton_eq_top.2 hunit
      have hn := Ideal.absNorm_span_natCast (S := 𝓞 E) q
      rw [htop, Ideal.absNorm_top] at hn
      have hpos : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
      rcases (Nat.pow_eq_one.1 hn.symm) with h | h
      · exact hq.ne_one h
      · omega
    · haveI : Finite (𝓞 E ⧸ K) := Ideal.finiteQuotientOfFreeOfNeBot K hK0
      haveI : Fact q.Prime := ⟨hq⟩
      have hcard : q ∣ Nat.card (𝓞 E ⧸ K) := by
        rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
        exact hqe
      obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' q hcard
      have hqx : (q : 𝓞 E ⧸ K) * x = 0 := by
        rw [← nsmul_eq_mul, ← hx]
        exact addOrderOf_nsmul_eq_zero x
      have hu : (q : 𝓞 E ⧸ K) * Ideal.Quotient.mk K t = 1 := by
        have := congrArg (Ideal.Quotient.mk K) hkm
        rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hk, zero_add, map_mul, map_one, map_natCast] at this
        rw [mul_comm]
        exact this
      have hx0 : x = 0 := by
        linear_combination (-x) * hu + (Ideal.Quotient.mk K t) * hqx
      rw [hx0, addOrderOf_zero] at hx
      exact hq.one_lt.ne hx
  · intro z hz
    obtain ⟨j', hj', rfl⟩ := (hcod z).1 hz
    have hmem : j' * (e : 𝓞 E) ∈ Ideal.span {j} := by
      rw [hK]
      exact Ideal.mul_mem_mul hj' heK
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨x, ?_⟩
    have hcast : ((x : E) * (j : E)) = (j' : E) * (e : E) := by
      have := congrArg (fun w : 𝓞 E => (w : E)) hx
      simpa using this
    linear_combination (-(a : E)⁻¹) * hcast

end UpperTheory.Gal.W2.Seed
