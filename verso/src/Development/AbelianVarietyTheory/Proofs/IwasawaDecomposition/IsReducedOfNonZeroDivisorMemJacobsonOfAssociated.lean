import Mathlib

open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hnx`. Establish `h0 : (Ideal.Quotient.mk (Ideal.span {x}) n) ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis. Take `⟨P, hPa, hle⟩` from `exists_le_isAssociatedPrime_of_isNoetherianRing R (Ideal.Quotient.mk (Ideal.span {x}) n) h0`. Use `haveI : P.IsPrime := hPa.isPrime`.

Use `haveI := hP P hPa`. Establish `hz : algebraMap R (Localization.AtPrime P) n = 0` using `(hn.map (algebraMap R (Localization.AtPrime P))).eq_zero`. Take `⟨⟨s, hs⟩, hsn⟩` from `(IsLocalization.map_eq_zero_iff P.primeCompl _ n).1 hz`. Apply `hs` to reduce the goal to its premises. Apply `hle` to reduce the goal to its premises.

Rewrite using `[Submodule.mem_colon_singleton, Submodule.mem_bot]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.span {x}) s * Ideal.Quotient.mk (Ideal.span {x}) n = 0`. Rewrite using `[← map_mul, hsn, map_zero]`.
-/
theorem mem_span_singleton_of_isNilpotent_of_associatedPrimes {R : Type} [CommRing R]
    [IsNoetherianRing R] (x : R)
    (hP : ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
      IsDomain (Localization.AtPrime P))
    {n : R} (hn : IsNilpotent n) : n ∈ Ideal.span {x} := by
  by_contra hnx
  have h0 : (Ideal.Quotient.mk (Ideal.span {x}) n) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hPa, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (Ideal.Quotient.mk (Ideal.span {x}) n) h0
  haveI : P.IsPrime := hPa.isPrime
  haveI := hP P hPa
  have hz : algebraMap R (Localization.AtPrime P) n = 0 :=
    (hn.map (algebraMap R (Localization.AtPrime P))).eq_zero
  obtain ⟨⟨s, hs⟩, hsn⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ n).1 hz
  apply hs
  apply hle
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
  change Ideal.Quotient.mk (Ideal.span {x}) s * Ideal.Quotient.mk (Ideal.span {x}) n = 0
  rw [← map_mul, hsn, map_zero]

/- English proof (translation)
Introduce `R _ _ x hx hj hP`. Use `⟨fun n hn => ?_⟩` and prove the remaining obligations. Establish `key : ∀ k : ℕ, ∀ m : R, IsNilpotent m → m ∈ Ideal.span {x} ^ k`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => intro m _`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `m hm`. Take `⟨m', rfl⟩` from `Ideal.mem_span_singleton'.1 (mem_span_singleton_of_isNilpotent_of_associatedPrimes x hP hm)`.

Establish `hm' : IsNilpotent m'`. Take `⟨e, he⟩` from `hm`. Use `⟨e, ?_⟩` and prove the remaining obligations. Rewrite `he` using `[mul_pow]`. Conclude with `(mem_nonZeroDivisors_iff_right.1 (pow_mem hx e)) _ he`.

Rewrite using `[pow_succ', mul_comm m' x]`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) (ih m' hm')`. Establish `hK` using `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := R) (Ideal.span {x}) ((Ideal.span_singleton_le_iff_mem _).2 hj)`. Establish `: n ∈ (⨅ i : ℕ, (Ideal.span {x}) ^ i • ⊤ : Submodule R R)`. Rewrite using `[Submodule.mem_iInf]`.

Introduce `i`. Simplify `key i n hn` using `[smul_eq_mul, Ideal.mul_top]`. Rewrite `this` using `[hK]`. Simplify using `using this`.
-/
theorem isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R →
      x ∈ Ideal.jacobson (⊥ : Ideal R) →
      (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
        IsDomain (Localization.AtPrime P)) → IsReduced R := by
  intro R _ _ x hx hj hP
  refine ⟨fun n hn => ?_⟩
  have key : ∀ k : ℕ, ∀ m : R, IsNilpotent m → m ∈ Ideal.span {x} ^ k := by
    intro k
    induction k with
    | zero => intro m _; simp
    | succ k ih =>
      intro m hm
      obtain ⟨m', rfl⟩ := Ideal.mem_span_singleton'.1
        (mem_span_singleton_of_isNilpotent_of_associatedPrimes x hP hm)
      have hm' : IsNilpotent m' := by
        obtain ⟨e, he⟩ := hm
        refine ⟨e, ?_⟩
        rw [mul_pow] at he
        exact (mem_nonZeroDivisors_iff_right.1 (pow_mem hx e)) _ he
      rw [pow_succ', mul_comm m' x]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) (ih m' hm')
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := R) (Ideal.span {x})
    ((Ideal.span_singleton_le_iff_mem _).2 hj)
  have : n ∈ (⨅ i : ℕ, (Ideal.span {x}) ^ i • ⊤ : Submodule R R) := by
    rw [Submodule.mem_iInf]
    intro i
    simpa [smul_eq_mul, Ideal.mul_top] using key i n hn
  rw [hK] at this
  simpa using this

end GlobalTheory
