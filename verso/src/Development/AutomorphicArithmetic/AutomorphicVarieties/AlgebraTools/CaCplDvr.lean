import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplReg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplMap

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `R _ _ _ π hπ B _ _ _ h`. Use `haveI : IsNoetherianRing B := h.noeth`. Use `set f := algebraMap R B with hf`. Establish `hm : maximalIdeal B = Ideal.span {f π}`. Establish `h1` using `UpperTheory.V.AlgebraTools.IsCplAt.map_pow_eq R _ B h 1`.

Simplify `h1.symm` using `[Ideal.map_span]`. Establish `hpow : ∀ n : ℕ, maximalIdeal B ^ n = Ideal.span {f π ^ n}`. Introduce `n`. Rewrite using `[hm, Ideal.span_singleton_pow]`. Establish `hnil : ∀ n : ℕ, f π ^ n ≠ 0`.

Introduce `n hn`. Establish `hmem : f (π ^ n) ∈ maximalIdeal B ^ (n + 1)`. Rewrite using `[map_pow, hn]`. Conclude with `zero_mem _`. Take `⟨s, hs, hs'⟩` from `h.strict (n + 1) (π ^ n) hmem`.

Rewrite `hs'` using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨t, ht⟩` from `hs'`. Apply `hs` to reduce the goal to its premises. Rewrite using `[Ideal.mem_span_singleton]`. Use `⟨t, ?_⟩` and prove the remaining obligations.

Establish `hπn : π ^ n ≠ 0` using `pow_ne_zero _ hπ.ne_zero`. Apply `mul_right_cancel₀ hπn` to reduce the goal to its premises. Rewrite using `[ht]`. Expand and normalize the polynomial expressions, which then agree. Establish `hK` using `Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal B) (Ideal.IsMaximal.ne_top inferInstance)`.

Establish `hfac : ∀ x : B, x ≠ 0 → ∃ (k : ℕ) (u : B), IsUnit u ∧ x = f π ^ k * u`. Introduce `x hx`. Establish `hex : ∃ n : ℕ, x ∉ maximalIdeal B ^ n`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Apply `hx` to reduce the goal to its premises. Establish `hin : x ∈ ⨅ i : ℕ, maximalIdeal B ^ i` using `Submodule.mem_iInf _ |>.mpr hc`. Rewrite `hin` using `[hK]`. Conclude with `(Submodule.mem_bot _).mp hin`. Establish `hn : x ∉ maximalIdeal B ^ Nat.find hex` using `Nat.find_spec hex`.

Establish `n0 : Nat.find hex ≠ 0`. Introduce `h0`. Apply `hn` to reduce the goal to its premises. Rewrite using `[h0, pow_zero, Ideal.one_eq_top]`. Conclude with `Submodule.mem_top`.

Take `⟨k, hk⟩ : ∃ k : ℕ, Nat.find hex = k + 1` from `⟨Nat.find hex - 1, by omega⟩`. Establish `hxk : x ∈ maximalIdeal B ^ k`. Assume the negation of the conclusion as `hc`. Use `Nat.find_min' hex hc` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite `hxk` using `[hpow, Ideal.mem_span_singleton']`. Take `⟨u, rfl⟩` from `hxk`. Use `⟨k, u, ?_, by ring⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hu`. Apply `hn` to reduce the goal to its premises.

Establish `hum : u ∈ maximalIdeal B` using `(IsLocalRing.mem_maximalIdeal u).mpr hu`. Rewrite `hum` using `[hm, Ideal.mem_span_singleton']`. Take `⟨c, rfl⟩` from `hum`. Rewrite using `[hk, hpow, Ideal.mem_span_singleton']`. Conclude with `⟨c, by ring⟩`.

Use `haveI : IsDomain B := by`. Establish `hnzd : NoZeroDivisors B` using `⟨fun {a b} hab => by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨i, u, hu, rfl⟩` from `hfac a hc.1`.

Take `⟨j, v, hv, rfl⟩` from `hfac b hc.2`. Apply `hnil (i + j)` to reduce the goal to its premises. Establish `hz : f π ^ (i + j) * (u * v) = 0`. Rewrite using `[← hab]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `(hu.mul hv).mul_left_eq_zero.mp hz⟩`. Conclude with `NoZeroDivisors.to_isDomain B`. Establish `hirr : Irreducible (f π)` using `IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (f π) (by simpa using hnil 1) hm`. Use `⟨inferInstance, ?_, hirr⟩` and prove the remaining obligations. Apply `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization` to reduce the goal to its premises.

Use `⟨f π, hirr, fun {x} hx => ?_⟩` and prove the remaining obligations. Take `⟨n, u, hu, rfl⟩` from `hfac x hx`. Conclude with `⟨n, hu.unit, by simp⟩`.
-/
theorem UpperTheory.V.AlgebraTools.IsCplAt.dvr :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (π : R), Prime π →
      ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R (Ideal.span {π}) B →
      ∃ _ : IsDomain B, IsDiscreteValuationRing B ∧ Irreducible (algebraMap R B π) := by
  intro R _ _ _ π hπ B _ _ _ h
  haveI : IsNoetherianRing B := h.noeth
  set f := algebraMap R B with hf
  have hm : maximalIdeal B = Ideal.span {f π} := by
    have h1 := UpperTheory.V.AlgebraTools.IsCplAt.map_pow_eq R _ B h 1
    simpa [Ideal.map_span] using h1.symm
  have hpow : ∀ n : ℕ, maximalIdeal B ^ n = Ideal.span {f π ^ n} := by
    intro n
    rw [hm, Ideal.span_singleton_pow]
  have hnil : ∀ n : ℕ, f π ^ n ≠ 0 := by
    intro n hn
    have hmem : f (π ^ n) ∈ maximalIdeal B ^ (n + 1) := by
      rw [map_pow, hn]
      exact zero_mem _
    obtain ⟨s, hs, hs'⟩ := h.strict (n + 1) (π ^ n) hmem
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hs'
    obtain ⟨t, ht⟩ := hs'
    apply hs
    rw [Ideal.mem_span_singleton]
    refine ⟨t, ?_⟩
    have hπn : π ^ n ≠ 0 := pow_ne_zero _ hπ.ne_zero
    apply mul_right_cancel₀ hπn
    rw [ht]
    ring
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal B) (Ideal.IsMaximal.ne_top inferInstance)
  have hfac : ∀ x : B, x ≠ 0 → ∃ (k : ℕ) (u : B), IsUnit u ∧ x = f π ^ k * u := by
    intro x hx
    classical
    have hex : ∃ n : ℕ, x ∉ maximalIdeal B ^ n := by
      by_contra hc
      push_neg at hc
      apply hx
      have hin : x ∈ ⨅ i : ℕ, maximalIdeal B ^ i := Submodule.mem_iInf _ |>.mpr hc
      rw [hK] at hin
      exact (Submodule.mem_bot _).mp hin
    have hn : x ∉ maximalIdeal B ^ Nat.find hex := Nat.find_spec hex
    have n0 : Nat.find hex ≠ 0 := by
      intro h0
      apply hn
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hxk : x ∈ maximalIdeal B ^ k := by
      by_contra hc
      have := Nat.find_min' hex hc
      omega
    rw [hpow, Ideal.mem_span_singleton'] at hxk
    obtain ⟨u, rfl⟩ := hxk
    refine ⟨k, u, ?_, by ring⟩
    by_contra hu
    apply hn
    have hum : u ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal u).mpr hu
    rw [hm, Ideal.mem_span_singleton'] at hum
    obtain ⟨c, rfl⟩ := hum
    rw [hk, hpow, Ideal.mem_span_singleton']
    exact ⟨c, by ring⟩
  haveI : IsDomain B := by
    have hnzd : NoZeroDivisors B := ⟨fun {a b} hab => by
      by_contra hc
      push_neg at hc
      obtain ⟨i, u, hu, rfl⟩ := hfac a hc.1
      obtain ⟨j, v, hv, rfl⟩ := hfac b hc.2
      apply hnil (i + j)
      have hz : f π ^ (i + j) * (u * v) = 0 := by
        rw [← hab]
        ring
      exact (hu.mul hv).mul_left_eq_zero.mp hz⟩
    exact NoZeroDivisors.to_isDomain B
  have hirr : Irreducible (f π) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (f π) (by simpa using hnil 1) hm
  refine ⟨inferInstance, ?_, hirr⟩
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨f π, hirr, fun {x} hx => ?_⟩
  obtain ⟨n, u, hu, rfl⟩ := hfac x hx
  exact ⟨n, hu.unit, by simp⟩
