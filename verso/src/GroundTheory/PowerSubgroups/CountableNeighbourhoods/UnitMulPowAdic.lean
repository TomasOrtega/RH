import Mathlib

namespace GroundTheory.Variant₂.N1

open IsLocalRing

/- English proof (translation)
Establish `hM : maximalIdeal (AdicCompletion (maximalIdeal R) R) = Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) ϖ}`. Establish `e` using `congrArg (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) hϖ.maximalIdeal_eq`. Rewrite using `[AdicCompletion.maximalIdeal_eq_map, e, Ideal.map_span, Set.image_singleton]`. Establish `hMpow : ∀ k : ℕ, maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ k = Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) ϖ ^ k}` using `fun k => by`. Rewrite using `[hM, Ideal.span_singleton_pow]`.

Establish `hex : ∃ k : ℕ, x ∉ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ k`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hx` to reduce the goal to its premises. Apply `IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := maximalIdeal (AdicCompletion (maximalIdeal R) R)) (M := AdicCompletion (maximalIdeal R) R)) x` to reduce the goal to its premises.

Introduce `k`. Simplify `h k` using `only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.zero]`. Establish `hk : x ∉ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ Nat.find hex` using `Nat.find_spec hex`. Establish `hk0 : Nat.find hex ≠ 0`. Introduce `h0`.

Apply `hk` to reduce the goal to its premises. Rewrite using `[h0, pow_zero, Ideal.one_eq_top]`. Conclude with `Submodule.mem_top`. Take `⟨n, hn⟩` from `Nat.exists_eq_succ_of_ne_zero hk0`. Establish `hxn : x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n`.

Use `Nat.find_min hex (show n < Nat.find hex by omega)` as an intermediate fact. Simplify using `using this`. Rewrite `hxn` using `[hMpow, Ideal.mem_span_singleton']`. Take `⟨y, hy⟩` from `hxn`. Establish `hyu : IsUnit y`.

Rewrite using `[← notMem_maximalIdeal]`. Introduce `hyM`. Apply `hk` to reduce the goal to its premises. Rewrite using `[hn, hMpow, Ideal.mem_span_singleton']`. Rewrite `hyM` using `[hM, Ideal.mem_span_singleton']`.

Take `⟨z, hz⟩` from `hyM`. Conclude with `⟨z, by rw [← hy, ← hz, pow_succ]; ring⟩`. Conclude with `⟨n, hyu.unit, by rw [IsUnit.unit_spec, hy]⟩`.
-/
theorem exists_eq_unit_mul_pow_adicCompletion {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    {x : AdicCompletion (maximalIdeal R) R} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : (AdicCompletion (maximalIdeal R) R)ˣ),
      x = ↑u * (algebraMap R (AdicCompletion (maximalIdeal R) R)) ϖ ^ n := by

  have hM : maximalIdeal (AdicCompletion (maximalIdeal R) R) =
      Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) ϖ} := by
    have e := congrArg (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))
      hϖ.maximalIdeal_eq
    rw [AdicCompletion.maximalIdeal_eq_map, e, Ideal.map_span, Set.image_singleton]
  have hMpow : ∀ k : ℕ, maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ k =
      Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) ϖ ^ k} := fun k => by
    rw [hM, Ideal.span_singleton_pow]

  have hex : ∃ k : ℕ, x ∉ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ k := by
    by_contra h
    push Not at h
    apply hx
    apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff
      (I := maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (M := AdicCompletion (maximalIdeal R) R)) x
    intro k
    simpa only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.zero] using h k
  classical
  have hk : x ∉ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ Nat.find hex :=
    Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hk
    rw [h0, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hxn : x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n := by
    have := Nat.find_min hex (show n < Nat.find hex by omega)
    simpa using this
  rw [hMpow, Ideal.mem_span_singleton'] at hxn
  obtain ⟨y, hy⟩ := hxn
  have hyu : IsUnit y := by
    rw [← notMem_maximalIdeal]
    intro hyM
    apply hk
    rw [hn, hMpow, Ideal.mem_span_singleton']
    rw [hM, Ideal.mem_span_singleton'] at hyM
    obtain ⟨z, hz⟩ := hyM
    exact ⟨z, by rw [← hy, ← hz, pow_succ]; ring⟩
  exact ⟨n, hyu.unit, by rw [IsUnit.unit_spec, hy]⟩

end GroundTheory.Variant₂.N1
