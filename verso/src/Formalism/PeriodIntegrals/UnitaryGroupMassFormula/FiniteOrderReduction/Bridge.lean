import Formalism.PeriodIntegrals.FinOrdRedOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderReduction.EqOneOfIsOfFinOrder

noncomputable section

namespace PI.FinOrdRedOne.Bridge

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Ideal WithZero

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hprime : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Establish `hspan : (span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible`. Establish `hle : span {(p : ℤ)} ≤ P.asIdeal.comap (algebraMap ℤ (𝓞 E))`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]`. Conclude with `hpP`.

Establish `hne : P.asIdeal.comap (algebraMap ℤ (𝓞 E)) ≠ ⊤` using `(P.isPrime.comap _).ne_top`. Establish `heq : span {(p : ℤ)} = P.asIdeal.comap (algebraMap ℤ (𝓞 E))` using `hspan.eq_of_le hne hle`. Establish `hlo : P.asIdeal.LiesOver (span {(p : ℤ)})` using `⟨heq⟩`. Establish `he : P.asIdeal.ramificationIdx ℤ = 1` using `@hU P.asIdeal P.isPrime hlo`. Establish `hbot : span {(p : ℤ)} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hp.ne_zero` after adjusting the coercions. Use `P.isPrime` as an intermediate fact. Rewrite `he` using `[← Ideal.ramificationIdx'_eq_ramificationIdx (span {(p : ℤ)}) P.asIdeal hbot]`. Establish `hmap : (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≤ P.asIdeal` using `Ideal.map_le_iff_le_comap.mpr hle`.

Establish `hiff` using `Ideal.ramificationIdx'_ne_one_iff (p := span {(p : ℤ)}) (P := P.asIdeal) hmap`. Introduce `hsq`. Apply `hiff.mpr _ he` to reduce the goal to its premises. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hsq`.
-/
theorem natCast_not_mem_sq (p : ℕ) (hp : p.Prime) (hU : Unram E p) (P : HeightOneSpectrum (𝓞 E))
    (hpP : (p : 𝓞 E) ∈ P.asIdeal) : (p : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hspan : (span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible
  have hle : span {(p : ℤ)} ≤ P.asIdeal.comap (algebraMap ℤ (𝓞 E)) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact hpP
  have hne : P.asIdeal.comap (algebraMap ℤ (𝓞 E)) ≠ ⊤ := (P.isPrime.comap _).ne_top
  have heq : span {(p : ℤ)} = P.asIdeal.comap (algebraMap ℤ (𝓞 E)) := hspan.eq_of_le hne hle
  have hlo : P.asIdeal.LiesOver (span {(p : ℤ)}) := ⟨heq⟩
  have he : P.asIdeal.ramificationIdx ℤ = 1 := @hU P.asIdeal P.isPrime hlo
  have hbot : span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have := P.isPrime
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (span {(p : ℤ)}) P.asIdeal hbot] at he
  have hmap : (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≤ P.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr hle
  have hiff := Ideal.ramificationIdx'_ne_one_iff (p := span {(p : ℤ)}) (P := P.asIdeal) hmap
  intro hsq
  apply hiff.mpr _ he
  rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_le, Set.singleton_subset_iff]
  exact hsq

/- English proof (translation)
Establish `h1` using `(P.intValuation_le_pow_iff_mem (p : 𝓞 E) 1).mpr (by rw [pow_one]; exact hpP)`. Establish `h2 : ¬ P.intValuation (p : 𝓞 E) ≤ exp (-((2 : ℕ) : ℤ))` using `fun h => natCast_not_mem_sq p hp hU P hpP ((P.intValuation_le_pow_iff_mem (p : 𝓞 E) 2).mp h)`. Establish `hx0 : P.intValuation (p : 𝓞 E) ≠ 0`. Introduce `h`. Apply `h2` to reduce the goal to its premises.

Rewrite using `[h]`. Conclude with `zero_le`. Rewrite `h1`, `h2`, the goal using `[← exp_log hx0]`. Rewrite `h1`, `h2` using `[exp_le_exp]`. Rewrite using `[exp_inj]`.

Move the coercions through the operations in `at h1 h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem intValuation_natCast (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) :
    P.intValuation (p : 𝓞 E) = exp (-1 : ℤ) := by
  have h1 := (P.intValuation_le_pow_iff_mem (p : 𝓞 E) 1).mpr (by rw [pow_one]; exact hpP)
  have h2 : ¬ P.intValuation (p : 𝓞 E) ≤ exp (-((2 : ℕ) : ℤ)) := fun h =>
    natCast_not_mem_sq p hp hU P hpP ((P.intValuation_le_pow_iff_mem (p : 𝓞 E) 2).mp h)
  have hx0 : P.intValuation (p : 𝓞 E) ≠ 0 := by
    intro h; apply h2; rw [h]; exact zero_le
  rw [← exp_log hx0] at h1 h2 ⊢
  rw [exp_le_exp] at h1 h2
  rw [exp_inj]
  push_cast at h1 h2
  omega

/- English proof (translation)
Establish `h1` using `P.valuedAdicCompletion_eq_valuation (K := E) ((p : ℕ) : 𝓞 E)`. Rewrite `h1` using `[valuation_of_algebraMap, intValuation_natCast p hp hU P hpP]`. Simplify using `only [map_natCast] at h1`. Conclude with `h1`.
-/
theorem valued_natCast (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) :
    Valued.v ((p : ℕ) : P.adicCompletion E) = exp (-1 : ℤ) := by
  have h1 := P.valuedAdicCompletion_eq_valuation (K := E) ((p : ℕ) : 𝓞 E)
  rw [valuation_of_algebraMap, intValuation_natCast p hp hU P hpP] at h1
  simp only [map_natCast] at h1
  exact h1

/- English proof (translation)
Introduce `h`. Establish `h1` using `valued_natCast p hp hU P hpP`. Establish `h2` using `congrArg (fun z : OP E P => (z : P.adicCompletion E)) h`. Move the coercions through the operations in `at h2`. Rewrite `h1` using `[h2, map_zero]`.

Conclude with `exp_ne_zero h1.symm`.
-/
theorem natCast_ne_zero (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) :
    ((p : ℕ) : OP E P) ≠ 0 := by
  intro h
  have h1 := valued_natCast p hp hU P hpP
  have h2 := congrArg (fun z : OP E P => (z : P.adicCompletion E)) h
  push_cast at h2
  rw [h2, map_zero] at h1
  exact exp_ne_zero h1.symm

/- English proof (translation)
Establish `hint` using `HeightOneSpectrum.adicCompletionIntegers.integers (K := E) (v := P)`. Establish `hvp` using `valued_natCast p hp hU P hpP`. Establish `hp0 : ((p : ℕ) : P.adicCompletion E) ≠ 0`. Introduce `h`. Rewrite `hvp` using `[h, map_zero]`.

Conclude with `exp_ne_zero hvp.symm`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hint.isUnit_iff_valuation_eq_one]`. Establish `hle : Valued.v (x : P.adicCompletion E) ≤ 1` using `x.2`.

Establish `hlt : Valued.v (x : P.adicCompletion E) < 1` using `lt_of_le_of_ne hle hx`. Establish `hle1 : Valued.v (x : P.adicCompletion E) ≤ exp (-1 : ℤ)`. Distinguish the cases in `h0 : Valued.v (x : P.adicCompletion E) = 0`. Rewrite using `[h0]`. Conclude with `zero_le`.

Rewrite `hlt`, the goal using `[← exp_log h0]`. Rewrite `hlt` using `[← exp_zero, exp_lt_exp]`. Rewrite using `[exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `hy : (x : P.adicCompletion E) / (p : P.adicCompletion E) ∈ P.adicCompletionIntegers E`.

Rewrite using `[mem_adicCompletionIntegers, map_div₀, hvp, div_le_one₀ (zero_lt_iff.mpr exp_ne_zero)]`. Conclude with `hle1`. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨⟨_, hy⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Use `push_cast`. Conclude with `div_mul_cancel₀ _ hp0`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hint.isUnit_iff_valuation_eq_one]`. Express the relevant statement in the definitionally equal form `Valued.v (((p : ℕ) : OP E P) : P.adicCompletion E) ≠ 1`. Use `push_cast`.

Rewrite using `[hvp, ← exp_zero, Ne, exp_inj]`. Use linear arithmetic over natural numbers and integers.
-/
theorem maximalIdeal_eq (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) :
    IsLocalRing.maximalIdeal (OP E P) = span {((p : ℕ) : OP E P)} := by
  have hint := HeightOneSpectrum.adicCompletionIntegers.integers (K := E) (v := P)
  have hvp := valued_natCast p hp hU P hpP
  have hp0 : ((p : ℕ) : P.adicCompletion E) ≠ 0 := by
    intro h; rw [h, map_zero] at hvp; exact exp_ne_zero hvp.symm
  apply le_antisymm
  · intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hint.isUnit_iff_valuation_eq_one] at hx
    have hle : Valued.v (x : P.adicCompletion E) ≤ 1 := x.2
    have hlt : Valued.v (x : P.adicCompletion E) < 1 := lt_of_le_of_ne hle hx
    have hle1 : Valued.v (x : P.adicCompletion E) ≤ exp (-1 : ℤ) := by
      by_cases h0 : Valued.v (x : P.adicCompletion E) = 0
      · rw [h0]; exact zero_le
      rw [← exp_log h0] at hlt ⊢
      rw [← exp_zero, exp_lt_exp] at hlt
      rw [exp_le_exp]
      omega
    have hy : (x : P.adicCompletion E) / (p : P.adicCompletion E) ∈
        P.adicCompletionIntegers E := by
      rw [mem_adicCompletionIntegers, map_div₀, hvp, div_le_one₀ (zero_lt_iff.mpr exp_ne_zero)]
      exact hle1
    rw [Ideal.mem_span_singleton']
    refine ⟨⟨_, hy⟩, ?_⟩
    apply Subtype.ext
    push_cast
    exact div_mul_cancel₀ _ hp0
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, hint.isUnit_iff_valuation_eq_one]
    change Valued.v (((p : ℕ) : OP E P) : P.adicCompletion E) ≠ 1
    push_cast
    rw [hvp, ← exp_zero, Ne, exp_inj]
    omega

/- English proof (translation)
Establish `hne : IsLocalRing.maximalIdeal (OP E P) ≠ ⊤` using `(IsLocalRing.maximalIdeal.isMaximal _).ne_top`. Establish `hK` using `Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal (OP E P)) hne`. Rewrite using `[← Ideal.mem_bot, ← hK, Ideal.mem_iInf]`. Introduce `k`. Rewrite using `[maximalIdeal_eq p hp hU P hpP, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.

Conclude with `hx k`.
-/
theorem eq_zero_of_forall_dvd (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) (x : OP E P)
    (hx : ∀ k : ℕ, ((p : ℕ) : OP E P) ^ k ∣ x) : x = 0 := by
  have hne : IsLocalRing.maximalIdeal (OP E P) ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal (OP E P)) hne
  rw [← Ideal.mem_bot, ← hK, Ideal.mem_iInf]
  intro k
  rw [maximalIdeal_eq p hp hU P hpP, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact hx k

end PI.FinOrdRedOne.Bridge
