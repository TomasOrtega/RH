import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ValCount
open IsLocalRing NumberField IsDedekindDomain GlobalTheory.ValCount
open scoped Classical

/- English proof (translation)
Establish `h : IsIntegral V (a : F)` using `(RingOfIntegers.isIntegral_coe a).tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
private theorem UpperTheory.integer_mem_valuationSubring {F : Type} [Field F] [NumberField F] (V : ValuationSubring F) (a : 𝓞 F) :
    (a : F) ∈ V := by
  have h : IsIntegral V (a : F) := (RingOfIntegers.isIntegral_coe a).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

/- English proof (translation)
Set `f : 𝓞 F →+* V` to `(algebraMap (𝓞 F) F).codRestrict V (UpperTheory.integer_mem_valuationSubring V)`. Set `P : Ideal (𝓞 F)` to `(maximalIdeal V).comap f`. Establish `hP : ∀ a : 𝓞 F, a ∈ P ↔ (a : F) ∈ V.nonunits` using `fun a => (V.coe_mem_nonunits_iff (a := f a)).symm`. Establish `hinv : ∀ a : 𝓞 F, a ∉ P → (a : F)⁻¹ ∈ V` using `fun a ha => by`. Rewrite `ha` using `[hP, ValuationSubring.mem_nonunits_iff_or, not_or, not_not]`.

Conclude with `ha.2`. Establish `hprime : P.IsPrime` using `Ideal.comap_isPrime f _`. Establish `hne : P ≠ ⊥`. Introduce `h`. Apply `hV` to reduce the goal to its premises.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) x`. Rewrite using `[div_eq_mul_inv]`. Use `V.mul_mem _ _ (UpperTheory.integer_mem_valuationSubring V a) (hinv b ?_)` and prove the remaining obligations.

Rewrite using `[h, Ideal.mem_bot]`. Conclude with `nonZeroDivisors.ne_zero hb`. Use `⟨⟨P, hprime, hne⟩, ?_, hP⟩` and prove the remaining obligations. Use `symm`. Use `ValuationSubring.eq_of_le_of_ne_top _ ?_ hV` and prove the remaining obligations.

Introduce and unpack `x ⟨a, s, hs, rfl⟩`. Use `V.mul_mem _ _ (UpperTheory.integer_mem_valuationSubring V a) (hinv s hs)` as an intermediate fact. Simplify using `using this`.
-/
private theorem UpperTheory.valuationSubring_eq_prime {F : Type} [Field F] [NumberField F] (V : ValuationSubring F) (hV : V ≠ ⊤) :
    ∃ v : HeightOneSpectrum (𝓞 F), V = v.valuationSubringAtPrime F ∧
      ∀ a : 𝓞 F, a ∈ v.asIdeal ↔ (a : F) ∈ V.nonunits := by
  let f : 𝓞 F →+* V := (algebraMap (𝓞 F) F).codRestrict V (UpperTheory.integer_mem_valuationSubring V)
  let P : Ideal (𝓞 F) := (maximalIdeal V).comap f
  have hP : ∀ a : 𝓞 F, a ∈ P ↔ (a : F) ∈ V.nonunits := fun a =>
    (V.coe_mem_nonunits_iff (a := f a)).symm
  have hinv : ∀ a : 𝓞 F, a ∉ P → (a : F)⁻¹ ∈ V := fun a ha => by
    rw [hP, ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at ha
    exact ha.2
  have hprime : P.IsPrime := Ideal.comap_isPrime f _
  have hne : P ≠ ⊥ := by
    intro h
    apply hV
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
    rw [div_eq_mul_inv]
    refine V.mul_mem _ _ (UpperTheory.integer_mem_valuationSubring V a) (hinv b ?_)
    rw [h, Ideal.mem_bot]
    exact nonZeroDivisors.ne_zero hb
  refine ⟨⟨P, hprime, hne⟩, ?_, hP⟩
  symm
  refine ValuationSubring.eq_of_le_of_ne_top _ ?_ hV
  rintro x ⟨a, s, hs, rfl⟩
  have := V.mul_mem _ _ (UpperTheory.integer_mem_valuationSubring V a) (hinv s hs)
  simpa using this

/- English proof (translation)
Introduce `F _ _ O hO s hs hT`. Take `⟨w, hw1, hw2⟩` from `UpperTheory.valuationSubring_eq_prime O hO`. Use `choose v hv1 hv2 using fun V : s => UpperTheory.valuationSubring_eq_prime V.1 (hT V.1 V.2)`. Use `haveI : Finite s := hs.to_subtype`. Use `haveI : Fintype s := Fintype.ofFinite s`.

Establish `h1 : ∀ V : s, ∃ y : 𝓞 F, V.1 ≠ O → y ∈ (v V).asIdeal ∧ 1 - y ∈ w.asIdeal`. Introduce `V`. Distinguish the cases in `hVO : V.1 = O`. Conclude with `⟨0, fun h => absurd hVO h⟩`. Establish `hne : (v V).asIdeal ≠ w.asIdeal`.

Introduce `h`. Apply `hVO` to reduce the goal to its premises. Rewrite using `[hv1 V, hw1, HeightOneSpectrum.ext h]`. Establish `hsup` using `Ideal.IsMaximal.coprime_of_ne (v V).isMaximal w.isMaximal hne`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hsup)`.

Conclude with `⟨a, fun _ => ⟨ha, by rw [← hab]; simpa using hb⟩⟩`. Use `choose y hy using h1`. Distinguish the cases in `hex : ∃ V : s, V.1 ≠ O`. Set `t : Finset s` to `Finset.univ.filter fun V => V.1 ≠ O`. Establish `hx : 1 - ∏ V ∈ t, y V ∈ w.asIdeal`.

Rewrite using `[← Ideal.Quotient.eq, map_prod, map_one]`. Use `symm`. Use `Finset.prod_eq_one fun V hV => ?_` and prove the remaining obligations. Use `(hy V (Finset.mem_filter.1 hV).2).2` as an intermediate fact. Rewrite `this` using `[← Ideal.Quotient.eq, map_one]`.

Conclude with `this.symm`. Establish `hn : ∀ V : s, V.1 ≠ O → 1 - ∏ V ∈ t, y V ∉ (v V).asIdeal`. Introduce `V hV h`. Establish `h2 : ∏ V ∈ t, y V ∈ (v V).asIdeal` using `Ideal.prod_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ V, hV⟩) (hy V hV).1`. Establish `h3` using `Ideal.add_mem _ h h2`.

Rewrite `h3` using `[sub_add_cancel]`. Conclude with `(v V).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)`. Use `⟨((1 - ∏ V ∈ t, y V : 𝓞 F) : F), ?_, (hw2 _).1 hx, fun V hV hVO => ⟨UpperTheory.integer_mem_valuationSubring V _, ?_⟩⟩` and prove the remaining obligations. Take `⟨V, hV⟩` from `hex`. Introduce `h`.

Apply `hn V hV` to reduce the goal to its premises. Rewrite using `[RingOfIntegers.coe_eq_zero_iff.1 h]`. Conclude with `zero_mem _`. Use `hn ⟨V, hV⟩ hVO` as an intermediate fact. Rewrite `this` using `[hv2, ValuationSubring.mem_nonunits_iff_or, not_or, not_not]`.

Conclude with `this.2`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot`. Conclude with `⟨a, fun h => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h), (hw2 a).1 ha, fun V hV hVO => absurd ⟨⟨V, hV⟩, hVO⟩ hex⟩`.
-/
theorem UpperTheory.exists_approximation_valuations :
    ∀ (F : Type) [Field F] [NumberField F] (O : ValuationSubring F), O ≠ ⊤ → ∀ s : Set (ValuationSubring F), s.Finite → (∀ V ∈ s, V ≠ ⊤) → ∃ x : F, x ≠ 0 ∧ x ∈ O.nonunits ∧ ∀ V ∈ s, V ≠ O → x ∈ V ∧ x⁻¹ ∈ V := by
  intro F _ _ O hO s hs hT
  obtain ⟨w, hw1, hw2⟩ := UpperTheory.valuationSubring_eq_prime O hO
  choose v hv1 hv2 using fun V : s => UpperTheory.valuationSubring_eq_prime V.1 (hT V.1 V.2)
  haveI : Finite s := hs.to_subtype
  haveI : Fintype s := Fintype.ofFinite s
  have h1 : ∀ V : s, ∃ y : 𝓞 F, V.1 ≠ O → y ∈ (v V).asIdeal ∧ 1 - y ∈ w.asIdeal := by
    intro V
    by_cases hVO : V.1 = O
    · exact ⟨0, fun h => absurd hVO h⟩
    have hne : (v V).asIdeal ≠ w.asIdeal := by
      intro h
      apply hVO
      rw [hv1 V, hw1, HeightOneSpectrum.ext h]
    have hsup := Ideal.IsMaximal.coprime_of_ne (v V).isMaximal w.isMaximal hne
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hsup)
    exact ⟨a, fun _ => ⟨ha, by rw [← hab]; simpa using hb⟩⟩
  choose y hy using h1
  by_cases hex : ∃ V : s, V.1 ≠ O
  · let t : Finset s := Finset.univ.filter fun V => V.1 ≠ O
    have hx : 1 - ∏ V ∈ t, y V ∈ w.asIdeal := by
      rw [← Ideal.Quotient.eq, map_prod, map_one]
      symm
      refine Finset.prod_eq_one fun V hV => ?_
      have := (hy V (Finset.mem_filter.1 hV).2).2
      rw [← Ideal.Quotient.eq, map_one] at this
      exact this.symm
    have hn : ∀ V : s, V.1 ≠ O → 1 - ∏ V ∈ t, y V ∉ (v V).asIdeal := by
      intro V hV h
      have h2 : ∏ V ∈ t, y V ∈ (v V).asIdeal :=
        Ideal.prod_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ V, hV⟩) (hy V hV).1
      have h3 := Ideal.add_mem _ h h2
      rw [sub_add_cancel] at h3
      exact (v V).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)
    refine ⟨((1 - ∏ V ∈ t, y V : 𝓞 F) : F), ?_, (hw2 _).1 hx, fun V hV hVO => ⟨UpperTheory.integer_mem_valuationSubring V _, ?_⟩⟩
    · obtain ⟨V, hV⟩ := hex
      intro h
      apply hn V hV
      rw [RingOfIntegers.coe_eq_zero_iff.1 h]
      exact zero_mem _
    · have := hn ⟨V, hV⟩ hVO
      rw [hv2, ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at this
      exact this.2
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    exact ⟨a, fun h => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h), (hw2 a).1 ha,
      fun V hV hVO => absurd ⟨⟨V, hV⟩, hVO⟩ hex⟩
