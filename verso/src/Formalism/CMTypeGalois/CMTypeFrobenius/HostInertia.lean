import Mathlib
import Formalism.CMTypeGalois.StatementField

open NumberField Ideal

noncomputable section

namespace Formalism.Q3

/- English proof (translation)
Rewrite using `[← Ideal.mem_span_singleton, Ideal.over_def P (span {(p : ℤ)}), Ideal.under_def, Ideal.mem_comap, eq_intCast]`.
-/
theorem hostIn_intCast_mem_iff {E : Type} [Field E] [NumberField E] (p : ℕ)
    (P : Ideal (𝓞 E)) [P.LiesOver (span {(p : ℤ)})] (n : ℤ) :
    (n : 𝓞 E) ∈ P ↔ (p : ℤ) ∣ n := by
  rw [← Ideal.mem_span_singleton, Ideal.over_def P (span {(p : ℤ)}), Ideal.under_def,
    Ideal.mem_comap, eq_intCast]

/- English proof (translation)
Establish `: IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E)` using `IsGaloisGroup.of_isFractionRing _ _ _ ℚ E`. Establish `: (span {(p : ℤ)}).IsPrime`. Rewrite using `[Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]`. Conclude with `Nat.prime_iff_prime_int.mp Fact.out`. Rewrite using `[card_inertia_eq_ramificationIdxIn (G := Gal(E/ℚ)) (span {(p : ℤ)}) P, ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) P Gal(E/ℚ)]`.
-/
theorem hostIn_card (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    Nat.card (P.inertia Gal(E/ℚ)) = P.ramificationIdx ℤ := by
  have : IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have : (span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp Fact.out
  rw [card_inertia_eq_ramificationIdxIn (G := Gal(E/ℚ)) (span {(p : ℤ)}) P,
    ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) P Gal(E/ℚ)]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[galSign]`.
-/
theorem hostIn_galSign_one {E : Type} [Field E] [Algebra ℚ E] (α : Fin 3 → E) :
    galSign α (1 : Gal(E/ℚ)) = 1 := by
  funext j
  simp [galSign]

/- English proof (translation)
Establish `hsq : α j ^ 2 = ((-(q j : ℤ) : ℤ) : E)` using `hα.1 j`. Establish `hint : IsIntegral ℤ (α j)`. Use `IsIntegral.of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Rewrite using `[hsq, ← eq_intCast (algebraMap ℤ E)]`. Conclude with `isIntegral_algebraMap`.

Use `⟨⟨α j, hint⟩, rfl, ?_⟩` and prove the remaining obligations. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Simplify using `only [map_intCast]`. Conclude with `hsq.trans (by push_cast; rfl)`.
-/
theorem hostIn_A (q : Fin 3 → ℕ) {E : Type} [Field E] [NumberField E] (α : Fin 3 → E)
    (hα : IsHost q α) (j : Fin 3) :
    ∃ A : 𝓞 E, (A : E) = α j ∧ A ^ 2 = ((-(q j : ℤ) : ℤ) : 𝓞 E) := by
  have hsq : α j ^ 2 = ((-(q j : ℤ) : ℤ) : E) := hα.1 j
  have hint : IsIntegral ℤ (α j) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hsq, ← eq_intCast (algebraMap ℤ E)]
    exact isIntegral_algebraMap
  refine ⟨⟨α j, hint⟩, rfl, ?_⟩
  apply RingOfIntegers.coe_injective
  simp only [map_intCast]
  exact hsq.trans (by push_cast; rfl)

/- English proof (translation)
Establish `hne : ∀ l, (-(q l : ℤ)) ≠ 0` using `fun l => by`. Use `(hq.1 l).1.pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hsq : α j ^ 2 = ((-(q j : ℤ) : ℤ) : E)` using `hα.1 j`. Establish `hσα : σ (α j) = -α j`.

Use `(hG 3 E _ α hα hne).2.1 σ j` as an intermediate fact. Rewrite using `[this, hj]`. Simplify using the standard rewrite rules. Take `⟨c, hc⟩ : ∃ c : ℤ, -(q j : ℤ) = 4 * c + 1` from `⟨(-(q j : ℤ) - 1) / 4, by have := (hq.1 j).2; omega⟩`. Establish `hcE : ((-(q j : ℤ) : ℤ) : E) = 4 * c + 1` using `by exact_mod_cast hc`.

Take `⟨ω, hωdef⟩ : ∃ ω : E, ω = (1 + α j) / 2` from `⟨_, rfl⟩`. Establish `hω2 : ω ^ 2 = ω + (c : E)`. Rewrite using `[hωdef]`. Take the linear combination `(1 / 4 : E) * hsq + (1 / 4 : E) * hcE`. Establish `hωint : IsIntegral ℤ ω`.

Use `⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C c), ?_, ?_⟩` and prove the remaining obligations. Apply `Polynomial.monic_X_pow_sub` to reduce the goal to its premises. Rewrite using `[Polynomial.degree_X_add_C]`. Evaluate the numerical expressions. Rewrite using `[Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, hω2]`.

Simplify using the standard rewrite rules. Take `⟨W, hWcoe⟩ : ∃ W : 𝓞 E, (W : E) = ω` from `⟨⟨ω, hωint⟩, rfl⟩`. Take `⟨A, hAcoe, hA2⟩` from `hostIn_A q α hα j`. Establish `hσW : σ • W - W = -A`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Use `show σ (W : E) - (W : E) = -(A : E)`. Rewrite using `[hWcoe, hAcoe, hωdef, map_div₀, map_add, map_one, hσα]`. Establish `h2 : σ (2 : E) = 2` using `map_ofNat σ 2`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hAP : A ∈ P`. Use `P.neg_mem_iff.mpr (hσW ▸ hσ W)` as an intermediate fact. Simplify using `using this`. Establish `hqP : ((-(q j : ℤ) : ℤ) : 𝓞 E) ∈ P`. Rewrite using `[← hA2]`.

Conclude with `P.pow_mem_of_mem hAP 2 (by norm_num)`. Rewrite `hqP` using `[hostIn_intCast_mem_iff p P]`. Conclude with `dvd_neg.mp hqP`.
-/
theorem hostIn_key (hG : MQGalois) (q : Fin 3 → ℕ) (hq : Hyp3 q)
    (E : Type) [Field E] [NumberField E] (α : Fin 3 → E) (hα : IsHost q α)
    (p : ℕ) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(E/ℚ))
    (hσ : ∀ x : 𝓞 E, σ • x - x ∈ P) (j : Fin 3) (hj : galSign α σ j = -1) :
    (p : ℤ) ∣ (q j : ℤ) := by
  have hne : ∀ l, (-(q l : ℤ)) ≠ 0 := fun l => by
    have := (hq.1 l).1.pos
    omega
  have hsq : α j ^ 2 = ((-(q j : ℤ) : ℤ) : E) := hα.1 j
  have hσα : σ (α j) = -α j := by
    have := (hG 3 E _ α hα hne).2.1 σ j
    rw [this, hj]
    simp
  obtain ⟨c, hc⟩ : ∃ c : ℤ, -(q j : ℤ) = 4 * c + 1 :=
    ⟨(-(q j : ℤ) - 1) / 4, by have := (hq.1 j).2; omega⟩
  have hcE : ((-(q j : ℤ) : ℤ) : E) = 4 * c + 1 := by exact_mod_cast hc
  obtain ⟨ω, hωdef⟩ : ∃ ω : E, ω = (1 + α j) / 2 := ⟨_, rfl⟩
  have hω2 : ω ^ 2 = ω + (c : E) := by
    rw [hωdef]
    linear_combination (1 / 4 : E) * hsq + (1 / 4 : E) * hcE
  have hωint : IsIntegral ℤ ω := by
    refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C c), ?_, ?_⟩
    · apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X_add_C]
      norm_num
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C,
        Polynomial.eval₂_X_pow, hω2]
      simp
  obtain ⟨W, hWcoe⟩ : ∃ W : 𝓞 E, (W : E) = ω := ⟨⟨ω, hωint⟩, rfl⟩
  obtain ⟨A, hAcoe, hA2⟩ := hostIn_A q α hα j
  have hσW : σ • W - W = -A := by
    apply RingOfIntegers.coe_injective
    show σ (W : E) - (W : E) = -(A : E)
    rw [hWcoe, hAcoe, hωdef, map_div₀, map_add, map_one, hσα]
    have h2 : σ (2 : E) = 2 := map_ofNat σ 2
    rw [h2]
    ring
  have hAP : A ∈ P := by
    have := P.neg_mem_iff.mpr (hσW ▸ hσ W)
    simpa using this
  have hqP : ((-(q j : ℤ) : ℤ) : 𝓞 E) ∈ P := by
    rw [← hA2]
    exact P.pow_mem_of_mem hAP 2 (by norm_num)
  rw [hostIn_intCast_mem_iff p P] at hqP
  exact dvd_neg.mp hqP

/- English proof (translation)
Establish `hq0 : (q i : ℤ) ≠ 0` using `by exact_mod_cast (hq.1 i).1.ne_zero`. Rewrite using `[← Ideal.ramificationIdx'_eq_ramificationIdx (span {(q i : ℤ)}) P (by simpa using (hq.1 i).1.ne_zero)]`. Establish `hmemq : ((q i : ℤ) : 𝓞 E) ∈ P` using `(hostIn_intCast_mem_iff (q i) P _).mpr dvd_rfl`. Establish `hmap : map (algebraMap ℤ (𝓞 E)) (span {(q i : ℤ)}) = span {((q i : ℤ) : 𝓞 E)}`. Rewrite using `[Ideal.map_span, Set.image_singleton, eq_intCast]`.

Rewrite using `[Ideal.ramificationIdx'_ne_one_iff (by rw [hmap, Ideal.span_le, Set.singleton_subset_iff]; exact hmemq), hmap, Ideal.span_le, Set.singleton_subset_iff]`. Take `⟨A, -, hA2⟩` from `hostIn_A q α hα i`. Establish `hA2P : A ^ 2 ∈ P`. Rewrite using `[hA2, Int.cast_neg]`. Conclude with `P.neg_mem_iff.mpr hmemq`.

Establish `hAP : A ∈ P` using `(inferInstance : P.IsPrime).mem_of_pow_mem 2 hA2P`. Establish `: ((q i : ℤ) : 𝓞 E) = -(A * A)`. Rewrite using `[← pow_two, hA2, Int.cast_neg, neg_neg]`. Use `show ((q i : ℤ) : 𝓞 E) ∈ P ^ 2`. Rewrite using `[this, pow_two]`.

Conclude with `(P * P).neg_mem_iff.mpr (Ideal.mul_mem_mul hAP hAP)`.
-/
theorem hostIn_ram_ne_one (q : Fin 3 → ℕ) (hq : Hyp3 q)
    (E : Type) [Field E] [NumberField E] (α : Fin 3 → E) (hα : IsHost q α)
    (i : Fin 3) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(q i : ℤ)})] :
    P.ramificationIdx ℤ ≠ 1 := by
  have hq0 : (q i : ℤ) ≠ 0 := by exact_mod_cast (hq.1 i).1.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (span {(q i : ℤ)}) P (by simpa using (hq.1 i).1.ne_zero)]
  have hmemq : ((q i : ℤ) : 𝓞 E) ∈ P := (hostIn_intCast_mem_iff (q i) P _).mpr dvd_rfl
  have hmap : map (algebraMap ℤ (𝓞 E)) (span {(q i : ℤ)}) = span {((q i : ℤ) : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, eq_intCast]
  rw [Ideal.ramificationIdx'_ne_one_iff
      (by rw [hmap, Ideal.span_le, Set.singleton_subset_iff]; exact hmemq),
    hmap, Ideal.span_le, Set.singleton_subset_iff]
  obtain ⟨A, -, hA2⟩ := hostIn_A q α hα i
  have hA2P : A ^ 2 ∈ P := by
    rw [hA2, Int.cast_neg]
    exact P.neg_mem_iff.mpr hmemq
  have hAP : A ∈ P := (inferInstance : P.IsPrime).mem_of_pow_mem 2 hA2P
  have : ((q i : ℤ) : 𝓞 E) = -(A * A) := by
    rw [← pow_two, hA2, Int.cast_neg, neg_neg]
  show ((q i : ℤ) : 𝓞 E) ∈ P ^ 2
  rw [this, pow_two]
  exact (P * P).neg_mem_iff.mpr (Ideal.mul_mem_mul hAP hAP)

/- English proof (translation)
Introduce `q hq E _ _ α hα i P _ _ σ`. Establish `hGal` using `hH q hq E α hα`. Establish `: IsGalois ℚ E` using `hGal.1`. Establish `hinj` using `hGal.2.2.1.1`. Establish `h1 : galSign α (1 : Gal(E/ℚ)) = 1` using `hostIn_galSign_one α`.

Establish `hfwd : ∀ τ : Gal(E/ℚ), (∀ x : 𝓞 E, τ • x - x ∈ P) → (galSign α τ = 1 ∨ galSign α τ = e3 i)`. Introduce `τ hτ`. Establish `hoth : ∀ j, j ≠ i → galSign α τ j = 1`. Introduce `j hji`. Break down `Int.units_eq_one_or (galSign α τ j) with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Establish `hd` using `hostIn_key hG q hq E α hα (q i) P τ hτ j h`. Use `(Nat.prime_dvd_prime_iff_eq (hq.1 i).1 (hq.1 j).1).mp (by exact_mod_cast hd)` as an intermediate fact. Conclude with `hji (hq.2 this).symm`.

Break down `Int.units_eq_one_or (galSign α τ i) with h | h` into its components or cases. Use `left`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hji : j = i`. Substitute `hji` using the available equality.

Simplify using `using h`. Rewrite using `[hoth j hji]`. Both sides reduce to the same expression. Use `right`. Use function extensionality and compare the values at `j`.

Distinguish the cases in `hji : j = i`. Substitute `hji` using the available equality. Simplify using `[e3, h]`. Simplify using `[e3, hji, hoth j hji]`. Use `⟨hfwd σ, fun h => ?_⟩` and prove the remaining obligations.

Break down `h with h | h` into its components or cases. Establish `: σ = 1` using `hinj (h.trans h1.symm)`. Substitute `this` using the available equality. Introduce `x`. Simplify using the standard rewrite rules.

Assume the negation of the conclusion as `hn`. Establish `hbot : P.inertia Gal(E/ℚ) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `τ hτ`. Rewrite using `[Subgroup.mem_bot]`.

Break down `hfwd τ hτ with h' | h'` into its components or cases. Conclude with `hinj (h'.trans h1.symm)`. Use `hinj (h'.trans h.symm)` as an intermediate fact. Substitute `this` using the available equality. Conclude with `absurd hτ hn`.

Establish `: Fact (q i).Prime` using `⟨(hq.1 i).1⟩`. Establish `hc` using `hostIn_card E (q i) P`. Rewrite `hc` using `[hbot, Subgroup.card_bot]`. Conclude with `hostIn_ram_ne_one q hq E α hα i P hc.symm`.
-/
theorem hostInertia_of (hH : HostGalois) (hG : MQGalois) : HostInertia := by
  intro q hq E _ _ α hα i P _ _ σ
  have hGal := hH q hq E α hα
  have : IsGalois ℚ E := hGal.1
  have hinj := hGal.2.2.1.1
  have h1 : galSign α (1 : Gal(E/ℚ)) = 1 := hostIn_galSign_one α
  have hfwd : ∀ τ : Gal(E/ℚ), (∀ x : 𝓞 E, τ • x - x ∈ P) →
      (galSign α τ = 1 ∨ galSign α τ = e3 i) := by
    intro τ hτ
    have hoth : ∀ j, j ≠ i → galSign α τ j = 1 := by
      intro j hji
      rcases Int.units_eq_one_or (galSign α τ j) with h | h
      · exact h
      · exfalso
        have hd := hostIn_key hG q hq E α hα (q i) P τ hτ j h
        have := (Nat.prime_dvd_prime_iff_eq (hq.1 i).1 (hq.1 j).1).mp (by exact_mod_cast hd)
        exact hji (hq.2 this).symm
    rcases Int.units_eq_one_or (galSign α τ i) with h | h
    · left
      funext j
      by_cases hji : j = i
      · subst hji
        simpa using h
      · rw [hoth j hji]
        rfl
    · right
      funext j
      by_cases hji : j = i
      · subst hji
        simp [e3, h]
      · simp [e3, hji, hoth j hji]
  refine ⟨hfwd σ, fun h => ?_⟩
  rcases h with h | h
  · have : σ = 1 := hinj (h.trans h1.symm)
    subst this
    intro x
    simp
  · by_contra hn
    have hbot : P.inertia Gal(E/ℚ) = ⊥ := by
      rw [eq_bot_iff]
      intro τ hτ
      rw [Subgroup.mem_bot]
      rcases hfwd τ hτ with h' | h'
      · exact hinj (h'.trans h1.symm)
      · have := hinj (h'.trans h.symm)
        subst this
        exact absurd hτ hn
    have : Fact (q i).Prime := ⟨(hq.1 i).1⟩
    have hc := hostIn_card E (q i) P
    rw [hbot, Subgroup.card_bot] at hc
    exact hostIn_ram_ne_one q hq E α hα i P hc.symm

end Formalism.Q3
