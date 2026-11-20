import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.AlgebraMapNeZeroOfMemHcompl

open NumberField

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3.WA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace BE

/- English proof (translation)
Establish `key : ∀ P : Ideal R, P.IsPrime → ¬ I ≤ I * P`. Introduce `P hP hle`. Establish `h1 : I * P = I * ⊤`. Rewrite using `[Ideal.mul_top]`. Conclude with `le_antisymm Ideal.mul_le_left hle`.

Conclude with `hP.ne_top (mul_left_cancel₀ hI h1)`. Establish `h1 : ¬ ((I : Set R) ⊆ (I * P : Ideal R) ∪ (I * Q : Ideal R))`. Introduce `h`. Break down `Ideal.subset_union.1 h with h | h` into its components or cases. Conclude with `key P hP h`.

Conclude with `key Q hQ h`. Take `⟨r, hrI, hr⟩` from `Set.not_subset.1 h1`. Establish `hrP : r ∉ I * P` using `fun h => hr (Or.inl h)`. Establish `hrQ : r ∉ I * Q` using `fun h => hr (Or.inr h)`. Establish `hr0 : r ≠ 0` using `fun h => hrP (h ▸ Ideal.zero_mem _)`.

Establish `hle : Ideal.span {r} ≤ I` using `(Ideal.span_singleton_le_iff_mem I).2 hrI`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.2 hle`. Establish `hmem : r ∈ I * J` using `hJ ▸ Ideal.mem_span_singleton_self r`. Establish `h2 : ¬ ((J : Set R) ⊆ (P : Ideal R) ∪ (Q : Ideal R))`. Introduce `h`.

Break down `Ideal.subset_union.1 h with h | h` into its components or cases. Conclude with `hrP (Ideal.mul_mono_right h hmem)`. Conclude with `hrQ (Ideal.mul_mono_right h hmem)`. Take `⟨s, hsJ, hs⟩` from `Set.not_subset.1 h2`. Use `⟨r, hrI, hr0, s, fun h => hs (Or.inl h), fun h => hs (Or.inr h), fun x hx => ?_⟩` and prove the remaining obligations.

Establish `h3 : x * s ∈ Ideal.span {r}` using `hJ ▸ Ideal.mul_mem_mul hx hsJ`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 h3`. Conclude with `⟨y, by rw [mul_comm s x, ← hy, mul_comm]⟩`.
-/
theorem exists_gen {R : Type*} [CommRing R] [IsDedekindDomain R] {I P Q : Ideal R} (hI : I ≠ ⊥)
    (hP : P.IsPrime) (hQ : Q.IsPrime) :
    ∃ r ∈ I, r ≠ 0 ∧ ∃ s : R, s ∉ P ∧ s ∉ Q ∧ ∀ x ∈ I, ∃ y : R, s * x = r * y := by
  have key : ∀ P : Ideal R, P.IsPrime → ¬ I ≤ I * P := by
    intro P hP hle
    have h1 : I * P = I * ⊤ := by
      rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left hle
    exact hP.ne_top (mul_left_cancel₀ hI h1)
  have h1 : ¬ ((I : Set R) ⊆ (I * P : Ideal R) ∪ (I * Q : Ideal R)) := by
    intro h
    rcases Ideal.subset_union.1 h with h | h
    · exact key P hP h
    · exact key Q hQ h
  obtain ⟨r, hrI, hr⟩ := Set.not_subset.1 h1
  have hrP : r ∉ I * P := fun h => hr (Or.inl h)
  have hrQ : r ∉ I * Q := fun h => hr (Or.inr h)
  have hr0 : r ≠ 0 := fun h => hrP (h ▸ Ideal.zero_mem _)
  have hle : Ideal.span {r} ≤ I := (Ideal.span_singleton_le_iff_mem I).2 hrI
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hmem : r ∈ I * J := hJ ▸ Ideal.mem_span_singleton_self r
  have h2 : ¬ ((J : Set R) ⊆ (P : Ideal R) ∪ (Q : Ideal R)) := by
    intro h
    rcases Ideal.subset_union.1 h with h | h
    · exact hrP (Ideal.mul_mono_right h hmem)
    · exact hrQ (Ideal.mul_mono_right h hmem)
  obtain ⟨s, hsJ, hs⟩ := Set.not_subset.1 h2
  refine ⟨r, hrI, hr0, s, fun h => hs (Or.inl h), fun h => hs (Or.inr h), fun x hx => ?_⟩
  have h3 : x * s ∈ Ideal.span {r} := hJ ▸ Ideal.mul_mem_mul hx hsJ
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h3
  exact ⟨y, by rw [mul_comm s x, ← hy, mul_comm]⟩

/- English proof (translation)
Establish `hP : ∀ c : R, s - c * a ∉ P`. Introduce `c h`. Apply `hsP` to reduce the goal to its premises. Use `P.add_mem h (P.mul_mem_left c ha)` as an intermediate fact. Simplify using `using this`.

Distinguish the cases in `h1 : s - k * a ∈ Q`. Use `right`. Use `⟨hP _, fun h2 => ?_⟩` and prove the remaining obligations. Establish `h3 : m * a ∈ Q`. Use `Q.sub_mem h1 h2` as an intermediate fact.

Establish `e : s - k * a - (s - (k + m) * a) = m * a` using `by ring`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Break down `hQ.mem_or_mem h3 with h | h` into its components or cases. Conclude with `hm h`. Apply `hsQ` to reduce the goal to its premises.

Use `Q.add_mem h1 (Q.mul_mem_left k h)` as an intermediate fact. Simplify using `using this`. Conclude with `Or.inl ⟨hP _, h1⟩`.
-/
theorem avoid_two {R : Type*} [CommRing R] {P Q : Ideal R} (hQ : Q.IsPrime) {a s m : R} (k : R)
    (ha : a ∈ P) (hsP : s ∉ P) (hsQ : s ∉ Q) (hm : m ∉ Q) :
    (s - k * a ∉ P ∧ s - k * a ∉ Q) ∨ (s - (k + m) * a ∉ P ∧ s - (k + m) * a ∉ Q) := by
  have hP : ∀ c : R, s - c * a ∉ P := by
    intro c h
    apply hsP
    have := P.add_mem h (P.mul_mem_left c ha)
    simpa using this
  by_cases h1 : s - k * a ∈ Q
  · right
    refine ⟨hP _, fun h2 => ?_⟩
    have h3 : m * a ∈ Q := by
      have := Q.sub_mem h1 h2
      have e : s - k * a - (s - (k + m) * a) = m * a := by ring
      rwa [e] at this
    rcases hQ.mem_or_mem h3 with h | h
    · exact hm h
    · apply hsQ
      have := Q.add_mem h1 (Q.mul_mem_left k h)
      simpa using this
  · exact Or.inl ⟨hP _, h1⟩

end BE

/- English proof (translation)
Take `⟨t, ht0, ht⟩` from `ht`. Establish `hpp` using `hp.isPrime`. Set `I : Ideal (𝓞 K)` to `{ carrier := {r | algebraMap (𝓞 K) K r * t⁻¹ ∈ A} add_mem' := by`. Introduce `x y hx hy`. Simplify using `only [Set.mem_ofPred_eq, map_add, add_mul] at *`.

Conclude with `A.add_mem hx hy`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := by`. Introduce `c x hx`. Simplify using `only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, mul_assoc] at *`.

Conclude with `hA _ (algebraMap_mem_locRing p c) _ hx }`. Establish `hmemI : ∀ r : 𝓞 K, r ∈ I ↔ algebraMap (𝓞 K) K r * t⁻¹ ∈ A` using `fun r => Iff.rfl`. Establish `hrep : ∀ a ∈ A, ∃ x ∈ I, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `K) p, a = algebraMap (𝓞 K) K x / (algebraMap (𝓞 K) K s * t) := by`. Introduce `a ha`. Take `⟨x, s, hs, hx⟩` from `(mem_locR_iff hpp _).1 ((mem_locRing p _).1 (ht a ha))`.

Establish `hs0` using `algebraMap_ne_zero_of_mem_hcompl hpp hs`. Establish `e : algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K s * (t * a)`. Rewrite using `[hx]`. Clear the denominators using the available nonvanishing facts. Use `⟨x, ?_, s, hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmemI, e]`. Establish `: algebraMap (𝓞 K) K s * (t * a) * t⁻¹ = algebraMap (𝓞 K) K s * a` using `by field_simp`. Rewrite using `[this]`. Conclude with `hA _ (algebraMap_mem_locRing p s) _ ha`. Rewrite using `[e]`.

Clear the denominators using the available nonvanishing facts. Establish `hI : I ≠ ⊥`. Take `⟨a, ha, ha0⟩` from `h0`. Take `⟨x, hx, s, hs, e⟩` from `hrep a ha`. Introduce `hbot`.

Rewrite `hx` using `[hbot, Ideal.mem_bot]`. Apply `ha0` to reduce the goal to its premises. Rewrite using `[e, hx]`. Simplify using the standard rewrite rules. Take `⟨r, hrI, hr0, s, hsP, hsQ, hgen⟩` from `BE.exists_gen hI hpp (conjIdeal_isPrime hpp)`.

Establish `hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `K) p := (mem_hcompl_iff hpp s).2 ⟨hsP, hsQ⟩`. Establish `hs0` using `algebraMap_ne_zero_of_mem_hcompl hpp hs`. Establish `hr0' : algebraMap (𝓞 K) K r ≠ 0`. Introduce `h`. Conclude with `hr0 ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).1 h)`.

Use `⟨algebraMap (𝓞 K) K r * t⁻¹, (hmemI r).1 hrI, mul_ne_zero hr0' (inv_ne_zero ht0), ?_⟩` and prove the remaining obligations. Introduce `a ha`. Take `⟨x, hx, s', hs', e⟩` from `hrep a ha`. Establish `hs0'` using `algebraMap_ne_zero_of_mem_hcompl hpp hs'`. Take `⟨y, hy⟩` from `hgen x hx`.

Establish `hy' : algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K r * algebraMap (𝓞 K) K y`. Rewrite using `[← map_mul, ← map_mul, hy]`. Rewrite using `[mem_locRing, mem_locR_iff hpp]`. Use `⟨y, s * s', mul_mem hs hs', ?_⟩` and prove the remaining obligations. Rewrite using `[e, map_mul]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `hy'`.
-/
theorem principal_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal)
    (A : AddSubgroup K) (hA : ∀ s ∈ locRing p, ∀ a ∈ A, s * a ∈ A) (h0 : ∃ a ∈ A, a ≠ 0)
    (ht : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ locRing p) :
    ∃ α ∈ A, α ≠ 0 ∧ ∀ a ∈ A, a * α⁻¹ ∈ locRing p := by
  obtain ⟨t, ht0, ht⟩ := ht
  have hpp := hp.isPrime
  let I : Ideal (𝓞 K) :=
    { carrier := {r | algebraMap (𝓞 K) K r * t⁻¹ ∈ A}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, map_add, add_mul] at *
        exact A.add_mem hx hy
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, mul_assoc] at *
        exact hA _ (algebraMap_mem_locRing p c) _ hx }
  have hmemI : ∀ r : 𝓞 K, r ∈ I ↔ algebraMap (𝓞 K) K r * t⁻¹ ∈ A := fun r => Iff.rfl

  have hrep : ∀ a ∈ A, ∃ x ∈ I, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
      a = algebraMap (𝓞 K) K x / (algebraMap (𝓞 K) K s * t) := by
    intro a ha
    obtain ⟨x, s, hs, hx⟩ := (mem_locR_iff hpp _).1 ((mem_locRing p _).1 (ht a ha))
    have hs0 := algebraMap_ne_zero_of_mem_hcompl hpp hs
    have e : algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K s * (t * a) := by
      rw [hx]; field_simp
    refine ⟨x, ?_, s, hs, ?_⟩
    · rw [hmemI, e]
      have : algebraMap (𝓞 K) K s * (t * a) * t⁻¹ = algebraMap (𝓞 K) K s * a := by field_simp
      rw [this]
      exact hA _ (algebraMap_mem_locRing p s) _ ha
    · rw [e]; field_simp
  have hI : I ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := h0
    obtain ⟨x, hx, s, hs, e⟩ := hrep a ha
    intro hbot
    rw [hbot, Ideal.mem_bot] at hx
    apply ha0
    rw [e, hx]; simp
  obtain ⟨r, hrI, hr0, s, hsP, hsQ, hgen⟩ := BE.exists_gen hI hpp (conjIdeal_isPrime hpp)
  have hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := (mem_hcompl_iff hpp s).2 ⟨hsP, hsQ⟩
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hpp hs
  have hr0' : algebraMap (𝓞 K) K r ≠ 0 := by
    intro h
    exact hr0 ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).1 h)
  refine ⟨algebraMap (𝓞 K) K r * t⁻¹, (hmemI r).1 hrI, mul_ne_zero hr0' (inv_ne_zero ht0), ?_⟩
  intro a ha
  obtain ⟨x, hx, s', hs', e⟩ := hrep a ha
  have hs0' := algebraMap_ne_zero_of_mem_hcompl hpp hs'
  obtain ⟨y, hy⟩ := hgen x hx
  have hy' : algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K x
      = algebraMap (𝓞 K) K r * algebraMap (𝓞 K) K y := by
    rw [← map_mul, ← map_mul, hy]
  rw [mem_locRing, mem_locR_iff hpp]
  refine ⟨y, s * s', mul_mem hs hs', ?_⟩
  rw [e, map_mul]
  field_simp
  linear_combination hy'

/- English proof (translation)
Take `⟨a₁, s₁, hs₁, ea⟩` from `(mem_locR_iff hp _).1 ((mem_locRing p _).1 ha)`. Take `⟨k₁, s₂, hs₂, ek⟩` from `(mem_locR_iff hp _).1 ((mem_locRing p _).1 hκ)`. Take `⟨m₁, s₃, hs₃, em⟩` from `(mem_locR_iff hp _).1 ((mem_locRing p _).1 hμ.2.1)`. Establish `h1` using `algebraMap_ne_zero_of_mem_hcompl hp hs₁`. Establish `h2` using `algebraMap_ne_zero_of_mem_hcompl hp hs₂`.

Establish `h3` using `algebraMap_ne_zero_of_mem_hcompl hp hs₃`. Establish `hm₁ : m₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `K) p := (isUnitIn_div_iff hp m₁ hs₃).1 (em ▸ hμ)`. Establish `ha₁ : a₁ ∉ Formalism.HermitianLatticesTheory.hcompl (K` using `K) p := by`. Introduce `h`. Use `(isUnitIn_div_iff hp a₁ hs₁).2 h` as an intermediate fact.

Rewrite `this` using `[← ea]`. Conclude with `hna this.2.2`. Establish `hQ` using `conjIdeal_isPrime hp`. Use `set S : 𝓞 K := s₁ * s₂ * s₃ with hS`. Establish `hSm : S ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `K) p := mul_mem (mul_mem hs₁ hs₂) hs₃`.

Establish `hS'` using `(mem_hcompl_iff hp S).1 hSm`. Establish `hM : m₁ * s₂ ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `K) p := mul_mem hm₁ hs₂`. Establish `hM'` using `(mem_hcompl_iff hp _).1 hM`. Establish `e1 : (1 - κ * a) = algebraMap (𝓞 K) K (S - (k₁ * s₃) * a₁) / algebraMap (𝓞 K) K S`. Rewrite using `[ea, ek, hS]`.

Simplify using `only [map_sub, map_mul]`. Clear the denominators using the available nonvanishing facts. Establish `e2 : (1 - (κ + μ) * a) = algebraMap (𝓞 K) K (S - (k₁ * s₃ + m₁ * s₂) * a₁) / algebraMap (𝓞 K) K S`. Rewrite using `[ea, ek, em, hS]`. Simplify using `only [map_sub, map_mul, map_add]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, e2, isUnitIn_div_iff hp _ hSm, isUnitIn_div_iff hp _ hSm, mem_hcompl_iff hp, mem_hcompl_iff hp]`. Establish `hor : a₁ ∈ p ∨ a₁ ∈ Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) p := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `ha₁ ((mem_hcompl_iff hp a₁).2 h)`. Break down `hor with h | h` into its components or cases. Conclude with `BE.avoid_two hQ (k₁ * s₃) h hS'.1 hS'.2 hM'.2`. Break down `BE.avoid_two hp (k₁ * s₃) h hS'.2 hS'.1 hM'.1 with h | h` into its components or cases. Conclude with `Or.inl h.symm`.

Conclude with `Or.inr h.symm`.
-/
theorem unit_or_locRing {p : Ideal (𝓞 K)} (hp : p.IsPrime) (a : K) (ha : a ∈ locRing p)
    (κ : K) (hκ : κ ∈ locRing p) (μ : K) (hna : a⁻¹ ∉ locRing p) (hμ : IsUnitIn (locRing p) μ) :
    IsUnitIn (locRing p) (1 - κ * a) ∨ IsUnitIn (locRing p) (1 - (κ + μ) * a) := by
  obtain ⟨a₁, s₁, hs₁, ea⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 ha)
  obtain ⟨k₁, s₂, hs₂, ek⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 hκ)
  obtain ⟨m₁, s₃, hs₃, em⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 hμ.2.1)
  have h1 := algebraMap_ne_zero_of_mem_hcompl hp hs₁
  have h2 := algebraMap_ne_zero_of_mem_hcompl hp hs₂
  have h3 := algebraMap_ne_zero_of_mem_hcompl hp hs₃
  have hm₁ : m₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := (isUnitIn_div_iff hp m₁ hs₃).1 (em ▸ hμ)
  have ha₁ : a₁ ∉ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    intro h
    have := (isUnitIn_div_iff hp a₁ hs₁).2 h
    rw [← ea] at this
    exact hna this.2.2
  have hQ := conjIdeal_isPrime hp
  set S : 𝓞 K := s₁ * s₂ * s₃ with hS
  have hSm : S ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := mul_mem (mul_mem hs₁ hs₂) hs₃
  have hS' := (mem_hcompl_iff hp S).1 hSm
  have hM : m₁ * s₂ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := mul_mem hm₁ hs₂
  have hM' := (mem_hcompl_iff hp _).1 hM
  have e1 : (1 - κ * a) = algebraMap (𝓞 K) K (S - (k₁ * s₃) * a₁) / algebraMap (𝓞 K) K S := by
    rw [ea, ek, hS]; simp only [map_sub, map_mul]; field_simp
  have e2 : (1 - (κ + μ) * a)
      = algebraMap (𝓞 K) K (S - (k₁ * s₃ + m₁ * s₂) * a₁) / algebraMap (𝓞 K) K S := by
    rw [ea, ek, em, hS]; simp only [map_sub, map_mul, map_add]; field_simp
  rw [e1, e2, isUnitIn_div_iff hp _ hSm, isUnitIn_div_iff hp _ hSm, mem_hcompl_iff hp,
    mem_hcompl_iff hp]
  have hor : a₁ ∈ p ∨ a₁ ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
    by_contra h
    push Not at h
    exact ha₁ ((mem_hcompl_iff hp a₁).2 h)
  rcases hor with h | h
  · exact BE.avoid_two hQ (k₁ * s₃) h hS'.1 hS'.2 hM'.2
  · rcases BE.avoid_two hp (k₁ * s₃) h hS'.2 hS'.1 hM'.1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm

/- English proof (translation)
Introduce `_ ha` and use `star_mem_locRing hp.isPrime ha frac := frac_locRing p unram := unram_locRing hK hp principal := principal_locRing hK hp unit_or := fun a ha κ hκ μ hna hμ => unit_or_locRing hp.isPrime a ha κ hκ μ hna hμ`.
-/
theorem isHermSemilocal_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)}
    (hp : p.IsMaximal) : IsHermSemilocal (locRing p) where
  star_mem := fun _ ha => star_mem_locRing hp.isPrime ha
  frac := frac_locRing p
  unram := unram_locRing hK hp
  principal := principal_locRing hK hp
  unit_or := fun a ha κ hκ μ hna hμ => unit_or_locRing hp.isPrime a ha κ hκ μ hna hμ

end ReciprocityTheory.ChartRestriction.L3.WA
