import Mathlib

open Polynomial Matrix

/- English proof (translation)
Use `set_option maxRecDepth 100000 in`. Evaluate the decidable proposition.
-/
private theorem UpperTheory.V.AlgebraTools.perm_four_pow_three_or_four :
    ∀ σ : Equiv.Perm (Fin 4), σ ^ 3 = 1 ∨ σ ^ 4 = 1 := by
  set_option maxRecDepth 100000 in
  decide

/- English proof (translation)
Introduce `G K _ _ π χ hker`. Establish `hχ : ∀ g : G, χ g ^ 3 = 1 ∨ χ g ^ 4 = 1` using `fun g => by`. Break down `UpperTheory.V.AlgebraTools.perm_four_pow_three_or_four (π g) with h | h` into its components or cases. Use `left`. Establish `hm : g ^ 3 ∈ π.ker` using `by rw [MonoidHom.mem_ker, map_pow, h]`.

Establish `hm'` using `hker hm`. Rewrite `hm'` using `[MonoidHom.mem_ker, map_pow]`. Then use the resulting hypothesis. Use `right`. Establish `hm : g ^ 4 ∈ π.ker` using `by rw [MonoidHom.mem_ker, map_pow, h]`. Establish `hm'` using `hker hm`.

Rewrite `hm'` using `[MonoidHom.mem_ker, map_pow]`. Then use the resulting hypothesis. Establish `hall : (∀ g : G, χ g ^ 3 = 1) ∨ (∀ g : G, χ g ^ 4 = 1)`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨⟨g, hg⟩, ⟨g', hg'⟩⟩` from `hne`.

Establish `h4 : χ g ^ 4 = 1` using `(hχ g).resolve_left hg`. Establish `h3 : χ g' ^ 3 = 1` using `(hχ g').resolve_right hg'`. Break down `hχ (g * g') with h | h` into its components or cases. Rewrite `h` using `[map_mul, mul_pow, h3, mul_one]`. Conclude with `hg h`.

Rewrite `h` using `[map_mul, mul_pow, h4, one_mul]`. Conclude with `hg' h`. Establish `key : ∀ k, 0 < k → (∀ g : G, χ g ^ k = 1) → 0 < orderOf χ ∧ orderOf χ ≤ k`. Introduce `k hk0 h`. Establish `hp : χ ^ k = 1` using `MonoidHom.ext fun g => by`.

Rewrite using `[MonoidHom.pow_apply, MonoidHom.one_apply]`. Conclude with `h g`. Conclude with `⟨orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hk0, hp⟩), orderOf_le_of_pow_eq_one hk0 hp⟩`. Break down `hall with h | h` into its components or cases. Take `⟨a, b⟩` from `key 3 (by norm_num) h`.

Conclude with `⟨a, b.trans (by norm_num)⟩`. Conclude with `key 4 (by norm_num) h`.
-/
theorem UpperTheory.V.AlgebraTools.permChar :
    ∀ (G K : Type) [Group G] [Field K] (π : G →* Equiv.Perm (Fin 4)) (χ : G →* Kˣ), π.ker ≤ χ.ker → 0 < orderOf χ ∧ orderOf χ ≤ 4 := by
  intro G K _ _ π χ hker
  have hχ : ∀ g : G, χ g ^ 3 = 1 ∨ χ g ^ 4 = 1 := fun g => by
    rcases UpperTheory.V.AlgebraTools.perm_four_pow_three_or_four (π g) with h | h
    · left
      have hm : g ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, h]
      have hm' := hker hm
      rwa [MonoidHom.mem_ker, map_pow] at hm'
    · right
      have hm : g ^ 4 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, h]
      have hm' := hker hm
      rwa [MonoidHom.mem_ker, map_pow] at hm'
  have hall : (∀ g : G, χ g ^ 3 = 1) ∨ (∀ g : G, χ g ^ 4 = 1) := by
    by_contra hne
    push_neg at hne
    obtain ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩ := hne
    have h4 : χ g ^ 4 = 1 := (hχ g).resolve_left hg
    have h3 : χ g' ^ 3 = 1 := (hχ g').resolve_right hg'
    rcases hχ (g * g') with h | h
    · rw [map_mul, mul_pow, h3, mul_one] at h
      exact hg h
    · rw [map_mul, mul_pow, h4, one_mul] at h
      exact hg' h
  have key : ∀ k, 0 < k → (∀ g : G, χ g ^ k = 1) → 0 < orderOf χ ∧ orderOf χ ≤ k := by
    intro k hk0 h
    have hp : χ ^ k = 1 := MonoidHom.ext fun g => by
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact h g
    exact ⟨orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hk0, hp⟩),
      orderOf_le_of_pow_eq_one hk0 hp⟩
  rcases hall with h | h
  · obtain ⟨a, b⟩ := key 3 (by norm_num) h
    exact ⟨a, b.trans (by norm_num)⟩
  · exact key 4 (by norm_num) h
