import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Introduce `O V St _ _ _ S j J hJ hstep`. Establish `key : ∀ (n : ℕ) (s : St), J - j s ≤ n → Module.length O (S s) + j s ≤ J`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Introduce `s hs`. Distinguish the cases in `h : S s = ⊥`. Establish `h0 : Module.length O (S s) = 0`. Rewrite using `[h]`. Conclude with `Module.length_eq_zero`.

Rewrite using `[h0, zero_add]`. Conclude with `hJ s` after adjusting the coercions. Take `⟨s', h1, -⟩` from `hstep s h`. Use `hJ s'` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Consider the case `succ n ih`. Introduce `s hs`. Distinguish the cases in `h : S s = ⊥`. Establish `h0 : Module.length O (S s) = 0`. Rewrite using `[h]`.

Conclude with `Module.length_eq_zero`. Rewrite using `[h0, zero_add]`. Conclude with `hJ s` after adjusting the coercions. Take `⟨s', h1, h2⟩` from `hstep s h`. Use `hJ s'` as an intermediate fact.

Conclude with `h2.trans (ih s' (by omega))`. Introduce `s`. Conclude with `key _ s le_rfl`.
-/
theorem UpperTheory.V.ML.chain :
    ∀ (O V St : Type) [CommRing O] [AddCommGroup V] [Module O V] (S : St → Submodule O V) (j : St → ℕ) (J : ℕ), (∀ s, j s ≤ J) →
    (∀ s, S s ≠ ⊥ → ∃ s', j s < j s' ∧ Module.length O (S s) + j s ≤ Module.length O (S s') + j s') → ∀ s, Module.length O (S s) + j s ≤ J := by
  intro O V St _ _ _ S j J hJ hstep
  have key : ∀ (n : ℕ) (s : St), J - j s ≤ n → Module.length O (S s) + j s ≤ J := by
    intro n
    induction n with
    | zero =>
      intro s hs
      by_cases h : S s = ⊥
      · have h0 : Module.length O (S s) = 0 := by
          rw [h]; exact Module.length_eq_zero
        rw [h0, zero_add]
        exact_mod_cast hJ s
      · obtain ⟨s', h1, -⟩ := hstep s h
        have := hJ s'
        omega
    | succ n ih =>
      intro s hs
      by_cases h : S s = ⊥
      · have h0 : Module.length O (S s) = 0 := by
          rw [h]; exact Module.length_eq_zero
        rw [h0, zero_add]
        exact_mod_cast hJ s
      · obtain ⟨s', h1, h2⟩ := hstep s h
        have := hJ s'
        exact h2.trans (ih s' (by omega))
  intro s
  exact key _ s le_rfl
