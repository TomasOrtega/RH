import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ A hl m hm ζ hζ`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `(Fact.out : l.Prime).one_lt.ne' (Nat.coprime_zero_left _ |>.mp hm)`. Establish `hv1 : ∀ x : Ω, x ^ m = 1 → A.valuation x = 1`.

Introduce `x hx`. Establish `h` using `congrArg A.valuation hx`. Rewrite `h` using `[map_pow, map_one]`. Break down `lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1` into its components or cases. Conclude with `absurd h (pow_lt_one₀ zero_le' h1 hm0).ne`.

Conclude with `h1`. Conclude with `absurd h (one_lt_pow₀ h1 hm0).ne'`. Establish `hint : ∀ a : ℤ, A.valuation (a : Ω) ≤ 1` using `fun a => by`. Simplify using `using A.valuation_le_one (a : A)`. Establish `hmv : ¬ A.valuation (m : Ω) < 1`.

Introduce `hlt`. Establish `hg : ((Nat.gcd m l : ℕ) : ℤ) = m * Nat.gcdA m l + l * Nat.gcdB m l` using `Nat.gcd_eq_gcd_ab m l`. Rewrite `hg` using `[Nat.Coprime.gcd_eq_one hm]`. Establish `hΩ` using `congrArg (Int.cast : ℤ → Ω) hg`. Move the coercions through the operations in `at hΩ`.

Establish `h1 : A.valuation (1 : Ω) < 1`. Rewrite using `[hΩ]`. Apply `Valuation.map_add_lt` to reduce the goal to its premises. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hlt`.

Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hl`. Simplify using `at h1`. Establish `part1 : ∀ ξ : Ω, ξ ^ m = 1 → A.valuation (ξ - ζ) < 1 → ξ = ζ`. Introduce `ξ hξ hlt`.

Assume the negation of the conclusion as `hne`. Establish `hζ0 : ζ ≠ 0`. Introduce and unpack `rfl`. Simplify using `[zero_pow hm0] at hζ`. Use `set η := ξ / ζ with hηdef`.

Establish `hη : η ^ m = 1` using `by rw [hηdef, div_pow, hξ, hζ, div_one]`. Establish `hη1 : η ≠ 1` using `fun h => hne ((div_eq_one_iff_eq hζ0).mp h)`. Establish `hvη : A.valuation (η - 1) < 1`. Establish `e : η - 1 = (ξ - ζ) / ζ` using `by rw [hηdef, sub_div, div_self hζ0]`. Rewrite using `[e, map_div₀, hv1 ζ hζ, div_one]`.

Conclude with `hlt`. Establish `hpow1 : ∀ j, A.valuation (η ^ j) = 1` using `fun j => by rw [map_pow, hv1 η hη, one_pow]`. Establish `hterm : ∀ i, A.valuation (1 - η ^ i) < 1`. Introduce `i`. Establish `e : 1 - η ^ i = -((∑ j ∈ Finset.range i, η ^ j) * (η - 1))`.

Rewrite using `[geom_sum_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Valuation.map_neg, map_mul]`. Establish `hs : A.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1` using `A.valuation.map_sum_le (fun j _ => (hpow1 j).le)`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' hs) hvη`.

Establish `hsum0 : ∑ i ∈ Finset.range m, η ^ i = 0`. Rewrite using `[geom_sum_eq hη1, hη, sub_self, zero_div]`. Establish `hmΩ : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i)`. Rewrite using `[Finset.sum_sub_distrib, hsum0, sub_zero]`. Simplify using the standard rewrite rules.

Apply `hmv` to reduce the goal to its premises. Rewrite using `[hmΩ]`. Conclude with `A.valuation.map_sum_lt one_ne_zero (fun i _ => hterm i)`. Use `⟨part1, ?_⟩` and prove the remaining obligations. Introduce `g hg`.

Establish `hg2` using `(mem_Ine.mp hg).2`. Apply `part1` to reduce the goal to its premises. Rewrite using `[← map_pow, hζ, map_one]`. Conclude with `hg2 ζ (hv1 ζ hζ).le`.
-/
theorem UpperTheory.V.LDataCardLeFinrank.ineFixRoots :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (m : ℕ), m.Coprime l → ∀ ζ : Ω, ζ ^ m = 1 →
      (∀ ξ : Ω, ξ ^ m = 1 → A.valuation (ξ - ζ) < 1 → ξ = ζ) ∧ ∀ g ∈ Ine (F := F) A, g ζ = ζ := by
  intro F Ω _ _ _ _ _ l _ A hl m hm ζ hζ
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.coprime_zero_left _ |>.mp hm)
  have hv1 : ∀ x : Ω, x ^ m = 1 → A.valuation x = 1 := by
    intro x hx
    have h := congrArg A.valuation hx
    rw [map_pow, map_one] at h
    rcases lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1
    · exact absurd h (pow_lt_one₀ zero_le' h1 hm0).ne
    · exact h1
    · exact absurd h (one_lt_pow₀ h1 hm0).ne'
  have hint : ∀ a : ℤ, A.valuation (a : Ω) ≤ 1 := fun a => by
    simpa using A.valuation_le_one (a : A)
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    intro hlt
    have hg : ((Nat.gcd m l : ℕ) : ℤ) = m * Nat.gcdA m l + l * Nat.gcdB m l := Nat.gcd_eq_gcd_ab m l
    rw [Nat.Coprime.gcd_eq_one hm] at hg
    have hΩ := congrArg (Int.cast : ℤ → Ω) hg
    push_cast at hΩ
    have h1 : A.valuation (1 : Ω) < 1 := by
      rw [hΩ]
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hlt
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hl
    simp at h1
  have part1 : ∀ ξ : Ω, ξ ^ m = 1 → A.valuation (ξ - ζ) < 1 → ξ = ζ := by
    intro ξ hξ hlt
    by_contra hne
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      simp [zero_pow hm0] at hζ
    set η := ξ / ζ with hηdef
    have hη : η ^ m = 1 := by rw [hηdef, div_pow, hξ, hζ, div_one]
    have hη1 : η ≠ 1 := fun h => hne ((div_eq_one_iff_eq hζ0).mp h)
    have hvη : A.valuation (η - 1) < 1 := by
      have e : η - 1 = (ξ - ζ) / ζ := by rw [hηdef, sub_div, div_self hζ0]
      rw [e, map_div₀, hv1 ζ hζ, div_one]
      exact hlt
    have hpow1 : ∀ j, A.valuation (η ^ j) = 1 := fun j => by rw [map_pow, hv1 η hη, one_pow]
    have hterm : ∀ i, A.valuation (1 - η ^ i) < 1 := by
      intro i
      have e : 1 - η ^ i = -((∑ j ∈ Finset.range i, η ^ j) * (η - 1)) := by
        rw [geom_sum_mul]
        ring
      rw [e, Valuation.map_neg, map_mul]
      have hs : A.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 :=
        A.valuation.map_sum_le (fun j _ => (hpow1 j).le)
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hs) hvη
    have hsum0 : ∑ i ∈ Finset.range m, η ^ i = 0 := by
      rw [geom_sum_eq hη1, hη, sub_self, zero_div]
    have hmΩ : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
      rw [Finset.sum_sub_distrib, hsum0, sub_zero]
      simp
    apply hmv
    rw [hmΩ]
    exact A.valuation.map_sum_lt one_ne_zero (fun i _ => hterm i)
  refine ⟨part1, ?_⟩
  intro g hg
  have hg2 := (mem_Ine.mp hg).2
  apply part1
  · rw [← map_pow, hζ, map_one]
  · exact hg2 ζ (hv1 ζ hζ).le
