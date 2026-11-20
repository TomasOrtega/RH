import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenOfNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.RamUnit

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ L`. Establish `h2 : (2 : K) ≠ 0` using `L.two_ne`. Use `haveI := L.frac`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hx hy`.

Unfold `hs`. Distinguish the cases in `h1 : ∃ a b : K, a ^ 2 - x * b ^ 2 = y`. Rewrite using `[if_pos h1, if_pos (nm_symm hx h2 h1 hy)]`. Establish `h1' : ¬ ∃ a b : K, a ^ 2 - y * b ^ 2 = x` using `fun h => h1 (nm_symm hy h2 h hx)`. Rewrite using `[if_neg h1, if_neg h1']`.

Introduce and unpack `x y ⟨U, s, hs0, rfl⟩ ⟨V, t, -, rfl⟩`. Take `⟨a, b, hab⟩` from `L.nm_unit U V`. Establish `hK` using `congrArg (algebraMap O K) hab`. Simplify using `only [map_sub, map_mul, map_pow] at hK`. Unfold `hs`.

Rewrite using `[if_pos]`. Use `⟨algebraMap O K a * t, algebraMap O K b * t / s, ?_⟩` and prove the remaining obligations. Rewrite using `[← hK]`. Clear the denominators using the available nonvanishing facts. Introduce `D hD hsq`.

Distinguish the cases in `he : EvenVal O D`. Take `⟨U, s, hs0, rfl⟩` from `he`. Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hUsq : ¬ IsSquare (algebraMap O K U)`. Introduce and unpack `⟨r, hr⟩`.

Conclude with `hsq ⟨r * s, by rw [hr]; ring⟩`. Establish `hp0 : algebraMap O K p ≠ 0`. Introduce `h0`. Apply `hp.ne_zero` to reduce the goal to its premises. Apply `IsFractionRing.injective O K` to reduce the goal to its premises.

Rewrite using `[h0, map_zero]`. Use `⟨algebraMap O K p, hp0, ?_⟩` and prove the remaining obligations. Unfold `hs`. Rewrite using `[if_neg]`. Introduce and unpack `⟨a, b, hab⟩`.

Establish `e : a ^ 2 - algebraMap O K ↑U * (s * b) ^ 2 = algebraMap O K p`. Rewrite using `[← hab]`. Expand and normalize the polynomial expressions, which then agree. Apply `L.not_even hp` to reduce the goal to its premises. Rewrite using `[← e]`.

Conclude with `L.even_of_norm U hUsq (by rw [e]; exact hp0)`. Take `⟨ε, hε⟩` from `ramUnit O K Δ L D hD he`. Use `⟨algebraMap O K ε, ?_, hε⟩` and prove the remaining obligations. Introduce `h0`. Rewrite `hε` using `[h0]`.

Unfold `hs at hε`. Rewrite `hε` using `[if_pos ⟨0, 0, by ring⟩]`. Evaluate the numerical expressions using `at hε`. Introduce and unpack `D x hD ⟨r, rfl⟩`. Establish `hr : r ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hD`. Unfold `hs`. Rewrite using `[if_pos]`. Use `⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.Sym.Loc.hsLaw : UpperTheory.V.Z.Sym.Loc.HsLaw := by
  intro O K _ _ _ _ _ Δ L
  have h2 : (2 : K) ≠ 0 := L.two_ne
  haveI := L.frac
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    unfold hs
    by_cases h1 : ∃ a b : K, a ^ 2 - x * b ^ 2 = y
    · rw [if_pos h1, if_pos (nm_symm hx h2 h1 hy)]
    · have h1' : ¬ ∃ a b : K, a ^ 2 - y * b ^ 2 = x := fun h => h1 (nm_symm hy h2 h hx)
      rw [if_neg h1, if_neg h1']
  · rintro x y ⟨U, s, hs0, rfl⟩ ⟨V, t, -, rfl⟩
    obtain ⟨a, b, hab⟩ := L.nm_unit U V
    have hK := congrArg (algebraMap O K) hab
    simp only [map_sub, map_mul, map_pow] at hK
    unfold hs
    rw [if_pos]
    refine ⟨algebraMap O K a * t, algebraMap O K b * t / s, ?_⟩
    rw [← hK]
    field_simp
  · intro D hD hsq
    by_cases he : EvenVal O D
    · obtain ⟨U, s, hs0, rfl⟩ := he
      obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
      have hUsq : ¬ IsSquare (algebraMap O K U) := by
        rintro ⟨r, hr⟩
        exact hsq ⟨r * s, by rw [hr]; ring⟩
      have hp0 : algebraMap O K p ≠ 0 := by
        intro h0
        apply hp.ne_zero
        apply IsFractionRing.injective O K
        rw [h0, map_zero]
      refine ⟨algebraMap O K p, hp0, ?_⟩
      unfold hs
      rw [if_neg]
      rintro ⟨a, b, hab⟩
      have e : a ^ 2 - algebraMap O K ↑U * (s * b) ^ 2 = algebraMap O K p := by
        rw [← hab]; ring
      apply L.not_even hp
      rw [← e]
      exact L.even_of_norm U hUsq (by rw [e]; exact hp0)
    · obtain ⟨ε, hε⟩ := ramUnit O K Δ L D hD he
      refine ⟨algebraMap O K ε, ?_, hε⟩
      intro h0
      rw [h0] at hε
      unfold hs at hε
      rw [if_pos ⟨0, 0, by ring⟩] at hε
      norm_num at hε
  · rintro D x hD ⟨r, rfl⟩
    have hr : r ≠ 0 := by
      rintro rfl
      simp at hD
    unfold hs
    rw [if_pos]
    refine ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩
    field_simp
    ring
