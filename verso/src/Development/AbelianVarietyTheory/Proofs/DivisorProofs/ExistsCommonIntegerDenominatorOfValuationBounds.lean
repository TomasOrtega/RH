import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ γ hγ`. Establish `hfin : {u : Pl E | ¬ γ u ≤ 1}.Finite` using `Filter.eventually_cofinite.1 hγ`. Set `S : Finset (Pl E)` to `hfin.toFinset`. Set `k : Pl E → ℕ` to `fun u => (WithZero.log (γ u)).toNat`. Set `N : Pl E → ℕ` to `fun u => Ideal.absNorm u.asIdeal`.

Use `⟨∏ u ∈ S, N u ^ k u, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `u _`. Apply `pow_ne_zero` to reduce the goal to its premises. Simplify using `only [N, ne_eq, Ideal.absNorm_eq_zero_iff]`.

Conclude with `u.ne_bot`. Introduce `x hx`. Establish `hval : ∀ u : Pl E, u.valuation E x * u.valuation E ((∏ w ∈ S, N w ^ k w : ℕ) : E) ≤ 1`. Introduce `u`. Establish `hcast : (((∏ w ∈ S, N w ^ k w : ℕ) : E)) = algebraMap (𝓞 E) E ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E)` using `(map_natCast _ _).symm`.

Rewrite using `[hcast, HeightOneSpectrum.valuation_of_algebraMap]`. Distinguish the cases in `hu : γ u ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Establish `huS : u ∈ S`. Simplify using `only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]`.

Conclude with `hu`. Establish `hmem : ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E) ∈ u.asIdeal ^ k u`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem (fun w => N w ^ k w) huS`. Rewrite using `[hc, Nat.cast_mul]`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises.

Rewrite using `[Nat.cast_pow]`. Conclude with `Ideal.pow_mem_pow (Ideal.absNorm_mem u.asIdeal) _`. Establish `hle` using `(u.intValuation_le_pow_iff_mem _ (k u)).2 hmem`. Establish `h0 : γ u ≠ 0`. Introduce `h`.

Conclude with `hu (h ▸ zero_le')`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[WithZero.exp_add, WithZero.exp_log h0]`. Use `_ ≤ 1 := by`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_le_exp]`.

Use `Int.self_le_toNat (WithZero.log (γ u))` as an intermediate fact. Simplify using `only [k]`. Use linear arithmetic over natural numbers and integers. Take `⟨a, ha⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E (((∏ w ∈ S, N w ^ k w : ℕ) : E) * x) (fun u => by rw [map_mul, mul_comm]; exact hval u)`. Conclude with `⟨a, by rw [← ha]⟩`.
-/
theorem exists_nat_mul_integral_of_valuation_le : ∀ (E : Type) [Field E] [NumberField E] (γ : Pl E → WithZero (Multiplicative ℤ)), (∀ᶠ u in cofinite, γ u ≤ 1) → ∃ d : ℕ, d ≠ 0 ∧ ∀ x : E, (∀ u : Pl E, u.valuation E x ≤ γ u) → ∃ a : 𝓞 E, (a : E) = d * x := by
  intro E _ _ γ hγ
  have hfin : {u : Pl E | ¬ γ u ≤ 1}.Finite := Filter.eventually_cofinite.1 hγ
  let S : Finset (Pl E) := hfin.toFinset
  let k : Pl E → ℕ := fun u => (WithZero.log (γ u)).toNat
  let N : Pl E → ℕ := fun u => Ideal.absNorm u.asIdeal
  refine ⟨∏ u ∈ S, N u ^ k u, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro u _
    apply pow_ne_zero
    simp only [N, ne_eq, Ideal.absNorm_eq_zero_iff]
    exact u.ne_bot
  · intro x hx
    have hval : ∀ u : Pl E, u.valuation E x * u.valuation E ((∏ w ∈ S, N w ^ k w : ℕ) : E) ≤ 1 := by
      intro u
      have hcast : (((∏ w ∈ S, N w ^ k w : ℕ) : E)) =
          algebraMap (𝓞 E) E ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E) := (map_natCast _ _).symm
      rw [hcast, HeightOneSpectrum.valuation_of_algebraMap]
      by_cases hu : γ u ≤ 1
      · calc u.valuation E x * u.intValuation ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E)
            ≤ 1 * 1 := mul_le_mul' ((hx u).trans hu) (u.intValuation_le_one _)
          _ = 1 := one_mul 1
      · have huS : u ∈ S := by
          simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact hu
        have hmem : ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E) ∈ u.asIdeal ^ k u := by
          obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w => N w ^ k w) huS
          rw [hc, Nat.cast_mul]
          apply Ideal.mul_mem_right
          rw [Nat.cast_pow]
          exact Ideal.pow_mem_pow (Ideal.absNorm_mem u.asIdeal) _
        have hle := (u.intValuation_le_pow_iff_mem _ (k u)).2 hmem
        have h0 : γ u ≠ 0 := by
          intro h; exact hu (h ▸ zero_le')
        calc u.valuation E x * u.intValuation ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E)
            ≤ γ u * WithZero.exp (-(k u : ℤ)) := mul_le_mul' (hx u) hle
          _ = WithZero.exp (WithZero.log (γ u) + -(k u : ℤ)) := by
              rw [WithZero.exp_add, WithZero.exp_log h0]
          _ ≤ 1 := by
              rw [← WithZero.exp_zero, WithZero.exp_le_exp]
              have := Int.self_le_toNat (WithZero.log (γ u))
              simp only [k]
              omega
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E
      (((∏ w ∈ S, N w ^ k w : ℕ) : E) * x) (fun u => by rw [map_mul, mul_comm]; exact hval u)
    exact ⟨a, by rw [← ha]⟩

end GlobalTheory
