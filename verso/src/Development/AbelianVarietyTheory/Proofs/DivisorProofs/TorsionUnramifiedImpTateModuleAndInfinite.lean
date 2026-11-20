import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof

/- English proof (translation)
Distinguish the cases in `h2 : ((2 : ℕ) : k) = 0`. Use `⟨3, ⟨Nat.prime_three⟩, fun h3 => one_ne_zero (α := k) ?_⟩` and prove the remaining obligations. Establish `: ((3 : ℕ) : k) - ((2 : ℕ) : k) = 1` using `by push_cast; ring`. Rewrite using `[← this, h2, h3, sub_zero]`. Conclude with `⟨2, ⟨Nat.prime_two⟩, h2⟩`.
-/
theorem exists_prime_natCast_ne_zero (k : Type) [Field k] :
    ∃ (l : ℕ) (_ : Fact l.Prime), (l : k) ≠ 0 := by
  by_cases h2 : ((2 : ℕ) : k) = 0
  · refine ⟨3, ⟨Nat.prime_three⟩, fun h3 => one_ne_zero (α := k) ?_⟩
    have : ((3 : ℕ) : k) - ((2 : ℕ) : k) = 1 := by push_cast; ring
    rw [← this, h2, h3, sub_zero]
  · exact ⟨2, ⟨Nat.prime_two⟩, h2⟩

/- English proof (translation)
Introduce `R K Ω _ _ _ _ _ _ _ V A _ _ hb`. Take `⟨l, hl, hl0⟩` from `exists_prime_natCast_ne_zero (ResidueField R)`. Establish `hpow : ∀ n : ℕ, ((l ^ n : ℕ) : ResidueField R) ≠ 0` using `fun n => by`. Rewrite using `[Nat.cast_pow]`. Conclude with `pow_ne_zero _ hl0`.

Use `⟨⟨l, hl, hl0, tateUnramified_of_torsionUnramified fun n => hb _ (hpow n)⟩, ?_⟩` and prove the remaining obligations. Conclude with `Set.infinite_of_injective_forall_mem (f := fun n : ℕ => l ^ n) (Nat.pow_right_injective hl.out.two_le) fun n => ⟨hpow n, hb _ (hpow n)⟩`.
-/
theorem torsionUnramified_imp_tate_and_infinite :
    ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [Field Ω]
      [Algebra K Ω] (V : ValuationSubring Ω) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A],
      (∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m) →
      (∃ (l : ℕ) (_ : Fact l.Prime), (l : ResidueField R) ≠ 0 ∧ TateUnramified A V l) ∧
        {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  intro R K Ω _ _ _ _ _ _ _ V A _ _ hb
  obtain ⟨l, hl, hl0⟩ := exists_prime_natCast_ne_zero (ResidueField R)
  have hpow : ∀ n : ℕ, ((l ^ n : ℕ) : ResidueField R) ≠ 0 := fun n => by
    rw [Nat.cast_pow]; exact pow_ne_zero _ hl0
  refine ⟨⟨l, hl, hl0, tateUnramified_of_torsionUnramified fun n => hb _ (hpow n)⟩, ?_⟩
  exact Set.infinite_of_injective_forall_mem (f := fun n : ℕ => l ^ n)
    (Nat.pow_right_injective hl.out.two_le) fun n => ⟨hpow n, hb _ (hpow n)⟩

end GlobalTheory.Proof
