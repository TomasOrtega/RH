import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfManyTorsionPointsCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupOfManyTorsionCharPStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `k _ _ G _ hG g hsm C hinf`. Take `⟨m, ⟨hm0, s, hs, hle⟩, hCm⟩` from `hinf.exists_gt C`. Establish `hm1 : 1 ≤ m` using `by omega`. Establish `hcard : 0 < s.card`. Break down `Nat.eq_zero_or_pos s.card with h | h` into its components or cases.

Rewrite `hle` using `[h, Nat.mul_zero]`. Establish `: 0 < m ^ (2 * g)` using `Nat.pow_pos hm1`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hlt : m ^ (2 * g) < m * s.card` using `lt_of_le_of_lt hle (Nat.mul_lt_mul_of_pos_right hCm hcard)`.

Take `⟨p, hp⟩` from `CharP.exists k`. Break down `CharP.char_is_prime_or_zero k p with hpp | hp0` into its components or cases. Use `haveI : Fact p.Prime := ⟨hpp⟩`. Conclude with `GlobalTheory.T.isProper_smoothConnGroup_of_many_torsion_charP k p G hG g hsm m hm0 s hs hlt`. Substitute `hp0 haveI : CharZero k := CharP.charP_to_charZero k` using the available equality.

Conclude with `GlobalTheory.T.isProper_of_many_torsion_points_charZero k G hG g hsm m s hs hlt`.
-/
theorem GlobalTheory.properOfInfinitelyManyLargeTorsionCounts :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G →
      ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ C : ℕ,
      {m : ℕ | (m : k) ≠ 0 ∧ ∃ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) ∧
        m ^ (2 * g) ≤ C * s.card}.Infinite → IsProper G.hom := by
  intro k _ _ G _ hG g hsm C hinf
  obtain ⟨m, ⟨hm0, s, hs, hle⟩, hCm⟩ := hinf.exists_gt C
  have hm1 : 1 ≤ m := by omega
  have hcard : 0 < s.card := by
    rcases Nat.eq_zero_or_pos s.card with h | h
    · rw [h, Nat.mul_zero] at hle
      have : 0 < m ^ (2 * g) := Nat.pow_pos hm1
      omega
    · exact h
  have hlt : m ^ (2 * g) < m * s.card :=
    lt_of_le_of_lt hle (Nat.mul_lt_mul_of_pos_right hCm hcard)
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | hp0
  · haveI : Fact p.Prime := ⟨hpp⟩
    exact GlobalTheory.T.isProper_smoothConnGroup_of_many_torsion_charP k p G hG g hsm m hm0 s hs hlt
  · subst hp0
    haveI : CharZero k := CharP.charP_to_charZero k
    exact GlobalTheory.T.isProper_of_many_torsion_points_charZero k G hG g hsm m s hs hlt
