import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

/- English proof (translation)
Take `⟨⟨n, hn, ho⟩, ht, hl, hr⟩` from `h`. Take `⟨⟨n', hn', ho'⟩, ht', hl', hr'⟩` from `h'`. Use `⟨⟨n * n', Nat.mul_pos hn hn', ?_⟩, ht.mul ht', fun v => HChar.LevelLe.mul (hl v) (hl' v), fun v hv => ?_⟩` and prove the remaining obligations. Unfold `HChar.OrderDvd at *`. Rewrite using `[mul_pow, pow_mul, ho, one_pow, one_mul, mul_comm n n', pow_mul, ho', one_pow]`.

Distinguish the cases in `h1 : ξ.UnrAt v`. Conclude with `hr' v fun h2 => hv (h1.mul h2)`. Conclude with `hr v h1`.
-/
theorem IsTwist.mul_twist {S : Set ℕ} {ξ ξ' : HChar H.E} (h : IsTwist H S ξ) (h' : IsTwist H S ξ') :
    IsTwist H S (ξ * ξ') := by
  obtain ⟨⟨n, hn, ho⟩, ht, hl, hr⟩ := h
  obtain ⟨⟨n', hn', ho'⟩, ht', hl', hr'⟩ := h'
  refine ⟨⟨n * n', Nat.mul_pos hn hn', ?_⟩, ht.mul ht', fun v => HChar.LevelLe.mul (hl v) (hl' v), fun v hv => ?_⟩
  · unfold HChar.OrderDvd at *
    rw [mul_pow, pow_mul, ho, one_pow, one_mul, mul_comm n n', pow_mul, ho', one_pow]
  · by_cases h1 : ξ.UnrAt v
    · exact hr' v fun h2 => hv (h1.mul h2)
    · exact hr v h1

/- English proof (translation)
Use `⟨h.fin, h.triv, h.tame, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hv' : OverP H p v`. Assume the negation of the conclusion as `hn`. Conclude with `hv (h.unr v hn)`. Take `⟨h1, h2, h3, -⟩` from `splitsC_main R H p hp hs v hv'`.

Rewrite using `[h1]`. Conclude with `⟨h3, hp, h2, hS⟩`.
-/
theorem isTwist_of_isDelta {S : Set ℕ} {p : ℕ} {δ : HChar H.E} (hp : p.Prime) (hs : SplitsC H.E p) (hS : p ∉ S)
    (h : IsDelta (H := H) p δ) : IsTwist H S δ := by
  refine ⟨h.fin, h.triv, h.tame, fun v hv => ?_⟩
  have hv' : OverP H p v := by
    by_contra hn
    exact hv (h.unr v hn)
  obtain ⟨h1, h2, h3, -⟩ := splitsC_main R H p hp hs v hv'
  rw [h1]
  exact ⟨h3, hp, h2, hS⟩

end GlobalTheory.Mem.Chr
