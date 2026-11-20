import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.Mod

/- English proof (translation)
Introduce `A k _ _ _ r hr q hq`. Establish `hmax : (RingHom.ker r).IsMaximal` using `RingHom.ker_isMaximal_of_surjective r hr`. Establish `heq : RingHom.ker r = IsLocalRing.maximalIdeal A` using `IsLocalRing.eq_maximalIdeal hmax`. Assume the negation of the conclusion as `hn`. Establish `hmem : (q : A) ∈ IsLocalRing.maximalIdeal A` using `(IsLocalRing.mem_maximalIdeal _).2 hn`.

Rewrite `hmem` using `[← heq, RingHom.mem_ker, map_natCast]`. Conclude with `hq.ne_zero hmem`.
-/
theorem spUnit : ∀ (A k : Type) [CommRing A] [IsLocalRing A] [Field k] (r : A →+* k),
    Function.Surjective r → ∀ q : ℕ, IsUnit (q : k) → IsUnit (q : A) := by
  intro A k _ _ _ r hr q hq
  have hmax : (RingHom.ker r).IsMaximal := RingHom.ker_isMaximal_of_surjective r hr
  have heq : RingHom.ker r = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hmax
  by_contra hn
  have hmem : (q : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 hn
  rw [← heq, RingHom.mem_ker, map_natCast] at hmem
  exact hq.ne_zero hmem

end UpperTheory.Gal.Mod
