import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ci.Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type} [CommRing R]
  [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, 1, map_one _, map_one _⟩`.
-/
theorem one (h : genPt ξ ⤳ centre z) : ValAt ξ z 1 1 := ⟨h, 1, map_one _, map_one _⟩

/- English proof (translation)
Take `⟨h, u, rfl, rfl⟩` from `ha`. Take `⟨_, v, rfl, rfl⟩` from `hb`. Conclude with `⟨h, u * v, map_mul _ _ _, map_mul _ _ _⟩`.
-/
theorem mul {a b : Ω} {r s : R} (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, u, rfl, rfl⟩ := ha
  obtain ⟨_, v, rfl, rfl⟩ := hb
  exact ⟨h, u * v, map_mul _ _ _, map_mul _ _ _⟩

/- English proof (translation)
Take `⟨h, u, rfl, rfl⟩` from `ha`. Conclude with `⟨h, u ^ n, map_pow _ _ _, map_pow _ _ _⟩`.
-/
theorem pow {a : Ω} {r : R} (ha : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨h, u, rfl, rfl⟩ := ha
  exact ⟨h, u ^ n, map_pow _ _ _, map_pow _ _ _⟩

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, Finset.prod_empty]`. Conclude with `one h`. Consider the case `insert k T hk ih => rw [Finset.prod_insert hk, Finset.prod_insert hk]`. Conclude with `mul (ha k) ih`.
-/
theorem prod (h : genPt ξ ⤳ centre z) {ι : Type} (T : Finset ι) {a : ι → Ω} {r : ι → R}
    (ha : ∀ k, ValAt ξ z (a k) (r k)) : ValAt ξ z (∏ k ∈ T, a k) (∏ k ∈ T, r k) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact one h
  | insert k T hk ih => rw [Finset.prod_insert hk, Finset.prod_insert hk]; exact mul (ha k) ih

/- English proof (translation)
Take `⟨_, u, rfl, -⟩` from `ha`. Conclude with `⟨u, rfl⟩`.
-/
theorem mem {a : Ω} {r : R} (ha : ValAt ξ z a r) (h : genPt ξ ⤳ centre z) : a ∈ regAt ξ ⟨centre z, h⟩ := by
  obtain ⟨_, u, rfl, -⟩ := ha
  exact ⟨u, rfl⟩

/- English proof (translation)
Take `⟨u, rfl⟩` from `ha`. Conclude with `⟨_, h, u, rfl, rfl⟩`.
-/
theorem of_mem {a : Ω} {h : genPt ξ ⤳ centre z} (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r, ValAt ξ z a r := by
  obtain ⟨u, rfl⟩ := ha
  exact ⟨_, h, u, rfl, rfl⟩

/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat n => simpa using pow ha n`. Consider the case `negSucc n => simpa only [zpow_negSucc, inv_pow] using pow ha' (n + 1)`.
-/
theorem zpow {K : Type} [Field K] {z : Spec (CommRingCat.of K) ⟶ X} {a : Ω} {r : K} (ha : ValAt ξ z a r)
    (ha' : ValAt ξ z a⁻¹ r⁻¹) (n : ℤ) : ValAt ξ z (a ^ n) (r ^ n) := by
  cases n with
  | ofNat n => simpa using pow ha n
  | negSucc n => simpa only [zpow_negSucc, inv_pow] using pow ha' (n + 1)

end PositivityTheory.HtPt.Ci.Val
