import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Introduce `R' A S _ _ _ _ _ _ χ₁ χ₂ g h`. Establish `key : ∀ x, ∃ n : ℕ, g ^ n * χ₁ x = g ^ n * χ₂ x`. Introduce `x`. Take `⟨⟨c, hc⟩, hcx⟩` from `(IsLocalization.eq_iff_exists (Submonoid.powers g) (Localization.Away g)).1 (h x)`. Take `⟨n, rfl⟩` from `Submonoid.mem_powers_iff _ _ |>.1 hc`.

Conclude with `⟨n, hcx⟩`. Use `choose n hn using key`. Take `⟨s, hs⟩` from `(Algebra.FiniteType.out : (⊤ : Subalgebra R' A).FG)`. Use `⟨∑ x ∈ s, n x, fun x => ?_⟩` and prove the remaining obligations. Use `set N := ∑ x ∈ s, n x`.

Establish `hx : x ∈ Algebra.adjoin R' (s : Set A)` using `by rw [hs]; exact Algebra.mem_top`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hxs`. Establish `hle : n x ≤ N` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) hxs`. Rewrite using `[← Nat.sub_add_cancel hle, pow_add, mul_assoc, mul_assoc, hn x]`.

Consider the case `algebraMap r => rw [AlgHom.commutes, AlgHom.commutes]`. Consider the case `add x y _ _ hx hy => rw [map_add, map_add, mul_add, mul_add, hx, hy]`. Consider the case `mul x y _ _ hx hy`. Rewrite using `[map_mul, map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem algHom_eq_mul_pow_of_eq_localizationAway :
    ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FiniteType R' A] (χ₁ χ₂ : A →ₐ[R'] S) (g : S),
    (∀ x, algebraMap S (Localization.Away g) (χ₁ x) = algebraMap S (Localization.Away g) (χ₂ x)) →
    ∃ N : ℕ, ∀ x, g ^ N * χ₁ x = g ^ N * χ₂ x := by
  intro R' A S _ _ _ _ _ _ χ₁ χ₂ g h
  have key : ∀ x, ∃ n : ℕ, g ^ n * χ₁ x = g ^ n * χ₂ x := by
    intro x
    obtain ⟨⟨c, hc⟩, hcx⟩ :=
      (IsLocalization.eq_iff_exists (Submonoid.powers g) (Localization.Away g)).1 (h x)
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hc
    exact ⟨n, hcx⟩
  choose n hn using key
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R' A).FG)
  refine ⟨∑ x ∈ s, n x, fun x => ?_⟩
  set N := ∑ x ∈ s, n x
  have hx : x ∈ Algebra.adjoin R' (s : Set A) := by rw [hs]; exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hxs =>
    have hle : n x ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hxs
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, mul_assoc, hn x]
  | algebraMap r => rw [AlgHom.commutes, AlgHom.commutes]
  | add x y _ _ hx hy => rw [map_add, map_add, mul_add, mul_add, hx, hy]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul]
    calc g ^ N * (χ₁ x * χ₁ y) = χ₁ x * (g ^ N * χ₁ y) := by ring
      _ = χ₁ x * (g ^ N * χ₂ y) := by rw [hy]
      _ = (g ^ N * χ₁ x) * χ₂ y := by ring
      _ = (g ^ N * χ₂ x) * χ₂ y := by rw [hx]
      _ = g ^ N * (χ₂ x * χ₂ y) := by ring

end GlobalTheory
