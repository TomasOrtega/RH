import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
  (I : X.IdealSheafData) (m : ℕ)

/- English proof (translation)
Break down `Nat.eq_zero_or_pos m with rfl | hpos` into its components or cases. Use `right`. Simplify using the standard rewrite rules. Establish `hm1 : 1 ≤ m` using `hpos`. Distinguish the cases in `h0 : orderAt I x = 0`.

Conclude with `Or.inl h0`. Use `right`. Establish `hlt : m - 1 < m` using `by omega`. Establish `hle : derivIdealSheafIterate k p (m - 1) I ^ m ≤ I ^ (m - (m - 1))` using `IsDerivBalanced.derivIdealSheafIterate_pow_le k p h hlt`. Establish `hsub : m - (m - 1) = 1` using `by omega`.

Rewrite `hle` using `[hsub, pow_one]`. Establish `hord : orderAt I x ≤ orderAt (derivIdealSheafIterate k p (m - 1) I ^ m) x` using `orderAt_le_of_le hle x`. Rewrite `hord` using `[orderAt_pow k p (derivIdealSheafIterate k p (m - 1) I) m x]`. Establish `hne : orderAt (derivIdealSheafIterate k p (m - 1) I) x ≠ 0`. Introduce `hz`.

Rewrite `hord` using `[hz, mul_zero]`. Conclude with `h0 (le_antisymm hord (by exact zero_le))`. Establish `hmem : x ∈ (derivIdealSheafIterate k p (m - 1) I).support`. Assume the negation of the conclusion as `hc`. Conclude with `hne ((orderAt_eq_zero_iff_not_mem_support _ x).mpr hc)`.

Establish `heq` using `support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm1`. Establish `hx : x ∈ orderAtLeastLocus I m`. Rewrite using `[← heq]`. Conclude with `hmem`. Conclude with `(mem_orderAtLeastLocus_iff I m x).mp hx`.
-/
theorem orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced
    (h : IsDerivBalanced k p I m) (x : X) :
    orderAt I x = 0 ∨ (m : ℕ∞) ≤ orderAt I x := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · right
    simp
  have hm1 : 1 ≤ m := hpos
  by_cases h0 : orderAt I x = 0
  · exact Or.inl h0
  right
  have hlt : m - 1 < m := by omega
  have hle : derivIdealSheafIterate k p (m - 1) I ^ m ≤ I ^ (m - (m - 1)) :=
    IsDerivBalanced.derivIdealSheafIterate_pow_le k p h hlt
  have hsub : m - (m - 1) = 1 := by omega
  rw [hsub, pow_one] at hle
  have hord : orderAt I x ≤ orderAt (derivIdealSheafIterate k p (m - 1) I ^ m) x :=
    orderAt_le_of_le hle x
  rw [orderAt_pow k p (derivIdealSheafIterate k p (m - 1) I) m x] at hord
  have hne : orderAt (derivIdealSheafIterate k p (m - 1) I) x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hord
    exact h0 (le_antisymm hord (by exact zero_le))
  have hmem : x ∈ (derivIdealSheafIterate k p (m - 1) I).support := by
    by_contra hc
    exact hne ((orderAt_eq_zero_iff_not_mem_support _ x).mpr hc)
  have heq := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm1
  have hx : x ∈ orderAtLeastLocus I m := by
    rw [← heq]
    exact hmem
  exact (mem_orderAtLeastLocus_iff I m x).mp hx

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_orderAtLeastLocus_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `h1 : (1 : ℕ∞) ≤ orderAt I x` using `le_trans (by exact_mod_cast hm) hx`.

Conclude with `(one_le_orderAt_iff_mem_support I x).mp h1`. Introduce `hx`. Establish `hx' : x ∈ I.support` using `hx`. Establish `hne : orderAt I x ≠ 0` using `fun h0 => (orderAt_eq_zero_iff_not_mem_support I x).mp h0 hx'`. Break down `orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced k p I m h x with h0 | h0` into its components or cases.

Conclude with `absurd h0 hne`. Conclude with `h0`.
-/
theorem orderAtLeastLocus_eq_support_of_isDerivBalanced
    (h : IsDerivBalanced k p I m) (hm : 1 ≤ m) :
    orderAtLeastLocus I m = (I.support : Set X) := by
  ext x
  rw [mem_orderAtLeastLocus_iff]
  constructor
  · intro hx
    have h1 : (1 : ℕ∞) ≤ orderAt I x := le_trans (by exact_mod_cast hm) hx
    exact (one_le_orderAt_iff_mem_support I x).mp h1
  · intro hx
    have hx' : x ∈ I.support := hx
    have hne : orderAt I x ≠ 0 := fun h0 =>
      (orderAt_eq_zero_iff_not_mem_support I x).mp h0 hx'
    rcases orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced k p I m h x with h0 | h0
    · exact absurd h0 hne
    · exact h0

end FunctorialResolution.EmbeddedResolution
