import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelSectionsLarge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ Ω _ y a n m g hy`. Establish `hN : IsNoetherianRing (Algebra.adjoin ℤ (Set.range g))` using `adjoin_isNoetherianRing g`. Take `⟨n₁, hn₁⟩` from `hL K ι Ω (Algebra.adjoin ℤ (Set.range g)) hN y hy`. Use `choose c0 hc0 using hy`. Use `set R := Algebra.adjoin ℤ (Set.range g)`.

Set `e : K → ℕ` to `fun k => n₁ + ((n : ℤ) * a k).natAbs`. Set `b : K → ℕ` to `fun k => ((n : ℤ) * a k + e k).toNat`. Establish `hb : ∀ k, ((b k : ℕ) : ℤ) = (n : ℤ) * a k + e k`. Introduce `k`. Use `Int.toNat_of_nonneg ?_` and prove the remaining obligations.

Simplify using `only [e]`. Use `push_cast`. Use `neg_abs_le ((n : ℤ) * a k)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hbn : ∀ k, n₁ ≤ b k`.

Introduce `k`. Establish `h1` using `hb k`. Simplify using `only [e] at h1`. Move the coercions through the operations in `at h1`. Use `neg_abs_le ((n : ℤ) * a k)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `set mon : Ω := ∏ k, y ⟨k, c0 k⟩ ^ e k`. Establish `hmon : mon ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc0 k)`. Set `φ : Ω →ₗ[R] Ω` to `LinearMap.mulRight R mon`. Establish `hφ : Function.Injective φ` using `mul_left_injective₀ hmon`.

Establish `hmap : (relChartLat R y a n).map φ ≤ relSecM R y b`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Conclude with `hn₁ b hbn (mul_prod_mem_relChartLat R y e c0 (fun k => hb k) hs)`. Establish `: IsNoetherian R (relSecM R y b)` using `isNoetherian_of_fg_of_noetherian _ (relSecM_fg R y b)`. Conclude with `Submodule.fg_of_fg_map_injective φ hφ (Submodule.FG.of_le_of_isNoetherian hmap)`.
-/
theorem RelLatticeFinite.proof (hL : RelSectionsLarge.Statement) : RelLatticeFinite.Statement := by
  intro K _ ι _ Ω _ y a n m g hy
  have hN : IsNoetherianRing (Algebra.adjoin ℤ (Set.range g)) := adjoin_isNoetherianRing g
  obtain ⟨n₁, hn₁⟩ := hL K ι Ω (Algebra.adjoin ℤ (Set.range g)) hN y hy
  choose c0 hc0 using hy
  set R := Algebra.adjoin ℤ (Set.range g)
  let e : K → ℕ := fun k => n₁ + ((n : ℤ) * a k).natAbs
  let b : K → ℕ := fun k => ((n : ℤ) * a k + e k).toNat
  have hb : ∀ k, ((b k : ℕ) : ℤ) = (n : ℤ) * a k + e k := by
    intro k
    refine Int.toNat_of_nonneg ?_
    simp only [e]
    push_cast
    have := neg_abs_le ((n : ℤ) * a k)
    omega
  have hbn : ∀ k, n₁ ≤ b k := by
    intro k
    have h1 := hb k
    simp only [e] at h1
    push_cast at h1
    have := neg_abs_le ((n : ℤ) * a k)
    omega
  set mon : Ω := ∏ k, y ⟨k, c0 k⟩ ^ e k
  have hmon : mon ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc0 k)
  let φ : Ω →ₗ[R] Ω := LinearMap.mulRight R mon
  have hφ : Function.Injective φ := mul_left_injective₀ hmon
  have hmap : (relChartLat R y a n).map φ ≤ relSecM R y b := by
    rintro _ ⟨s, hs, rfl⟩
    exact hn₁ b hbn (mul_prod_mem_relChartLat R y e c0 (fun k => hb k) hs)
  have : IsNoetherian R (relSecM R y b) := isNoetherian_of_fg_of_noetherian _ (relSecM_fg R y b)
  exact Submodule.fg_of_fg_map_injective φ hφ (Submodule.FG.of_le_of_isNoetherian hmap)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
