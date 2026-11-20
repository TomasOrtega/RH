import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

/- English proof (translation)
Take `⟨hz, -⟩` from `val_spec hu`. Establish `hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0` using `fun k => (hw.2 k (c₀ k) (isUnit_iff_ne_zero.2 (h₀ k))).1`. Establish `hy₁ : ∀ k, y ⟨k, c₁ k⟩ ≠ 0` using `fun k => (hw.2 k (c₁ k) (isUnit_iff_ne_zero.2 (h₁ k))).1`. Establish `hr : ∀ k, ∃ r : ℂ, ValAt ξ z (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) r ∧ w ⟨k, c₀ k⟩ = r * w ⟨k, c₁ k⟩` using `fun k => (hw.2 k (c₁ k) (isUnit_iff_ne_zero.2 (h₁ k))).2 (c₀ k)`. Use `choose r hrv hrw using hr`.

Establish `hr0 : ∀ k, r k ≠ 0` using `fun k hk => h₀ k (by rw [hrw k, hk, zero_mul])`. Establish `hprod : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k) (∏ k ∈ s, r k ^ a k)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using val_one hz`.

Consider the case `insert k s hk ih`. Rewrite using `[Finset.prod_insert hk, Finset.prod_insert hk]`. Conclude with `val_mul (val_zpow (hr0 k) (hrv k) (a k)) ih`. Establish `hg₀ : (∏ k, y ⟨k, c₀ k⟩ ^ a k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₀ k)`. Establish `hg₁ : (∏ k, y ⟨k, c₁ k⟩ ^ a k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₁ k)`.

Establish `hΩ : τ / gen y a e₀ c₁ = (τ / gen y a e₀ c₀) * ∏ k, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k`. Establish `: ∏ k, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k = (∏ k, y ⟨k, c₀ k⟩ ^ a k) / ∏ k, y ⟨k, c₁ k⟩ ^ a k`. Rewrite using `[← Finset.prod_div_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => div_zpow _ _ _`. Rewrite using `[this]`.

Unfold `gen`. Clear the denominators using the available nonvanishing facts. Establish `hval : u' = u * ∏ k, r k ^ a k`. Establish `h` using `val_mul hu (hprod Finset.univ)`. Rewrite `h` using `[← hΩ]`.

Conclude with `val_unique hξ hu' h`. Establish `hw₀ : ∏ k, w ⟨k, c₀ k⟩ ^ a k = (∏ k, r k ^ a k) * ∏ k, w ⟨k, c₁ k⟩ ^ a k`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [hrw k, mul_zpow]`. Rewrite using `[hw₀, hval, _root_.mul_assoc]`.
-/
theorem gen_chart_change (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (a : K → ℤ) (e₀ τ : Ω) (c₀ c₁ : (k : K) → J k) (u u' : ℂ)
    (hξ : IsCptGen ξ) (he : e₀ ≠ 0) (hw : CoordsAt ξ y z w) (h₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0)
    (h₁ : ∀ k, w ⟨k, c₁ k⟩ ≠ 0) (hu : ValAt ξ z (τ / gen y a e₀ c₀) u)
    (hu' : ValAt ξ z (τ / gen y a e₀ c₁) u') :
    u * ∏ k, w ⟨k, c₀ k⟩ ^ a k = u' * ∏ k, w ⟨k, c₁ k⟩ ^ a k := by
  classical
  obtain ⟨hz, -⟩ := val_spec hu
  have hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (hw.2 k (c₀ k) (isUnit_iff_ne_zero.2 (h₀ k))).1
  have hy₁ : ∀ k, y ⟨k, c₁ k⟩ ≠ 0 := fun k => (hw.2 k (c₁ k) (isUnit_iff_ne_zero.2 (h₁ k))).1
  have hr : ∀ k, ∃ r : ℂ, ValAt ξ z (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) r ∧ w ⟨k, c₀ k⟩ = r * w ⟨k, c₁ k⟩ :=
    fun k => (hw.2 k (c₁ k) (isUnit_iff_ne_zero.2 (h₁ k))).2 (c₀ k)
  choose r hrv hrw using hr
  have hr0 : ∀ k, r k ≠ 0 := fun k hk => h₀ k (by rw [hrw k, hk, zero_mul])
  have hprod : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k) (∏ k ∈ s, r k ^ a k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using val_one hz
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact val_mul (val_zpow (hr0 k) (hrv k) (a k)) ih
  have hg₀ : (∏ k, y ⟨k, c₀ k⟩ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₀ k)
  have hg₁ : (∏ k, y ⟨k, c₁ k⟩ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₁ k)
  have hΩ : τ / gen y a e₀ c₁ = (τ / gen y a e₀ c₀) * ∏ k, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k := by
    have : ∏ k, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k = (∏ k, y ⟨k, c₀ k⟩ ^ a k) / ∏ k, y ⟨k, c₁ k⟩ ^ a k := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun k _ => div_zpow _ _ _
    rw [this]
    unfold gen
    field_simp
  have hval : u' = u * ∏ k, r k ^ a k := by
    have h := val_mul hu (hprod Finset.univ)
    rw [← hΩ] at h
    exact val_unique hξ hu' h
  have hw₀ : ∏ k, w ⟨k, c₀ k⟩ ^ a k = (∏ k, r k ^ a k) * ∏ k, w ⟨k, c₁ k⟩ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [hrw k, mul_zpow]
  rw [hw₀, hval, _root_.mul_assoc]

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
