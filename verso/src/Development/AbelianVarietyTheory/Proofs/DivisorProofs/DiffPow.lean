import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.CUniq

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `fun h => hx (isUnit_of_map_unit θ x h)`.
-/
theorem map_max {R V : Type} [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] (θ : R →+* V) [IsLocalHom θ]
    {x : R} (hx : x ∈ maximalIdeal R) : θ x ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  exact fun h => hx (isUnit_of_map_unit θ x h)

/- English proof (translation)
Establish `hc : ∀ a, θ₁ (ψ a) = θ₂ (ψ a)` using `fun a => congrArg (fun f => f a) h`. Proceed by induction on `k with`. Consider the case `zero => intro r`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Establish `hm : ∀ x ∈ maximalIdeal R, θ₁ x - θ₂ x ∈ maximalIdeal V ^ (k + 1)`. Introduce `x hx`. Rewrite `hx` using `[← hψ.2.2.2.1]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨p, -, rfl⟩` from `hy`. Simplify using `[hc]`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz`. Use `add_mem hy hz` as an intermediate fact.

Simplify `this` using `[map_add, sub_add_sub_comm]`. Consider the case `smul a y hy' hy`. Establish `hyM : y ∈ maximalIdeal R` using `hψ.2.2.2.1 ▸ hy'`. Establish `e : θ₁ (a • y) - θ₂ (a • y) = θ₁ a * (θ₁ y - θ₂ y) + (θ₁ a - θ₂ a) * θ₂ y`. Simplify using `only [smul_eq_mul, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `add_mem (Ideal.mul_mem_left _ _ hy) ?_` and prove the remaining obligations. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul (ih a) (map_max θ₂ hyM)`.

Introduce `r`. Take `⟨a, b, hb, hx⟩` from `hψ.2.2.2.2 r`. Establish `e` using `hm _ hx`. Establish `hu : IsUnit (θ₁ (ψ b))` using `hb.map θ₁`. Establish `e2 : θ₁ (r * ψ b - ψ a) - θ₂ (r * ψ b - ψ a) = (θ₁ r - θ₂ r) * θ₁ (ψ b)`.

Simplify using `only [map_sub, map_mul, hc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `e` using `[e2]`. Take `⟨u, hu'⟩` from `hu`. Establish `: θ₁ r - θ₂ r = (θ₁ r - θ₂ r) * θ₁ (ψ b) * ↑u⁻¹`.

Rewrite using `[← hu', _root_.mul_assoc, Units.mul_inv, _root_.mul_one]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ e`.
-/
theorem diff_pow {A R V : Type} [CommRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V]
    (ψ : A →+* R) (hψ : IsComplAt ψ) (θ₁ θ₂ : R →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂]
    (h : θ₁.comp ψ = θ₂.comp ψ) (k : ℕ) : ∀ r : R, θ₁ r - θ₂ r ∈ maximalIdeal V ^ k := by
  have hc : ∀ a, θ₁ (ψ a) = θ₂ (ψ a) := fun a => congrArg (fun f => f a) h
  induction k with
  | zero => intro r; simp
  | succ k ih =>
    have hm : ∀ x ∈ maximalIdeal R, θ₁ x - θ₂ x ∈ maximalIdeal V ^ (k + 1) := by
      intro x hx
      rw [← hψ.2.2.2.1] at hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨p, -, rfl⟩ := hy
        simp [hc]
      | zero => simp
      | add y z _ _ hy hz =>
        have := add_mem hy hz
        simpa [map_add, sub_add_sub_comm] using this
      | smul a y hy' hy =>
        have hyM : y ∈ maximalIdeal R := hψ.2.2.2.1 ▸ hy'
        have e : θ₁ (a • y) - θ₂ (a • y) = θ₁ a * (θ₁ y - θ₂ y) + (θ₁ a - θ₂ a) * θ₂ y := by
          simp only [smul_eq_mul, map_mul]; ring
        rw [e]
        refine add_mem (Ideal.mul_mem_left _ _ hy) ?_
        rw [pow_succ]
        exact Ideal.mul_mem_mul (ih a) (map_max θ₂ hyM)
    intro r
    obtain ⟨a, b, hb, hx⟩ := hψ.2.2.2.2 r
    have e := hm _ hx
    have hu : IsUnit (θ₁ (ψ b)) := hb.map θ₁
    have e2 : θ₁ (r * ψ b - ψ a) - θ₂ (r * ψ b - ψ a) = (θ₁ r - θ₂ r) * θ₁ (ψ b) := by
      simp only [map_sub, map_mul, hc]; ring
    rw [e2] at e
    obtain ⟨u, hu'⟩ := hu
    have : θ₁ r - θ₂ r = (θ₁ r - θ₂ r) * θ₁ (ψ b) * ↑u⁻¹ := by
      rw [← hu', _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ e

end GlobalTheory.TChart.CUniq

/- English proof (translation)
Introduce `A R V _ _ _ _ _ _ ψ hψ θ₁ θ₂ h₁ h₂ h`. Use extensionality with `r`. Establish `hk` using `fun k => GlobalTheory.TChart.CUniq.diff_pow ψ hψ θ₁ θ₂ h k r`. Establish `hbot` using `Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V) (maximalIdeal.isMaximal V).ne_top`. Establish `: θ₁ r - θ₂ r ∈ ⨅ k : ℕ, maximalIdeal V ^ k` using `Ideal.mem_iInf.mpr hk`.

Rewrite `this` using `[hbot, Ideal.mem_bot, sub_eq_zero]`. Conclude with `this`.
-/
theorem GlobalTheory.TChart.cuniq : ∀ (A R V : Type) [CommRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (ψ : A →+* R), IsComplAt ψ → ∀ θ₁ θ₂ : R →+* V, IsLocalHom θ₁ → IsLocalHom θ₂ → θ₁.comp ψ = θ₂.comp ψ → θ₁ = θ₂ := by
  intro A R V _ _ _ _ _ _ ψ hψ θ₁ θ₂ h₁ h₂ h
  ext r
  have hk := fun k => GlobalTheory.TChart.CUniq.diff_pow ψ hψ θ₁ θ₂ h k r
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V) (maximalIdeal.isMaximal V).ne_top
  have : θ₁ r - θ₂ r ∈ ⨅ k : ℕ, maximalIdeal V ^ k := Ideal.mem_iInf.mpr hk
  rw [hbot, Ideal.mem_bot, sub_eq_zero] at this
  exact this
