import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlanePropertiesStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const Complex.continuous_im`.
-/
theorem isOpen_Hs_mobt : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

/- English proof (translation)
Introduce `g`. Take `⟨hmaps, hmul, hone, -, hdiff, -⟩` from `GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties`. Establish `hinj : ∀ x y : ℂ, x ∈ Hs → y ∈ Hs → mob g x = mob g y → x = y`. Introduce `x y hx hy hxy`. Establish `ex : mob (g⁻¹ * g) x = x` using `by rw [inv_mul_cancel, hone]`.

Establish `ey : mob (g⁻¹ * g) y = y` using `by rw [inv_mul_cancel, hone]`. Rewrite using `[← ex, ← ey, hmul _ _ _ hx, hmul _ _ _ hy, hxy]`. Introduce `S hS`. Rewrite using `[Filter.mem_map, mem_codiscreteWithin]`. Rewrite `hS` using `[mem_codiscreteWithin]`.

Introduce `z hz`. Establish `hw` using `hS (mob g z) (hmaps g z hz)`. Establish `hHs : Hs ∈ nhds z` using `isOpen_Hs_mobt.mem_nhds hz`. Establish `hcont : ContinuousAt (mob g) z` using `(hdiff g).continuousOn.continuousAt hHs`. Establish `htend : Filter.Tendsto (mob g) (nhdsWithin z {z}ᶜ) (nhdsWithin (mob g z) {mob g z}ᶜ)`.

Rewrite using `[tendsto_nhdsWithin_iff]`. Use `⟨hcont.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩` and prove the remaining obligations. Use `filter_upwards [nhdsWithin_le_nhds hHs, self_mem_nhdsWithin] with x hx hxz`. Conclude with `fun h => hxz (hinj x z hx hz h)`. Rewrite `hw`, the goal using `[Filter.disjoint_principal_right]`.

Use `filter_upwards [htend hw, nhdsWithin_le_nhds hHs] with x hx hxH`. Introduce and unpack `⟨hx1, hx2⟩`. Conclude with `hx ⟨hmaps g x hx1, hx2⟩`.
-/
theorem tendsto_mob_codiscreteWithin :
    ∀ g : GQ, Filter.Tendsto (mob g) (Filter.codiscreteWithin Hs) (Filter.codiscreteWithin Hs) := by
  intro g
  obtain ⟨hmaps, hmul, hone, -, hdiff, -⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  have hinj : ∀ x y : ℂ, x ∈ Hs → y ∈ Hs → mob g x = mob g y → x = y := by
    intro x y hx hy hxy
    have ex : mob (g⁻¹ * g) x = x := by rw [inv_mul_cancel, hone]
    have ey : mob (g⁻¹ * g) y = y := by rw [inv_mul_cancel, hone]
    rw [← ex, ← ey, hmul _ _ _ hx, hmul _ _ _ hy, hxy]
  intro S hS
  rw [Filter.mem_map, mem_codiscreteWithin]
  rw [mem_codiscreteWithin] at hS
  intro z hz
  have hw := hS (mob g z) (hmaps g z hz)
  have hHs : Hs ∈ nhds z := isOpen_Hs_mobt.mem_nhds hz
  have hcont : ContinuousAt (mob g) z := (hdiff g).continuousOn.continuousAt hHs
  have htend : Filter.Tendsto (mob g) (nhdsWithin z {z}ᶜ) (nhdsWithin (mob g z) {mob g z}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hHs, self_mem_nhdsWithin] with x hx hxz
    exact fun h => hxz (hinj x z hx hz h)
  rw [Filter.disjoint_principal_right] at hw ⊢
  filter_upwards [htend hw, nhdsWithin_le_nhds hHs] with x hx hxH
  rintro ⟨hx1, hx2⟩
  exact hx ⟨hmaps g x hx1, hx2⟩

end GlobalTheory.FN
