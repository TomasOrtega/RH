import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

/- English proof (translation)
Introduce `R _ A _ _ n hR b _ S _ u g hu hg D _ _ D' _ _ φ x y`. Take `⟨D1, _, _, ψ1, z1, h1, hz1⟩` from `hR D' (spOver φ ≫ x)`. Take `⟨E, _, _, ψ2, w, h2, hw⟩` from `hR D1 (spOver ψ1 ≫ spOver φ ≫ y)`. Establish `hψ : spOver (ψ2.comp ψ1) = spOver ψ2 ≫ spOver ψ1` using `(spOver_comp ψ1 ψ2).symm`. Establish `hz : (spOver ψ2 ≫ z1) ^ n = spOver (ψ2.comp ψ1) ≫ spOver φ ≫ x`.

Rewrite using `[← comp_pow, hz1, hψ, Category.assoc]`. Establish `hw' : w ^ n = spOver (ψ2.comp ψ1) ≫ spOver φ ≫ y` using `by rw [hw, hψ, Category.assoc]`. Establish `hmul : spOver φ ≫ (x * y) = (spOver φ ≫ x) * (spOver φ ≫ y)` using `comp_mul _ _ _`. Establish `hzw : ((spOver ψ2 ≫ z1) * w) ^ n = spOver (ψ2.comp ψ1) ≫ spOver φ ≫ (x * y)`. Rewrite using `[mul_pow, hz, hw', hmul, comp_mul]`.

Establish `hc : ∀ t : Pt A D, spOver (ψ2.comp ψ1) ≫ spOver φ ≫ t = spOver ((ψ2.comp ψ1).comp φ) ≫ t` using `fun t ↦ by`. Rewrite using `[← Category.assoc, spOver_comp]`. Establish `hinj : Function.Injective (ψ2.comp ψ1)` using `fun a c h ↦ h1.injective (h2.injective h)`. Apply `hinj` to reduce the goal to its premises. Establish `e1` using `hg D' (spOver φ ≫ x) (spOver φ ≫ y) E (ψ2.comp ψ1) _ _ hz hw'`.

Establish `e2` using `hg D x y E ((ψ2.comp ψ1).comp φ) _ _ (hz.trans (hc x)) (hw'.trans (hc y))`. Rewrite `e2` using `[AlgHom.comp_apply]`. Establish `e3` using `hu D D' φ (x * y) E (ψ2.comp ψ1) _ hzw`. Rewrite `e3` using `[hmul]`. Establish `e4` using `hu D D' φ x E (ψ2.comp ψ1) _ hz`.

Establish `e5` using `hu D D' φ y E (ψ2.comp ψ1) _ hw'`. Simplify using `only [map_sub]`. Take the linear combination `e1 - e2 - e3 + e4 + e5`.
-/
theorem isAdd_of_isSecDiff_isSecAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A, (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∀ (u : Fn1 A) (g : Fn2 A), IsSecDiff n S u → IsSecAdd n S g → IsAdd u g := by
  intro R _ A _ _ n hR b _ S _ u g hu hg D _ _ D' _ _ φ x y
  obtain ⟨D1, _, _, ψ1, z1, h1, hz1⟩ := hR D' (spOver φ ≫ x)
  obtain ⟨E, _, _, ψ2, w, h2, hw⟩ := hR D1 (spOver ψ1 ≫ spOver φ ≫ y)
  have hψ : spOver (ψ2.comp ψ1) = spOver ψ2 ≫ spOver ψ1 := (spOver_comp ψ1 ψ2).symm
  have hz : (spOver ψ2 ≫ z1) ^ n = spOver (ψ2.comp ψ1) ≫ spOver φ ≫ x := by
    rw [← comp_pow, hz1, hψ, Category.assoc]
  have hw' : w ^ n = spOver (ψ2.comp ψ1) ≫ spOver φ ≫ y := by rw [hw, hψ, Category.assoc]
  have hmul : spOver φ ≫ (x * y) = (spOver φ ≫ x) * (spOver φ ≫ y) := comp_mul _ _ _
  have hzw : ((spOver ψ2 ≫ z1) * w) ^ n = spOver (ψ2.comp ψ1) ≫ spOver φ ≫ (x * y) := by
    rw [mul_pow, hz, hw', hmul, comp_mul]
  have hc : ∀ t : Pt A D, spOver (ψ2.comp ψ1) ≫ spOver φ ≫ t = spOver ((ψ2.comp ψ1).comp φ) ≫ t := fun t ↦ by
    rw [← Category.assoc, spOver_comp]
  have hinj : Function.Injective (ψ2.comp ψ1) := fun a c h ↦ h1.injective (h2.injective h)
  apply hinj
  have e1 := hg D' (spOver φ ≫ x) (spOver φ ≫ y) E (ψ2.comp ψ1) _ _ hz hw'
  have e2 := hg D x y E ((ψ2.comp ψ1).comp φ) _ _ (hz.trans (hc x)) (hw'.trans (hc y))
  rw [AlgHom.comp_apply] at e2
  have e3 := hu D D' φ (x * y) E (ψ2.comp ψ1) _ hzw
  rw [hmul] at e3
  have e4 := hu D D' φ x E (ψ2.comp ψ1) _ hz
  have e5 := hu D D' φ y E (ψ2.comp ψ1) _ hw'
  simp only [map_sub]
  linear_combination e1 - e2 - e3 + e4 + e5

end GlobalTheory.PtExt
