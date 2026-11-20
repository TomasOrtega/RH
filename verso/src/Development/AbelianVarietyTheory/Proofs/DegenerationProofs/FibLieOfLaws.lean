import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch

open GlobalTheory.PointUnif GlobalTheory.EigenSplit in

/- English proof (translation)
Introduce `_ R _ _ _ D J g Λ Hm χ ex fr hfib O _ act F hF τ n hn`. Take `⟨-, P', φ, w, u, -, hφ, -, -, h1, h2, -, hex, -⟩` from `hfib`. Take `⟨Φ, hΦ⟩` from `GlobalTheory.LiePull.exists_pushEquiv hφ (𝟙_ _) (TF (R := R) ℂ).hom (Category.id_comp _).symm`. Establish `he` using `isExp_push hφ u h1 h2 Φ hΦ`. Establish `hx : ∀ z, Φ (u.ex z) = ex z` using `fun z => Over.OverMorphism.ext ((hΦ _).trans (hex z).symm)`.

Establish `hker : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ` using `fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)`. Establish `hF' : ∀ a z, Φ (u.ex (F a z)) = Φ (u.ex z) ≫ act.act a` using `fun a z => by`. Rewrite using `[hx, hx]`. Conclude with `hF a z`. Take `⟨ρ, hρ⟩` from `he.exists_rep act u.Λ u.discrete hker fun a => ⟨F a, hF' a⟩`.

Establish `hρF : ∀ a, ρ a = F a` using `fun a => by`. Use `sub_eq_zero.1 (linear_eq_zero_of_discrete u.Λ u.discrete _ fun z => (hker _).1 ?_)` and prove the remaining obligations. Use `he.1 ((ρ a - F a) z) (F a z)` as an intermediate fact. Simplify using `only [LinearMap.sub_apply, sub_add_cancel] at this`. Rewrite `this` using `[hρ, ← hF']`.

Conclude with `mul_eq_right.1 this.symm`. Establish `hy : (TF (R` using `R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R _)) := (Spec.map_comp _ _).symm`. Rewrite `hn` using `[← hy]`. Establish `hE : (⨅ a, (F a).eigenspace (τ a) : Submodule ℂ (Fin g → ℂ)) = eigenSub ρ τ`. Use extensionality with `z`.

Simplify using `only [mem_eigenSub, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, hρF]`. Rewrite using `[hE]`. Conclude with `he.finrank_eigenSub act ρ hρ hn`.
-/
theorem fibLie_of_laws : Laws → FibLieSt := by
  intro _ R _ _ _ D J g Λ Hm χ ex fr hfib O _ act F hF τ n hn
  obtain ⟨-, P', φ, w, u, -, hφ, -, -, h1, h2, -, hex, -⟩ := hfib
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hφ (𝟙_ _) (TF (R := R) ℂ).hom (Category.id_comp _).symm
  have he := isExp_push hφ u h1 h2 Φ hΦ
  have hx : ∀ z, Φ (u.ex z) = ex z := fun z => Over.OverMorphism.ext ((hΦ _).trans (hex z).symm)
  have hker : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ := fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)
  have hF' : ∀ a z, Φ (u.ex (F a z)) = Φ (u.ex z) ≫ act.act a := fun a z => by
    rw [hx, hx]; exact hF a z
  obtain ⟨ρ, hρ⟩ := he.exists_rep act u.Λ u.discrete hker fun a => ⟨F a, hF' a⟩
  have hρF : ∀ a, ρ a = F a := fun a => by
    refine sub_eq_zero.1 (linear_eq_zero_of_discrete u.Λ u.discrete _ fun z => (hker _).1 ?_)
    have := he.1 ((ρ a - F a) z) (F a z)
    simp only [LinearMap.sub_apply, sub_add_cancel] at this
    rw [hρ, ← hF'] at this
    exact mul_eq_right.1 this.symm
  have hy : (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R _)) :=
    (Spec.map_comp _ _).symm
  rw [← hy] at hn
  have hE : (⨅ a, (F a).eigenspace (τ a) : Submodule ℂ (Fin g → ℂ)) = eigenSub ρ τ := by
    ext z
    simp only [mem_eigenSub, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, hρF]
  rw [hE]
  exact he.finrank_eigenSub act ρ hρ hn

end GlobalTheory.Ex.Arch
end
