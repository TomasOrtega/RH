import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

/- English proof (translation)
Introduce `R _ C _ F`. Use `⟨fun hcl x n n' u v u' v' ⟨f, ω, hf, hω, hd⟩ ⟨f', ω', hf', hω', hd'⟩ ↦ ?_, fun x n u v ⟨f, ω, hf, hω, hd⟩ h0 ↦ ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `H1.mk_eq_mk.1 (hf.trans hf'.symm)`. Set `e0 : Glob1 F` to `⟨fun T ↦ ω T - ω' T - D R _ (b T), fun T T' φ ↦ by`. Establish `hb' : f.1 T T' φ - f'.1 T T' φ = b T' - mp F φ (b T)` using `(congrFun (congrFun (congrFun hb T) T') φ).symm`.

Establish `h2 : D R _ (b T') = D R _ (f.1 T T' φ) - D R _ (f'.1 T T' φ) + D R _ (mp F φ (b T))`. Rewrite using `[← map_sub, hb', map_sub]`. Normalize the expressions using the abelian group laws. Use `show ω T' - ω' T' - D R _ (b T') = p1 F φ (ω T - ω' T - D R _ (b T))`. Rewrite using `[hω φ, hω' φ, map_sub, map_sub, p1_D, h2]`.

Use the proof step `abel⟩`. Establish `he0 : e0 ∈ Closed1 F` using `by rw [hcl]; exact Submodule.mem_top`. Use function extensionality and compare the values at `T`. Rewrite using `[← hd T, ← hd' T]`. Establish `h` using `he0 T`.

Express the relevant statement in the definitionally equal form `dOne R _ (ω T - ω' T - D R _ (b T)) = 0 at h`. Rewrite `h` using `[map_sub, map_sub, dOne_D, sub_zero, sub_eq_zero]`. Conclude with `h`. Use `⟨Hyp1.mk F ⟨(f.1, ω), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨f.2, hω, fun T ↦ (hd T).trans (congrFun h0 T)⟩⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[toO_mk]`.

Conclude with `hf`.
-/
theorem curvature_wellDefined_and_lift : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), (Closed1 F = ⊤ → ∀ (x : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F), ObRel F x u v → ObRel F x u' v' → wsum F u v = wsum F u' v') ∧ ∀ (x : GlobalTheory.CatCoh.H1 F) (n : ℕ) (u v : Fin n → Glob1 F), ObRel F x u v → wsum F u v = 0 → ∃ c, toO F c = x := by
  intro R _ C _ F
  refine ⟨fun hcl x n n' u v u' v' ⟨f, ω, hf, hω, hd⟩ ⟨f', ω', hf', hω', hd'⟩ ↦ ?_,
    fun x n u v ⟨f, ω, hf, hω, hd⟩ h0 ↦ ?_⟩
  · obtain ⟨b, hb⟩ := H1.mk_eq_mk.1 (hf.trans hf'.symm)
    let e0 : Glob1 F := ⟨fun T ↦ ω T - ω' T - D R _ (b T), fun T T' φ ↦ by
      have hb' : f.1 T T' φ - f'.1 T T' φ = b T' - mp F φ (b T) :=
        (congrFun (congrFun (congrFun hb T) T') φ).symm
      have h2 : D R _ (b T') = D R _ (f.1 T T' φ) - D R _ (f'.1 T T' φ) + D R _ (mp F φ (b T)) := by
        rw [← map_sub, hb', map_sub]; abel
      show ω T' - ω' T' - D R _ (b T') = p1 F φ (ω T - ω' T - D R _ (b T))
      rw [hω φ, hω' φ, map_sub, map_sub, p1_D, h2]
      abel⟩
    have he0 : e0 ∈ Closed1 F := by rw [hcl]; exact Submodule.mem_top
    funext T
    rw [← hd T, ← hd' T]
    have h := he0 T
    change dOne R _ (ω T - ω' T - D R _ (b T)) = 0 at h
    rw [map_sub, map_sub, dOne_D, sub_zero, sub_eq_zero] at h
    exact h
  · refine ⟨Hyp1.mk F ⟨(f.1, ω), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨f.2, hω, fun T ↦ (hd T).trans (congrFun h0 T)⟩⟩, ?_⟩
    rw [toO_mk]
    exact hf

end GlobalTheory.AbCoh
