import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `R _ C _ F`. Establish `hw : ∀ {n n' : ℕ} (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F) (T : C), wsum F (Fin.append u u') (Fin.append v v') T = wsum F u v T + wsum F u' v' T`. Introduce `n n' u v u' v' T`. Simplify using `only [wsum, Fin.sum_univ_add, Fin.append_left, Fin.append_right]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `x x' n n' y w y' w' ⟨f, g, ω, hf, hg, he⟩ ⟨f', g', ω', hf', hg', he'⟩`. Use `⟨f + f', Fin.append g g', ω + ω', by rw [map_add, hf, hf'], ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Use `Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) k` and prove the remaining obligations. Simplify using `only [Fin.append_left]`.

Conclude with `hg i`. Simplify using `only [Fin.append_right]`. Conclude with `hg' i`. Introduce `T T' φ`. Establish `e1` using `he φ`.

Establish `e2` using `he' φ`. Simplify using `only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Submodule.coe_add, Pi.add_apply, map_add]`. Rewrite using `[e1, e2]`. Normalize the expressions using the abelian group laws. Introduce and unpack `x x' n n' u v u' v' ⟨f, ω, hf, hc, hd⟩ ⟨f', ω', hf', hc', hd'⟩`.

Use `⟨f + f', ω + ω', by rw [map_add, hf, hf'], ?_, ?_⟩` and prove the remaining obligations. Introduce `T T' φ`. Simplify using `only [Submodule.coe_add, Pi.add_apply, map_add]`. Rewrite using `[hc φ, hc' φ]`. Normalize the expressions using the abelian group laws.

Introduce `T`. Simplify using `only [Pi.add_apply, map_add, hw, hd T, hd' T]`. Introduce `w w' n n' u v u' v' h h' T`. Simplify using `only [Submodule.coe_add, Pi.add_apply, map_add, hw, h T, h' T]`.
-/
theorem GlobalTheory.AbCoh.rel_add : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), (∀ (x x' : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F) (y' : Fin n' → GlobalTheory.CatCoh.H1 F) (w' : Fin n' → Glob1 F), DRel F x y w → DRel F x' y' w' → DRel F (x + x') (Fin.append y y') (Fin.append w w')) ∧ (∀ (x x' : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F), ObRel F x u v → ObRel F x' u' v' → ObRel F (x + x') (Fin.append u u') (Fin.append v v')) ∧ ∀ (w w' : Glob1 F) (n n' : ℕ) (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F), ClRel F w u v → ClRel F w' u' v' → ClRel F (w + w') (Fin.append u u') (Fin.append v v') := by
  intro R _ C _ F
  have hw : ∀ {n n' : ℕ} (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F) (T : C),
      wsum F (Fin.append u u') (Fin.append v v') T = wsum F u v T + wsum F u' v' T := by
    intro n n' u v u' v' T
    simp only [wsum, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  refine ⟨?_, ?_, ?_⟩
  · rintro x x' n n' y w y' w' ⟨f, g, ω, hf, hg, he⟩ ⟨f', g', ω', hf', hg', he'⟩
    refine ⟨f + f', Fin.append g g', ω + ω', by rw [map_add, hf, hf'], ?_, ?_⟩
    · intro k
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) k
      · simp only [Fin.append_left]; exact hg i
      · simp only [Fin.append_right]; exact hg' i
    · intro T T' φ
      have e1 := he φ
      have e2 := he' φ
      simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Submodule.coe_add, Pi.add_apply, map_add]
      rw [e1, e2]; abel
  · rintro x x' n n' u v u' v' ⟨f, ω, hf, hc, hd⟩ ⟨f', ω', hf', hc', hd'⟩
    refine ⟨f + f', ω + ω', by rw [map_add, hf, hf'], ?_, ?_⟩
    · intro T T' φ
      simp only [Submodule.coe_add, Pi.add_apply, map_add]
      rw [hc φ, hc' φ]; abel
    · intro T
      simp only [Pi.add_apply, map_add, hw, hd T, hd' T]
  · intro w w' n n' u v u' v' h h' T
    simp only [Submodule.coe_add, Pi.add_apply, map_add, hw, h T, h' T]
