import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt

open GlobalTheory.LatHecke

namespace GlobalTheory.LatHecke

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _ r`. Use `⟨fun L => ?_, fun g L => glMap_isLattice g L⟩` and prove the remaining obligations. Use `haveI := L.2`. Use `haveI : Module.Free O L.1 := Submodule.IsLattice.free K L.1`. Use `haveI : Module.Finite O L.1 := Module.Finite.iff_fg.2 L.2.fg`.

Establish `hr : Module.finrank O L.1 = r`. Simplify using `using Submodule.IsLattice.finrank_of_pi K L.1`. Set `b : Module.Basis (Fin r) O L.1` to `Module.finBasisOfFinrankEq O L.1 hr`. Set `c : Module.Basis (Fin r) K (Fin r → K)` to `b.extendOfIsLattice K`. Establish `hc : ∀ i, c i = (b i : Fin r → K)` using `fun i => Module.Basis.extendOfIsLattice_apply K b i`.

Set `e : (Fin r → K) ≃ₗ[K] (Fin r → K)` to `(Pi.basisFun K (Fin r)).equiv c (Equiv.refl _)`. Establish `he : ∀ i, e (Pi.basisFun K (Fin r) i) = c i` using `fun i => by`. Simplify using `using (Pi.basisFun K (Fin r)).equiv_apply i c (Equiv.refl _)`. Set `g : GL (Fin r) K` to `⟨LinearMap.toMatrix' (e : (Fin r → K) →ₗ[K] (Fin r → K)), LinearMap.toMatrix' (e.symm : (Fin r → K) →ₗ[K] (Fin r → K)), by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩`. Establish `hg : Matrix.toLin' (g : Matrix (Fin r) (Fin r) K) = (e : (Fin r → K) →ₗ[K] (Fin r → K))` using `Matrix.toLin'_toMatrix' _`.

Use `⟨g, ?_⟩` and prove the remaining obligations. Establish `h1 : Set.range (Subtype.val ∘ b) = L.1.subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map ((Matrix.toLin' (g : Matrix (Fin r) (Fin r) K)).restrictScalars O) = L.1`.

Rewrite using `[hg, Submodule.map_span, ← Set.range_comp]`. Establish `h2 : ((e : (Fin r → K) →ₗ[K] (Fin r → K)).restrictScalars O) ∘ (Pi.basisFun K (Fin r)) = Subtype.val ∘ b`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]`. Rewrite using `[he, hc]`.

Rewrite using `[h2, h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]`.
-/
theorem gl_transitive_lattices : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ), (∀ L : Lat O K r, ∃ g : GL (Fin r) K, glMap g (std O K r).1 = L.1) ∧ ∀ (g : GL (Fin r) K) (L : Lat O K r), (glMap g L.1).IsLattice K := by
  intro O K _ _ _ _ _ _ _ r
  refine ⟨fun L => ?_, fun g L => glMap_isLattice g L⟩
  haveI := L.2
  haveI : Module.Free O L.1 := Submodule.IsLattice.free K L.1
  haveI : Module.Finite O L.1 := Module.Finite.iff_fg.2 L.2.fg
  have hr : Module.finrank O L.1 = r := by
    simpa using Submodule.IsLattice.finrank_of_pi K L.1
  let b : Module.Basis (Fin r) O L.1 := Module.finBasisOfFinrankEq O L.1 hr
  let c : Module.Basis (Fin r) K (Fin r → K) := b.extendOfIsLattice K
  have hc : ∀ i, c i = (b i : Fin r → K) := fun i => Module.Basis.extendOfIsLattice_apply K b i
  let e : (Fin r → K) ≃ₗ[K] (Fin r → K) := (Pi.basisFun K (Fin r)).equiv c (Equiv.refl _)
  have he : ∀ i, e (Pi.basisFun K (Fin r) i) = c i := fun i => by
    simpa using (Pi.basisFun K (Fin r)).equiv_apply i c (Equiv.refl _)
  let g : GL (Fin r) K :=
    ⟨LinearMap.toMatrix' (e : (Fin r → K) →ₗ[K] (Fin r → K)),
      LinearMap.toMatrix' (e.symm : (Fin r → K) →ₗ[K] (Fin r → K)),
      by rw [← LinearMap.toMatrix'_comp]; simp,
      by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hg : Matrix.toLin' (g : Matrix (Fin r) (Fin r) K) = (e : (Fin r → K) →ₗ[K] (Fin r → K)) :=
    Matrix.toLin'_toMatrix' _
  refine ⟨g, ?_⟩
  have h1 : Set.range (Subtype.val ∘ b) = L.1.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  change (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
    ((Matrix.toLin' (g : Matrix (Fin r) (Fin r) K)).restrictScalars O) = L.1
  rw [hg, Submodule.map_span, ← Set.range_comp]
  have h2 : ((e : (Fin r → K) →ₗ[K] (Fin r → K)).restrictScalars O) ∘ (Pi.basisFun K (Fin r))
      = Subtype.val ∘ b := by
    funext i
    simp only [Function.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [he, hc]
  rw [h2, h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.LatHecke
