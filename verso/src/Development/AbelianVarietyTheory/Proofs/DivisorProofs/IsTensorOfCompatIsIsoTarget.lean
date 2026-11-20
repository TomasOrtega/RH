import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `hu hc hτ`. Establish `hlift : ∀ (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w), ν.lift U w x = Sec.map (u.f w) (τ.lift U w x)`. Introduce `U w x`. Establish `h : ν.lift U w = ((u.f w).hom.app (op U)).hom ∘ₗ τ.lift U w`. Apply `DirectSum.linearMap_ext` to reduce the goal to its premises.

Introduce `p`. Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `a b`. Simplify using `only [Pair.lift, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul]`. Conclude with `(hc U p.1.1 p.1.2 w p.2 a b).symm`.

Conclude with `LinearMap.congr_fun h x`. Establish `hinv : ∀ (w : ℤ) (U : Scheme.{0}) (y : Sec (K'.X w) U), Sec.map (u.f w) (Sec.map ((inv u).f w) y) = y`. Introduce `w U y`. Express the relevant statement in the definitionally equal form `Sec.map ((inv u).f w ≫ u.f w) y = y`. Rewrite using `[← HomologicalComplex.comp_f, IsIso.inv_hom_id, HomologicalComplex.id_f]`.

Both sides reduce to the same expression. Establish `hinv' : ∀ (w : ℤ) (U : Scheme.{0}) (y : Sec (K.X w) U), Sec.map ((inv u).f w) (Sec.map (u.f w) y) = y`. Introduce `w U y`. Express the relevant statement in the definitionally equal form `Sec.map (u.f w ≫ (inv u).f w) y = y`. Rewrite using `[← HomologicalComplex.comp_f, IsIso.hom_inv_id, HomologicalComplex.id_f]`.

Both sides reduce to the same expression. Establish `hnat : ∀ {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U), Sec.map φ (Sec.res g z) = Sec.res g (Sec.map φ z)`. Introduce `F G φ V U g z`. Conclude with `congrArg (fun f => f.hom z) (φ.hom.naturality g.op)`. Use `⟨fun U w y => ?_, fun U w x hx => ?_⟩` and prove the remaining obligations.

Take `⟨S, hS, hP⟩` from `hτ.1 U w (Sec.map ((inv u).f w) y)`. Use `⟨S, hS, fun V g hg => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hP V g hg`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[hlift, hx, hnat, hinv]`.

Apply `hτ.2 U w x` to reduce the goal to its premises. Rewrite `hx` using `[hlift]`. Establish `h2` using `congrArg (Sec.map ((inv u).f w)) hx`. Rewrite `h2` using `[hinv']`. Rewrite using `[h2]`.

Conclude with `map_zero _`.
-/
theorem Pair.isTensor_of_compat_isIso (R : Type) [CommRing R] {I J K K' : Cx R} (τ : Pair I J K) (ν : Pair I J K')
    (u : K ⟶ K') : IsIso u → τ.Compat ν (𝟙 I) (𝟙 J) u → τ.IsTensor → ν.IsTensor := by
  intro hu hc hτ
  have hlift : ∀ (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w), ν.lift U w x = Sec.map (u.f w) (τ.lift U w x) := by
    intro U w x
    have h : ν.lift U w = ((u.f w).hom.app (op U)).hom ∘ₗ τ.lift U w := by
      apply DirectSum.linearMap_ext
      intro p
      apply TensorProduct.ext'
      intro a b
      simp only [Pair.lift, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul]
      exact (hc U p.1.1 p.1.2 w p.2 a b).symm
    exact LinearMap.congr_fun h x
  have hinv : ∀ (w : ℤ) (U : Scheme.{0}) (y : Sec (K'.X w) U), Sec.map (u.f w) (Sec.map ((inv u).f w) y) = y := by
    intro w U y
    change Sec.map ((inv u).f w ≫ u.f w) y = y
    rw [← HomologicalComplex.comp_f, IsIso.inv_hom_id, HomologicalComplex.id_f]
    rfl
  have hinv' : ∀ (w : ℤ) (U : Scheme.{0}) (y : Sec (K.X w) U), Sec.map ((inv u).f w) (Sec.map (u.f w) y) = y := by
    intro w U y
    change Sec.map (u.f w ≫ (inv u).f w) y = y
    rw [← HomologicalComplex.comp_f, IsIso.hom_inv_id, HomologicalComplex.id_f]
    rfl
  have hnat : ∀ {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U),
      Sec.map φ (Sec.res g z) = Sec.res g (Sec.map φ z) := by
    intro F G φ V U g z
    exact congrArg (fun f => f.hom z) (φ.hom.naturality g.op)
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · obtain ⟨S, hS, hP⟩ := hτ.1 U w (Sec.map ((inv u).f w) y)
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    refine ⟨x, ?_⟩
    rw [hlift, hx, hnat, hinv]
  · apply hτ.2 U w x
    rw [hlift] at hx
    have h2 := congrArg (Sec.map ((inv u).f w)) hx
    rw [hinv'] at h2
    rw [h2]
    exact map_zero _

end GlobalTheory.EtC

end
