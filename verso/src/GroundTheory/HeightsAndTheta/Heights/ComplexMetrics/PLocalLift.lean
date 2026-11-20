import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

/- English proof (translation)
Introduce `A _ N X U f p hp`. Take `⟨t, ht⟩` from `X.ι.stalkMap_surjective p (germR hp f)`. Take `⟨V, hpV, g, hg⟩` from `(projectiveSpace A N).presheaf.exists_germ_eq t`. Establish `h1 : X.X.presheaf.germ U p hp f = X.X.presheaf.germ (X.ι ⁻¹ᵁ V) p hpV (X.ι.app V g)`. Rewrite using `[← Scheme.Hom.germ_stalkMap_apply, hg]`.

Conclude with `ht.symm`. Take `⟨W, hpW, iU, iV, he⟩` from `X.X.presheaf.germ_eq p hp hpV _ _ h1`. Use `⟨V, g, W, hpW, iU.le, iV.le, fun p' hp' => ?_⟩` and prove the remaining obligations. Establish `e1` using `X.X.presheaf.germ_res_apply iU p' hp' f`. Establish `e2` using `X.X.presheaf.germ_res_apply iV p' hp' (X.ι.app V g)`.

Establish `e3` using `Scheme.Hom.germ_stalkMap_apply X.ι V p' (iV.le hp') g`. Conclude with `e1.symm.trans ((congrArg (X.X.presheaf.germ W p' hp') he).trans (e2.trans e3.symm))`.
-/
theorem ComplexMetric.LocalLift.proof : ComplexMetric.LocalLift.Statement.{u} := by
  intro A _ N X U f p hp
  obtain ⟨t, ht⟩ := X.ι.stalkMap_surjective p (germR hp f)
  obtain ⟨V, hpV, g, hg⟩ := (projectiveSpace A N).presheaf.exists_germ_eq t
  have h1 : X.X.presheaf.germ U p hp f =
      X.X.presheaf.germ (X.ι ⁻¹ᵁ V) p hpV (X.ι.app V g) := by
    rw [← Scheme.Hom.germ_stalkMap_apply, hg]
    exact ht.symm
  obtain ⟨W, hpW, iU, iV, he⟩ := X.X.presheaf.germ_eq p hp hpV _ _ h1
  refine ⟨V, g, W, hpW, iU.le, iV.le, fun p' hp' => ?_⟩
  have e1 := X.X.presheaf.germ_res_apply iU p' hp' f
  have e2 := X.X.presheaf.germ_res_apply iV p' hp' (X.ι.app V g)
  have e3 := Scheme.Hom.germ_stalkMap_apply X.ι V p' (iV.le hp') g
  exact e1.symm.trans ((congrArg (X.X.presheaf.germ W p' hp') he).trans (e2.trans e3.symm))

end GroundTheory.Heights₂.Heights
