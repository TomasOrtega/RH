import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Introduce `X _ _ V F _ _ _ _ _ _ q f x hf`. Set `b` to `Module.finBasis ℝ V`. Set `E : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] ((Fin q → Fin (Module.finrank ℝ V)) → F)` to `{ toFun := fun a k => a fun i => b (k i) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hE : Function.Injective E`. Introduce `a a' h`.

Apply `ContinuousAlternatingMap.toAlternatingMap_injective` to reduce the goal to its premises. Use `Module.Basis.ext_alternating b fun k _ => ?_` and prove the remaining obligations. Conclude with `congrFun h k`. Take `⟨g, hg⟩` from `E.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hE)`. Establish `h1 : ContDiffAt ℝ ∞ (fun y => E (f y)) x` using `contDiffAt_pi.2 fun k => hf _`.

Establish `h2` using `(LinearMap.toContinuousLinearMap g).contDiff.contDiffAt.comp x h1`. Establish `h3 : (LinearMap.toContinuousLinearMap g) ∘ (fun y => E (f y)) = f`. Use function extensionality and compare the values at `y`. Conclude with `LinearMap.congr_fun hg (f y)`. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis.
-/
theorem altSmooth : AltSmooth := by
  intro X _ _ V F _ _ _ _ _ _ q f x hf
  let b := Module.finBasis ℝ V
  let E : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] ((Fin q → Fin (Module.finrank ℝ V)) → F) :=
    { toFun := fun a k => a fun i => b (k i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hE : Function.Injective E := by
    intro a a' h
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine Module.Basis.ext_alternating b fun k _ => ?_
    exact congrFun h k
  obtain ⟨g, hg⟩ := E.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hE)
  have h1 : ContDiffAt ℝ ∞ (fun y => E (f y)) x := contDiffAt_pi.2 fun k => hf _
  have h2 := (LinearMap.toContinuousLinearMap g).contDiff.contDiffAt.comp x h1
  have h3 : (LinearMap.toContinuousLinearMap g) ∘ (fun y => E (f y)) = f := by
    funext y
    exact LinearMap.congr_fun hg (f y)
  rwa [h3] at h2

end UpperTheory.V.Lit.Dr
