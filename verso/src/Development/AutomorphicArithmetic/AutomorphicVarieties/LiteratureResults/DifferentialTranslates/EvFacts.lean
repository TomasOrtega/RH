import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero`. Rewrite using `[map_zero, map_zero]`. Both sides reduce to the same expression. Consider the case `tmul φ v`.

Use function extensionality and compare the values at `g`. Simplify using `[mul_comm]`. Consider the case `add x y hx hy`. Rewrite using `[map_add, map_add, Pi.add_apply, Submodule.coe_add, ← hx, ← hy]`. Both sides reduce to the same expression.
-/
private theorem ev_comp {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    (fun g => ev m g j) = (TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d) m j).1 := by
  induction m using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    rfl
  | tmul φ v =>
    funext g
    simp [mul_comm]
  | add x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, Submodule.coe_add, ← hx, ← hy]
    rfl

/- English proof (translation)
Introduce `E _ _ _ a d`. Use `⟨fun m m' h => ?_, fun m j => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Apply `(TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[← ev_comp, ← ev_comp, h]`. Rewrite using `[ev_comp]`. Conclude with `Subtype.property _`. Use `⟨(TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).symm fun j => ⟨_, hf j⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g j`.

Use `congrFun (ev_comp ((TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).symm fun j => ⟨_, hf j⟩) j) g` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Conclude with `this`.
-/
theorem evFacts : EvFacts := by
  intro E _ _ _ a d
  refine ⟨fun m m' h => ?_, fun m j => ?_, fun f hf => ?_⟩
  · apply (TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).injective
    funext j
    apply Subtype.ext
    rw [← ev_comp, ← ev_comp, h]
  · rw [ev_comp]
    exact Subtype.property _
  · refine ⟨(TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).symm fun j => ⟨_, hf j⟩, ?_⟩
    funext g j
    have := congrFun (ev_comp ((TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).symm fun j => ⟨_, hf j⟩) j) g
    rw [LinearEquiv.apply_symm_apply] at this
    exact this

end UpperTheory.V.Lit.Dr
