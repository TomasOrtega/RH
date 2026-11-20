import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory.GlVec

/- English proof (translation)
Introduce `E _ _ _ a f hf`. Set `Tl : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Lie E a` to `{ toFun := fun x => toL x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Set `T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a` to `LinearMap.toContinuousLinearMap Tl`. Establish `hT : ∀ x, T x = toL x` using `fun _ => rfl`. Establish `hval : ∀ (g : glG E a) (Y : glL E a), ((g * (glH E a).expG Y : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val = (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E))`.

Introduce `g Y`. Both sides reduce to the same expression. Establish `hsm : (glH E a).IsSmoothFun (fun y : glG E a => f (toL y.1.val))`. Rewrite using `[IsExpLieAlgebra.isSmoothFun_iff]`. Introduce `g`.

Establish `hin : ContDiff ℝ ∞ (fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E))))` using `T.contDiff.comp (contDiff_const.mul ((GroundTheory.Automorphic.contDiff_exp ℝ _).comp (glL E a).subtypeL.contDiff))`. Use `hf.comp_contDiff hin (fun Y => by` as an intermediate fact. Rewrite using `[hT, ← hval g Y]`. Conclude with `val_mem_invSet _)`. Establish `e : (fun Y : glL E a => f (toL ((g * (glH E a).expG Y : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val)) = f ∘ fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))`.

Use function extensionality and compare the values at `Y`. Simplify using `only [Function.comp_apply, hT, hval]`. Rewrite using `[e]`. Conclude with `this`. Use `⟨hsm, fun X => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Conclude with `(hf.fderiv_of_isOpen isOpen_invSet (by simp)).clm_apply (rmul (toL X.1)).contDiff.contDiffOn`. Use function extensionality and compare the values at `y`. Establish `h1` using `IsExpLieAlgebra.hasDerivAt_rightDeriv (glH E a) hsm X y`. Establish `hy : toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val ∈ invSet E a` using `val_mem_invSet _`. Establish `hfd : HasFDerivAt f (fderiv ℝ f (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val)) (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val)` using `((hf.contDiffAt (isOpen_invSet.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt`.

Establish `hc : HasDerivAt (fun t : ℝ => T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * NormedSpace.exp (t • (X : Matrix (Fin a) (Fin a) (Cinf E))))) (T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * (X : Matrix (Fin a) (Fin a) (Cinf E)))) 0`. Establish `h2` using `(hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (0 : ℝ)).const_mul (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val`. Simplify using `only [zero_smul, NormedSpace.exp_zero, one_mul] at h2`. Conclude with `T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2`. Establish `hc' : HasDerivAt (fun t : ℝ => T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * NormedSpace.exp (t • (X : Matrix (Fin a) (Fin a) (Cinf E))))) _ 0` using `hc`.

Establish `h3` using `(show HasFDerivAt f (fderiv ℝ f (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val)) (T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * NormedSpace.exp ((0:ℝ) • (X : Matrix (Fin a) (Fin a) (Cinf E))))) by`. Simplify `hfd).comp_hasDerivAt (0 : ℝ) hc'` using `[hT]`. Conclude with `h1.unique h3`.
-/
theorem isSmoothFun_and_rightDeriv_eq_vecF : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (glH E a).IsSmoothFun (fun y : glG E a => f (toL y.1.val)) ∧ ∀ X : glL E a, ContDiffOn ℝ ∞ (vecF E a (toL X.1) f) (invSet E a) ∧ (glH E a).rightDeriv X (fun y : glG E a => f (toL y.1.val)) = fun y : glG E a => vecF E a (toL X.1) f (toL y.1.val) := by
  intro E _ _ _ a f hf
  let Tl : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Lie E a :=
    { toFun := fun x => toL x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap Tl
  have hT : ∀ x, T x = toL x := fun _ => rfl
  have hval : ∀ (g : glG E a) (Y : glL E a), ((g * (glH E a).expG Y : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val
      = (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E)) := by
    intro g Y; rfl
  have hsm : (glH E a).IsSmoothFun (fun y : glG E a => f (toL y.1.val)) := by
    rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro g
    have hin : ContDiff ℝ ∞ (fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
        NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))) :=
      T.contDiff.comp (contDiff_const.mul ((GroundTheory.Automorphic.contDiff_exp ℝ _).comp (glL E a).subtypeL.contDiff))
    have := hf.comp_contDiff hin (fun Y => by
      rw [hT, ← hval g Y]; exact val_mem_invSet _)
    have e : (fun Y : glL E a => f (toL ((g * (glH E a).expG Y : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val)) =
        f ∘ fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
          NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E))) := by
      funext Y; simp only [Function.comp_apply, hT, hval]
    rw [e]
    exact this
  refine ⟨hsm, fun X => ⟨?_, ?_⟩⟩
  · exact (hf.fderiv_of_isOpen isOpen_invSet (by simp)).clm_apply (rmul (toL X.1)).contDiff.contDiffOn
  · funext y
    have h1 := IsExpLieAlgebra.hasDerivAt_rightDeriv (glH E a) hsm X y
    have hy : toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val ∈ invSet E a := val_mem_invSet _
    have hfd : HasFDerivAt f (fderiv ℝ f (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val))
        (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val) :=
      ((hf.contDiffAt (isOpen_invSet.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
    have hc : HasDerivAt (fun t : ℝ => T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
        NormedSpace.exp (t • (X : Matrix (Fin a) (Fin a) (Cinf E)))))
        (T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * (X : Matrix (Fin a) (Fin a) (Cinf E)))) 0 := by
      have h2 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (0 : ℝ)).const_mul
        (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val
      simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
      exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
    have hc' : HasDerivAt (fun t : ℝ => T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
        NormedSpace.exp (t • (X : Matrix (Fin a) (Fin a) (Cinf E))))) _ 0 := hc
    have h3 := (show HasFDerivAt f (fderiv ℝ f (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val))
        (T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * NormedSpace.exp ((0:ℝ) • (X : Matrix (Fin a) (Fin a) (Cinf E))))) by
          simpa [hT] using hfd).comp_hasDerivAt (0 : ℝ) hc'
    exact h1.unique h3

end GlobalTheory.GlVec
