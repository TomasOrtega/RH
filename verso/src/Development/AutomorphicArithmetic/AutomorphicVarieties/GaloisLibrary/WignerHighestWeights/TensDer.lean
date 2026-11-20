import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ a π Ξ k Z h0 hk m' hm`. Set `e` to `TensorProduct.piScalarRight ℂ ℂ π.V (Fin Ξ.d)`. Establish `h1 : e m' ≠ 0` using `fun h => hm (e.map_eq_zero_iff.1 h)`. Take `⟨j, hj⟩` from `Function.ne_iff.1 h1`. Establish `h2 : (e m' j).1.1 ≠ 0` using `fun h => hj (Subtype.ext (Subtype.ext h))`.

Take `⟨g, hg⟩` from `Function.ne_iff.1 h2`. Set `l : π.V ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun m => (e m j).1.1 g map_add' := fun x y => by rw [map_add]; rfl map_smul' := fun c x => by rw [map_smul]; rfl }`. Establish `hl : ∀ (φ : π.V) (v : Fin Ξ.d → ℂ), l (φ ⊗ₜ v) = φ.1.1 g * v j` using `fun φ v => by`. Establish `h : e (φ ⊗ₜ v) j = v j • φ`. Simplify using `only [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]`.

Express the relevant statement in the definitionally equal form `(e (φ ⊗ₜ v) j).1.1 g = _`. Rewrite using `[h, mul_comm]`. Both sides reduce to the same expression. Establish `hc0 : (fun t => Unitary.toUnits (k t)) 0 = 1` using `by simp only [h0, map_one]`. Use `⟨l, hg, fun m => ?_⟩` and prove the remaining obligations.

Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simpa only [map_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)`. Consider the case `add x y hx hy => simpa only [map_add] using hx.fun_add hy`. Consider the case `tmul φ v`. Establish `h3` using `GlobalTheory.CuspRep.hasDerivAt_curve φ.1 g (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk`.

Establish `h4` using `HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk j i).mul_const (v i)`. Establish `h5` using `h3.fun_mul h4`. Simplify using `only [h0, map_one, mul_one] at h5`. Simplify using `only [tensorK, tensorLie_tmul, TensorProduct.map_tmul, map_add, hl, Matrix.toLin'_apply]`. Establish `h6 : ∑ i, (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) j i * v i = v j` using `congrFun (Matrix.one_mulVec v) j`.

Rewrite `h5` using `[h6]`. Conclude with `h5`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.tensDer :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), SepDer (tensorK π Ξ) (tensorLie π Ξ) := by
  intro E _ _ _ a π Ξ k Z h0 hk m' hm
  let e := TensorProduct.piScalarRight ℂ ℂ π.V (Fin Ξ.d)
  have h1 : e m' ≠ 0 := fun h => hm (e.map_eq_zero_iff.1 h)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 h1
  have h2 : (e m' j).1.1 ≠ 0 := fun h => hj (Subtype.ext (Subtype.ext h))
  obtain ⟨g, hg⟩ := Function.ne_iff.1 h2
  let l : π.V ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun m => (e m j).1.1 g
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hl : ∀ (φ : π.V) (v : Fin Ξ.d → ℂ), l (φ ⊗ₜ v) = φ.1.1 g * v j := fun φ v => by
    have h : e (φ ⊗ₜ v) j = v j • φ := by
      simp only [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    change (e (φ ⊗ₜ v) j).1.1 g = _
    rw [h, mul_comm]
    rfl
  have hc0 : (fun t => Unitary.toUnits (k t)) 0 = 1 := by simp only [h0, map_one]
  refine ⟨l, hg, fun m => ?_⟩
  induction m using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add x y hx hy => simpa only [map_add] using hx.fun_add hy
  | tmul φ v =>
    have h3 := GlobalTheory.CuspRep.hasDerivAt_curve φ.1 g (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk
    have h4 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk j i).mul_const (v i)
    have h5 := h3.fun_mul h4
    simp only [h0, map_one, mul_one] at h5
    simp only [tensorK, tensorLie_tmul, TensorProduct.map_tmul, map_add, hl, Matrix.toLin'_apply]
    have h6 : ∑ i, (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) j i * v i = v j := congrFun (Matrix.one_mulVec v) j
    rw [h6] at h5
    exact h5
