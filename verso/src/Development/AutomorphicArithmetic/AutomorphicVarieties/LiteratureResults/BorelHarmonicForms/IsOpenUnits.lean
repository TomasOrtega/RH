import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CxGrpComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneParam
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

/- English proof (translation)
Establish `e : {x : Fin a → Fin a → T → ℂ | IsUnit (Matrix.of x)} = ⋂ t, {x : Fin a → Fin a → T → ℂ | (Matrix.of x).det t ≠ 0}`. Use extensionality with `x`. Simplify using `[Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]`. Rewrite using `[e]`. Use `isOpen_iInter_of_finite fun t => isOpen_ne_fun ?_ continuous_const` and prove the remaining obligations.

Establish `h : Continuous fun x : Fin a → Fin a → T → ℂ => (Matrix.of x).det` using `Continuous.matrix_det continuous_id`. Conclude with `(continuous_apply t).comp h`.
-/
private theorem isOpen_units (T : Type) [Fintype T] (a : ℕ) :
    IsOpen {x : Fin a → Fin a → T → ℂ | IsUnit (Matrix.of x)} := by
  have e : {x : Fin a → Fin a → T → ℂ | IsUnit (Matrix.of x)} = ⋂ t, {x : Fin a → Fin a → T → ℂ | (Matrix.of x).det t ≠ 0} := by
    ext x
    simp [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
  rw [e]
  refine isOpen_iInter_of_finite fun t => isOpen_ne_fun ?_ continuous_const
  have h : Continuous fun x : Fin a → Fin a → T → ℂ => (Matrix.of x).det := Continuous.matrix_det continuous_id
  exact (continuous_apply t).comp h

/- English proof (translation)
Introduce `E _ _ _ a Ξ`. Take `⟨R, Φ, hΦ, hR, hm⟩` from `UpperTheory.V.Lit.Bor.cxGrp E a Ξ`. Establish `ho` using `isOpen_units (E →+* ℂ) a`. Set `o : Fin a → Fin a → (E →+* ℂ) → ℂ` to `fun i j => (1 : Matrix (Fin a) (Fin a) ((E →+* ℂ) → ℂ)) i j`. Establish `hd : ∀ k l (g : GL (Fin a) ((E →+* ℂ) → ℂ)), DifferentiableAt ℂ (Φ k l) (fun i j => g.val i j)` using `fun k l g => (hΦ k l).differentiableAt (ho.mem_nhds g.isUnit)`.

Establish `hd1 : ∀ k l, HasFDerivAt (Φ k l) ((fderiv ℂ (Φ k l) o).restrictScalars ℝ) o` using `fun k l => (hd k l 1).hasFDerivAt.restrictScalars ℝ`. Set `D : Matrix (Fin a) (Fin a) ((E →+* ℂ) → ℂ) →ₗ[ℂ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ` to `{ toFun := fun Z => Matrix.of fun k l => fderiv ℂ (Φ k l) o (fun i j => Z i j) map_add' := fun X Y => by`. Use extensionality with `k l`. Conclude with `map_add (fderiv ℂ (Φ k l) o) (fun i j => X i j) (fun i j => Y i j)`. Use the proof step `map_smul' := fun c X => by`.

Use extensionality with `k l`. Conclude with `map_smul (fderiv ℂ (Φ k l) o) c (fun i j => X i j) }`. Use `⟨R, D, ⟨fun k l => ?_, fun c Z h0 hc k l => ?_⟩, fun X => ?_⟩` and prove the remaining obligations. Simplify using `only [hR]`. Use `continuous_iff_continuousAt.2 fun g => ?_` and prove the remaining obligations.

Establish `hv : Continuous fun g : GL (Fin a) ((E →+* ℂ) → ℂ) => (fun i j => g.val i j : Fin a → Fin a → (E →+* ℂ) → ℂ)` using `Units.continuous_val (M := Matrix (Fin a) (Fin a) ((E →+* ℂ) → ℂ))`. Conclude with `ContinuousAt.comp (f := fun g : GL (Fin a) ((E →+* ℂ) → ℂ) => (fun i j => g.val i j : Fin a → Fin a → (E →+* ℂ) → ℂ)) (hd k l g).continuousAt hv.continuousAt`. Simplify using `only [hR]`. Establish `h1 : HasDerivAt (fun s => (fun i j => (c s).val i j : Fin a → Fin a → (E →+* ℂ) → ℂ)) (fun i j => Z i j) 0` using `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun t => hc i j t`. Conclude with `(hd1 k l).comp_hasDerivAt_of_eq (0 : ℝ) h1 (by rw [h0]; rfl)`.

Use extensionality with `k l`. Set `L : Lie E a →L[ℝ] (Fin a → Fin a → (E →+* ℂ) → ℂ)` to `ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j => ContinuousLinearMap.pi fun τ => (coordL τ).comp ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin a → Cinf E) i))`. Establish `hL : L (oneL E a) = o`. Use function extensionality and compare the values at `i j`. Conclude with `congrFun (congrFun (Matrix.map_one (emb E) (map_zero _) (map_one _)) i) j`.

Establish `h` using `extGL_eventuallyEq (f := fun y => Ξ.mat y k l) (F := fun x => Φ k l (L x)) (fun y => by rw [← hm, hR]; rfl) (x := oneL E a) isUnit_one`. Establish `h1 : HasFDerivAt (Φ k l) ((fderiv ℂ (Φ k l) o).restrictScalars ℝ) (L (oneL E a))`. Rewrite using `[hL]`. Conclude with `hd1 k l`. Establish `h2` using `HasFDerivAt.comp (oneL E a) h1 L.hasFDerivAt`.

Express the relevant statement in the definitionally equal form `_ = fderiv ℝ _ _ (toL X)`. Rewrite using `[h.fderiv_eq]`. Conclude with `(congrArg (fun M : Lie E a →L[ℝ] ℂ => M (toL X)) h2.fderiv).symm`.
-/
theorem UpperTheory.V.Lit.Bor.cxExt :
    UpperTheory.V.Lit.Bor.CxExt := by
  intro E _ _ _ a Ξ
  classical
  obtain ⟨R, Φ, hΦ, hR, hm⟩ := UpperTheory.V.Lit.Bor.cxGrp E a Ξ
  have ho := isOpen_units (E →+* ℂ) a
  let o : Fin a → Fin a → (E →+* ℂ) → ℂ := fun i j => (1 : Matrix (Fin a) (Fin a) ((E →+* ℂ) → ℂ)) i j
  have hd : ∀ k l (g : GL (Fin a) ((E →+* ℂ) → ℂ)), DifferentiableAt ℂ (Φ k l) (fun i j => g.val i j) := fun k l g =>
    (hΦ k l).differentiableAt (ho.mem_nhds g.isUnit)
  have hd1 : ∀ k l, HasFDerivAt (Φ k l) ((fderiv ℂ (Φ k l) o).restrictScalars ℝ) o := fun k l =>
    (hd k l 1).hasFDerivAt.restrictScalars ℝ
  let D : Matrix (Fin a) (Fin a) ((E →+* ℂ) → ℂ) →ₗ[ℂ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
    { toFun := fun Z => Matrix.of fun k l => fderiv ℂ (Φ k l) o (fun i j => Z i j)
      map_add' := fun X Y => by
        ext k l
        exact map_add (fderiv ℂ (Φ k l) o) (fun i j => X i j) (fun i j => Y i j)
      map_smul' := fun c X => by
        ext k l
        exact map_smul (fderiv ℂ (Φ k l) o) c (fun i j => X i j) }
  refine ⟨R, D, ⟨fun k l => ?_, fun c Z h0 hc k l => ?_⟩, fun X => ?_⟩
  · simp only [hR]
    refine continuous_iff_continuousAt.2 fun g => ?_
    have hv : Continuous fun g : GL (Fin a) ((E →+* ℂ) → ℂ) => (fun i j => g.val i j : Fin a → Fin a → (E →+* ℂ) → ℂ) :=
      Units.continuous_val (M := Matrix (Fin a) (Fin a) ((E →+* ℂ) → ℂ))
    exact ContinuousAt.comp (f := fun g : GL (Fin a) ((E →+* ℂ) → ℂ) => (fun i j => g.val i j : Fin a → Fin a → (E →+* ℂ) → ℂ))
      (hd k l g).continuousAt hv.continuousAt
  · simp only [hR]
    have h1 : HasDerivAt (fun s => (fun i j => (c s).val i j : Fin a → Fin a → (E →+* ℂ) → ℂ)) (fun i j => Z i j) 0 :=
      hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun t => hc i j t
    exact (hd1 k l).comp_hasDerivAt_of_eq (0 : ℝ) h1 (by rw [h0]; rfl)
  · ext k l
    let L : Lie E a →L[ℝ] (Fin a → Fin a → (E →+* ℂ) → ℂ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j => ContinuousLinearMap.pi fun τ =>
        (coordL τ).comp ((ContinuousLinearMap.proj j).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin a → Cinf E) i))
    have hL : L (oneL E a) = o := by
      funext i j
      exact congrFun (congrFun (Matrix.map_one (emb E) (map_zero _) (map_one _)) i) j
    have h := extGL_eventuallyEq (f := fun y => Ξ.mat y k l) (F := fun x => Φ k l (L x))
      (fun y => by rw [← hm, hR]; rfl) (x := oneL E a) isUnit_one
    have h1 : HasFDerivAt (Φ k l) ((fderiv ℂ (Φ k l) o).restrictScalars ℝ) (L (oneL E a)) := by
      rw [hL]; exact hd1 k l
    have h2 := HasFDerivAt.comp (oneL E a) h1 L.hasFDerivAt
    change _ = fderiv ℝ _ _ (toL X)
    rw [h.fderiv_eq]
    exact (congrArg (fun M : Lie E a →L[ℝ] ℂ => M (toL X)) h2.fderiv).symm
