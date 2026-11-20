import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws

noncomputable section

open Matrix

namespace PositivityTheory.RgBcC.Cxb

open PositivityTheory.RgBcC

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `m`. Simplify using the standard rewrite rules.
-/
theorem map_comp' {M N P : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] [AddCommGroup P]
    [Module ℂ P] (f : N →ₗ[ℂ] P) (g : M →ₗ[ℂ] N) :
    ExteriorAlgebra.map (f ∘ₗ g) = (ExteriorAlgebra.map f).comp (ExteriorAlgebra.map g) := by
  ext m
  simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem creL_eq (v : Md n → ℂ) : creL n v = matL n (LinearMap.mul ℂ (abelian₂ n) (ExteriorAlgebra.ι ℂ v)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem annL_eq (w : Md n → ℂ) :
    annL n w = matL n (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (dualOf w)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gamM_eq (g : Matrix (Md n) (Md n) ℂ) : gamM g = matL n (ExteriorAlgebra.map (Matrix.toLin' g)).toLinearMap := rfl

/- English proof (translation)
The claim follows from `LinearMap.toMatrix_mul _ _ _`.
-/
theorem matL_mul (f h : abelian₂ n →ₗ[ℂ] abelian₂ n) : matL n (f * h) = matL n f * matL n h := LinearMap.toMatrix_mul _ _ _

/- English proof (translation)
The claim follows from `LinearMap.toMatrix_one _`.
-/
theorem matL_one : matL n (1 : abelian₂ n →ₗ[ℂ] abelian₂ n) = 1 := LinearMap.toMatrix_one _

/- English proof (translation)
Proceed by induction on `y using CliffordAlgebra.left_induction with`. Consider the case `algebraMap r`. Rewrite using `[AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap, CliffordAlgebra.contractLeft_algebraMap, map_zero]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`. Consider the case `ι_mul x m hx`.

Establish `e : ExteriorAlgebra.map f (CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) m * x) = CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) (f m) * ExteriorAlgebra.map f x`. Rewrite using `[map_mul]`. Conclude with `congrArg (· * _) (ExteriorAlgebra.map_apply_ι f m)`. Rewrite using `[e, CliffordAlgebra.contractLeft_ι_mul, hx, CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul]`. Rewrite using `[show ExteriorAlgebra.map f (CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) m) = CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) (f m) from ExteriorAlgebra.map_apply_ι f m]`.

Both sides reduce to the same expression.
-/
theorem contractLeft_map (f : (Md n → ℂ) →ₗ[ℂ] (Md n → ℂ)) (d : Module.Dual ℂ (Md n → ℂ)) (y : abelian₂ n) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) d (ExteriorAlgebra.map f y) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (d ∘ₗ f) y) := by
  induction y using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap, CliffordAlgebra.contractLeft_algebraMap, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x m hx =>
    have e : ExteriorAlgebra.map f (CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) m * x) =
        CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) (f m) * ExteriorAlgebra.map f x := by
      rw [map_mul]
      exact congrArg (· * _) (ExteriorAlgebra.map_apply_ι f m)
    rw [e, CliffordAlgebra.contractLeft_ι_mul, hx, CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul]
    rw [show ExteriorAlgebra.map f (CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) m) =
      CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) (f m) from ExteriorAlgebra.map_apply_ι f m]
    rfl

end PositivityTheory.RgBcC.Cxb

namespace PositivityTheory.RgBcC

open PositivityTheory.RgBcC.Cxb

/- English proof (translation)
Introduce `n`. Use `⟨?_, fun g h => ?_⟩` and prove the remaining obligations. Rewrite using `[gamM_eq, Matrix.toLin'_one, ExteriorAlgebra.map_id]`. Conclude with `LinearMap.toMatrix_id _`. Rewrite using `[gamM_eq, gamM_eq, gamM_eq, Matrix.toLin'_mul, map_comp', AlgHom.comp_toLinearMap, ← matL_mul]`.

Both sides reduce to the same expression.
-/
theorem gamMul : GamMul := by
  intro n
  refine ⟨?_, fun g h => ?_⟩
  · rw [gamM_eq, Matrix.toLin'_one, ExteriorAlgebra.map_id]
    exact LinearMap.toMatrix_id _
  · rw [gamM_eq, gamM_eq, gamM_eq, Matrix.toLin'_mul, map_comp', AlgHom.comp_toLinearMap, ← matL_mul]
    rfl

/- English proof (translation)
Introduce `n v w`. Rewrite using `[annL_eq, creL_eq, ← matL_mul, ← matL_mul, ← map_add, ← matL_one, ← map_smul]`. Use `congr 1`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`.

Rewrite using `[LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.mul_apply', LinearMap.mul_apply', CliffordAlgebra.contractLeft_ι_mul]`. Use `show (w ⬝ᵥ v) • y - _ + _ = _`. Normalize the expressions using the abelian group laws.
-/
theorem car : Car := by
  intro n v w
  rw [annL_eq, creL_eq, ← matL_mul, ← matL_mul, ← map_add, ← matL_one, ← map_smul]
  congr 1
  apply LinearMap.ext
  intro y
  rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.mul_apply', LinearMap.mul_apply', CliffordAlgebra.contractLeft_ι_mul]
  show (w ⬝ᵥ v) • y - _ + _ = _
  abel

/- English proof (translation)
Introduce `n g v w`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[gamM_eq, creL_eq, creL_eq, ← matL_mul, ← matL_mul]`. Use `congr 1`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Simplify using `only [Module.End.mul_apply, AlgHom.toLinearMap_apply, LinearMap.mul_apply', map_mul, ExteriorAlgebra.map_apply_ι, Matrix.toLin'_apply]`. Rewrite using `[gamM_eq, annL_eq, annL_eq, ← matL_mul, ← matL_mul]`. Use `congr 1`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, AlgHom.toLinearMap_apply]`.

Establish `hd : dualOf w ∘ₗ Matrix.toLin' g = dualOf (gᵀ *ᵥ w)`. Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, dualOf, LinearMap.coe_mk, AddHom.coe_mk, Matrix.toLin'_apply]`. Rewrite using `[Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]`. Rewrite using `[contractLeft_map, hd]`.
-/
theorem gamCre : GamCre := by
  intro n g v w
  refine ⟨?_, ?_⟩
  · rw [gamM_eq, creL_eq, creL_eq, ← matL_mul, ← matL_mul]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply, LinearMap.mul_apply', map_mul, ExteriorAlgebra.map_apply_ι,
      Matrix.toLin'_apply]
  · rw [gamM_eq, annL_eq, annL_eq, ← matL_mul, ← matL_mul]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply]
    have hd : dualOf w ∘ₗ Matrix.toLin' g = dualOf (gᵀ *ᵥ w) := by
      refine LinearMap.ext fun u => ?_
      simp only [LinearMap.comp_apply, dualOf, LinearMap.coe_mk, AddHom.coe_mk, Matrix.toLin'_apply]
      rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    rw [contractLeft_map, hd]

end PositivityTheory.RgBcC
