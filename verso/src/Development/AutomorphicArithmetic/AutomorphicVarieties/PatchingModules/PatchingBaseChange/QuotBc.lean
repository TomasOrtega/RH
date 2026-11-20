import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Introduce `R R' _ _ _ M _ _ I I' hI`. Substitute `hI` using the available equality. Establish `hker : ∀ i ∈ I, ∀ y : R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M)), i • y = 0`. Introduce `i hi y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => exact smul_zero _`. Consider the case `tmul a q`. Proceed by induction on `q using Submodule.Quotient.induction_on with`. Consider the case `H m`. Rewrite using `[← TensorProduct.tmul_smul, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hi Submodule.mem_top), TensorProduct.tmul_zero]`.

Consider the case `add y z hy hz => rw [smul_add, hy, hz, add_zero]`. Establish `hann : I.map (algebraMap R R') ≤ Module.annihilator R' (R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M)))` using `Ideal.map_le_iff_le_comap.2 fun i hi => Module.mem_annihilator.2 fun y => by`. Rewrite using `[algebraMap_smul]`. Conclude with `hker i hi y`. Set `ψ : M ⧸ (I • ⊤ : Submodule R M) →ₗ[R] (R' ⊗[R] M) ⧸ (I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M))` to `(I • ⊤ : Submodule R M).liftQ (((I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)).mkQ.restrictScalars R) ∘ₗ TensorProduct.mk R R' M 1) (by`.

Rewrite using `[Submodule.smul_le]`. Introduce `i hi m _`. Rewrite using `[LinearMap.mem_ker, LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, TensorProduct.tmul_smul, ← algebraMap_smul R' i ((1 : R') ⊗ₜ[R] m)]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hi) Submodule.mem_top)`. Set `φ` to `ψ.liftBaseChange R'`.

Set `χ` to `(I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)).liftQ (LinearMap.baseChange R' (I • ⊤ : Submodule R M).mkQ) (by`. Rewrite using `[Submodule.smul_le]`. Introduce `r hr x _`. Rewrite using `[LinearMap.mem_ker, map_smul]`. Conclude with `Module.mem_annihilator.1 (hann hr) _)`.

Use `⟨LinearEquiv.ofLinear φ χ ?_ ?_⟩` and prove the remaining obligations. Apply `Submodule.linearMap_qext` to reduce the goal to its premises. Apply `TensorProduct.AlgebraTensorModule.ext` to reduce the goal to its premises. Introduce `a m`. Simplify using `[φ, χ, ψ]`.

Rewrite using `[← Submodule.Quotient.mk_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Apply `TensorProduct.AlgebraTensorModule.ext` to reduce the goal to its premises. Introduce `a q`. Proceed by induction on `q using Submodule.Quotient.induction_on with`. Consider the case `H m => simp [φ, χ, ψ, TensorProduct.smul_tmul']`.
-/
theorem UpperTheory.V.Pa.BC.quot_bc :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (I : Ideal R) (I' : Ideal R'), I' = I.map (algebraMap R R') → Nonempty (R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R'] (R' ⊗[R] M) ⧸ (I' • ⊤ : Submodule R' (R' ⊗[R] M))) := by
  intro R R' _ _ _ M _ _ I I' hI
  subst hI
  have hker : ∀ i ∈ I, ∀ y : R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M)), i • y = 0 := by
    intro i hi y
    induction y using TensorProduct.induction_on with
    | zero => exact smul_zero _
    | tmul a q =>
      induction q using Submodule.Quotient.induction_on with
      | H m =>
        rw [← TensorProduct.tmul_smul, ← Submodule.Quotient.mk_smul,
          (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hi Submodule.mem_top),
          TensorProduct.tmul_zero]
    | add y z hy hz => rw [smul_add, hy, hz, add_zero]
  have hann : I.map (algebraMap R R') ≤ Module.annihilator R' (R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M))) :=
    Ideal.map_le_iff_le_comap.2 fun i hi => Module.mem_annihilator.2 fun y => by
      rw [algebraMap_smul]
      exact hker i hi y
  let ψ : M ⧸ (I • ⊤ : Submodule R M) →ₗ[R]
      (R' ⊗[R] M) ⧸ (I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)) :=
    (I • ⊤ : Submodule R M).liftQ
      (((I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)).mkQ.restrictScalars R) ∘ₗ
        TensorProduct.mk R R' M 1) (by
      rw [Submodule.smul_le]
      intro i hi m _
      rw [LinearMap.mem_ker, LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, TensorProduct.tmul_smul,
        ← algebraMap_smul R' i ((1 : R') ⊗ₜ[R] m)]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hi) Submodule.mem_top)
  let φ := ψ.liftBaseChange R'
  let χ := (I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)).liftQ
    (LinearMap.baseChange R' (I • ⊤ : Submodule R M).mkQ) (by
      rw [Submodule.smul_le]
      intro r hr x _
      rw [LinearMap.mem_ker, map_smul]
      exact Module.mem_annihilator.1 (hann hr) _)
  refine ⟨LinearEquiv.ofLinear φ χ ?_ ?_⟩
  · apply Submodule.linearMap_qext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    simp [φ, χ, ψ]
    rw [← Submodule.Quotient.mk_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · apply TensorProduct.AlgebraTensorModule.ext
    intro a q
    induction q using Submodule.Quotient.induction_on with
    | H m => simp [φ, χ, ψ, TensorProduct.smul_tmul']
