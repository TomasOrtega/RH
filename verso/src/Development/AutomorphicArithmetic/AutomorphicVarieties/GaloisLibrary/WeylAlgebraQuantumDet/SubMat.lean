import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop

open Matrix UpperTheory.V.Weyl

/- English proof (translation)
Introduce `G _ d ρ S hS`. Take `⟨T, hT⟩` from `Submodule.exists_isCompl S`. Set `b` to `Module.finBasis ℂ S`. Set `P : (Fin d → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ)` to `b.equivFun.toLinearMap ∘ₗ Submodule.linearProjOfIsCompl S T hT`. Set `I : (Fin (Module.finrank ℂ S) → ℂ) →ₗ[ℂ] (Fin d → ℂ)` to `S.subtype ∘ₗ b.equivFun.symm.toLinearMap`.

Establish `hIP : ∀ v, v ∈ S → I (P v) = v`. Introduce `v hv`. Establish `e : S.linearProjOfIsCompl T hT v = ⟨v, hv⟩` using `Submodule.linearProjOfIsCompl_apply_left hT ⟨v, hv⟩`. Use `show ((b.equivFun.symm (b.equivFun (S.linearProjOfIsCompl T hT v)) : S) : Fin d → ℂ) = v`. Rewrite using `[e, LinearEquiv.symm_apply_apply]`.

Establish `hPI : P ∘ₗ I = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `w`. Establish `e : S.linearProjOfIsCompl T hT ((b.equivFun.symm w : S) : Fin d → ℂ) = b.equivFun.symm w` using `Submodule.linearProjOfIsCompl_apply_left hT _`. Use `show b.equivFun (S.linearProjOfIsCompl T hT ((b.equivFun.symm w : S) : Fin d → ℂ)) = w`.

Rewrite using `[e, LinearEquiv.apply_symm_apply]`. Set `A` to `LinearMap.toMatrix' I`. Set `B` to `LinearMap.toMatrix' P`. Establish `hAw : ∀ w, A *ᵥ w = I w` using `fun w => LinearMap.toMatrix'_mulVec I w`. Establish `hBw : ∀ v, B *ᵥ v = P v` using `fun v => LinearMap.toMatrix'_mulVec P v`.

Establish `hBA : B * A = 1`. Rewrite using `[← LinearMap.toMatrix'_comp, hPI, LinearMap.toMatrix'_id]`. Establish `key : ∀ M : Matrix (Fin d) (Fin (Module.finrank ℂ S)) ℂ, (∀ w, M *ᵥ w ∈ S) → A * (B * M) = M`. Introduce `M hM`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `w`. Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBw, hAw, hIP _ (hM w)]`. Establish `hAS : ∀ w, A *ᵥ w ∈ S`. Introduce `w`.

Rewrite using `[hAw]`. Conclude with `(b.equivFun.symm w).2`. Establish `hcol : ∀ y w, (ρ y * A) *ᵥ w ∈ S`. Introduce `y w`. Rewrite using `[← Matrix.mulVec_mulVec]`.

Conclude with `hS y _ (hAS w)`. Set `ρ' : G →* Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ` to `{ toFun := fun y => B * ρ y * A map_one' := by simp only [map_one, Matrix.mul_one, hBA] map_mul' := by`. Introduce `x y`. Simplify using `only [map_mul, Matrix.mul_assoc]`. Rewrite using `[key _ (hcol y)] }`.

Use `⟨_, A, B, ρ', rfl, hBA, hAS, fun y => rfl, fun y => ?_⟩` and prove the remaining obligations. Use `show ρ y * A = A * (B * ρ y * A)`. Rewrite using `[Matrix.mul_assoc B, key _ (hcol y)]`.
-/
theorem UpperTheory.V.Weyl.subMat :
    ∀ (G : Type) [Monoid G] (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (S : Submodule ℂ (Fin d → ℂ)),
      (∀ y, ∀ v ∈ S, ρ y *ᵥ v ∈ S) →
      ∃ (d' : ℕ) (A : Matrix (Fin d) (Fin d') ℂ) (B : Matrix (Fin d') (Fin d) ℂ) (ρ' : G →* Matrix (Fin d') (Fin d') ℂ),
        d' = Module.finrank ℂ S ∧ B * A = 1 ∧ (∀ w, A *ᵥ w ∈ S) ∧ (∀ y, ρ' y = B * ρ y * A) ∧ ∀ y, ρ y * A = A * ρ' y := by
  intro G _ d ρ S hS
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl S
  let b := Module.finBasis ℂ S
  let P : (Fin d → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    b.equivFun.toLinearMap ∘ₗ Submodule.linearProjOfIsCompl S T hT
  let I : (Fin (Module.finrank ℂ S) → ℂ) →ₗ[ℂ] (Fin d → ℂ) := S.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hIP : ∀ v, v ∈ S → I (P v) = v := by
    intro v hv
    have e : S.linearProjOfIsCompl T hT v = ⟨v, hv⟩ := Submodule.linearProjOfIsCompl_apply_left hT ⟨v, hv⟩
    show ((b.equivFun.symm (b.equivFun (S.linearProjOfIsCompl T hT v)) : S) : Fin d → ℂ) = v
    rw [e, LinearEquiv.symm_apply_apply]
  have hPI : P ∘ₗ I = LinearMap.id := by
    apply LinearMap.ext
    intro w
    have e : S.linearProjOfIsCompl T hT ((b.equivFun.symm w : S) : Fin d → ℂ) = b.equivFun.symm w :=
      Submodule.linearProjOfIsCompl_apply_left hT _
    show b.equivFun (S.linearProjOfIsCompl T hT ((b.equivFun.symm w : S) : Fin d → ℂ)) = w
    rw [e, LinearEquiv.apply_symm_apply]
  let A := LinearMap.toMatrix' I
  let B := LinearMap.toMatrix' P
  have hAw : ∀ w, A *ᵥ w = I w := fun w => LinearMap.toMatrix'_mulVec I w
  have hBw : ∀ v, B *ᵥ v = P v := fun v => LinearMap.toMatrix'_mulVec P v
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp, hPI, LinearMap.toMatrix'_id]
  have key : ∀ M : Matrix (Fin d) (Fin (Module.finrank ℂ S)) ℂ, (∀ w, M *ᵥ w ∈ S) → A * (B * M) = M := by
    intro M hM
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBw, hAw,
      hIP _ (hM w)]
  have hAS : ∀ w, A *ᵥ w ∈ S := by
    intro w
    rw [hAw]
    exact (b.equivFun.symm w).2
  have hcol : ∀ y w, (ρ y * A) *ᵥ w ∈ S := by
    intro y w
    rw [← Matrix.mulVec_mulVec]
    exact hS y _ (hAS w)
  let ρ' : G →* Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ :=
    { toFun := fun y => B * ρ y * A
      map_one' := by simp only [map_one, Matrix.mul_one, hBA]
      map_mul' := by
        intro x y
        simp only [map_mul, Matrix.mul_assoc]
        rw [key _ (hcol y)] }
  refine ⟨_, A, B, ρ', rfl, hBA, hAS, fun y => rfl, fun y => ?_⟩
  show ρ y * A = A * (B * ρ y * A)
  rw [Matrix.mul_assoc B, key _ (hcol y)]
