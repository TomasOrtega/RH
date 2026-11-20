import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJFEInducedChar

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Measures MeasureTheory GJMatrix
open scoped NNReal
open ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

def matrixTensor (g : Fin n × Fin n → F → ℂ) (X : Matrix (Fin n) (Fin n) F) : ℂ :=
  ∏ ij : Fin n × Fin n, g ij (X ij.1 ij.2)

omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/- English proof (translation)
Simplify using `[matrixTensor, norm_prod]`.
-/
theorem matrixTensor_norm (g : Fin n × Fin n → F → ℂ) (X : Matrix (Fin n) (Fin n) F) :
    matrixTensor (fun ij x => ((‖g ij x‖ : ℝ) : ℂ)) X = ((‖matrixTensor g X‖ : ℝ) : ℂ) := by
  simp [matrixTensor, norm_prod]

/- English proof (translation)
Establish `h` using `(isSchwartzBruhat_iff_comp_symm Φ).1 hΦ`. Rewrite `h` using `[localSchwartzBruhatPi_eq_span]`. Set `L : ((Fin n × Fin n → F) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin n) F → ℂ)` to `LinearMap.funLeft ℂ ℂ (matrixCoordHomeomorph (Fin n) F)`. Establish `hm` using `Submodule.mem_map_of_mem (f := L) h`. Rewrite `hm` using `[Submodule.map_span, ← Set.range_comp]`.

Establish `e1 : L (Φ ∘ (matrixCoordHomeomorph (Fin n) F).symm) = Φ`. Use function extensionality and compare the values at `X`. Simplify using `[L, LinearMap.funLeft_apply]`. Establish `e2 : (⇑L ∘ fun p : ℤ × (Fin n × Fin n → F) => localTensor fun i => cosetInd (LocalField.valBall F p.1) (p.2 i)) = fun p => matrixTensor fun ij => cosetInd (LocalField.valBall F p.1) (p.2 ij)`. Use function extensionality and compare the values at `p X`.

Both sides reduce to the same expression. Rewrite `hm` using `[e1, e2]`. Conclude with `hm`.
-/
theorem mem_span_matrixTensor {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    Φ ∈ Submodule.span ℂ (Set.range fun p : ℤ × (Fin n × Fin n → F) =>
      matrixTensor fun ij => cosetInd (LocalField.valBall F p.1) (p.2 ij)) := by
  have h := (isSchwartzBruhat_iff_comp_symm Φ).1 hΦ
  rw [localSchwartzBruhatPi_eq_span] at h
  let L : ((Fin n × Fin n → F) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin n) F → ℂ) :=
    LinearMap.funLeft ℂ ℂ (matrixCoordHomeomorph (Fin n) F)
  have hm := Submodule.mem_map_of_mem (f := L) h
  rw [Submodule.map_span, ← Set.range_comp] at hm
  have e1 : L (Φ ∘ (matrixCoordHomeomorph (Fin n) F).symm) = Φ := by
    funext X
    simp [L, LinearMap.funLeft_apply]
  have e2 : (⇑L ∘ fun p : ℤ × (Fin n × Fin n → F) =>
      localTensor fun i => cosetInd (LocalField.valBall F p.1) (p.2 i)) =
      fun p => matrixTensor fun ij => cosetInd (LocalField.valBall F p.1) (p.2 ij) := by
    funext p X
    rfl
  rw [e1, e2] at hm
  exact hm

section Unip

variable [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)

variable (β) in

def unipMeasure : Measure (UnipotentIndex n β → F) :=
  Measure.pi fun _ => LocalField.selfDualMeasure ψ

instance : (unipMeasure β ψ).IsAddHaarMeasure := by
  unfold unipMeasure
  infer_instance

variable (β) in

def tensorConst (g : Fin n × Fin n → F → ℂ) : ℂ :=
  (∏ s : UnipotentIndex n β,
    LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g s.1) 0) *
      ∏ ij : Fin n × Fin n, if β ij.2 < β ij.1 then g ij 0 else 1

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [BorelSpace F] in

/- English proof (translation)
Rewrite using `[prod_subtype_eq_ite (fun ij : Fin n × Fin n => ¬ β ij.1 < β ij.2) fun ij => g ij (X ij.1 ij.2), leviTensor, prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 = β ij.2) fun ij => g ij (X ij.1 ij.2), ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun ij _ => ?_` and prove the remaining obligations. Break down `lt_trichotomy (β ij.1) (β ij.2) with h | h | h` into its components or cases. Simplify using `[h, h.ne, not_lt.2 h.le]`. Simplify using `[h]`.

Simplify using `[h, h.ne', not_lt.2 h.le, hX ij.1 ij.2 h.ne']`.
-/
theorem prod_not_unip_eq {X : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, β i ≠ β j → X i j = 0)
    (g : Fin n × Fin n → F → ℂ) :
    ∏ s : {ij : Fin n × Fin n // ¬ β ij.1 < β ij.2}, g s.1 (X s.1.1 s.1.2) =
      leviTensor β (fun s => g s.1) X * ∏ ij : Fin n × Fin n, if β ij.2 < β ij.1 then g ij 0 else 1 := by
  classical
  rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => ¬ β ij.1 < β ij.2) fun ij => g ij (X ij.1 ij.2),
    leviTensor, prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 = β ij.2)
      fun ij => g ij (X ij.1 ij.2), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ij _ => ?_
  rcases lt_trichotomy (β ij.1) (β ij.2) with h | h | h
  · simp [h, h.ne, not_lt.2 h.le]
  · simp [h]
  · simp [h, h.ne', not_lt.2 h.le, hX ij.1 ij.2 h.ne']

/- English proof (translation)
Establish `hsplit : ∀ u : UnipotentIndex n β → F, matrixTensor g (X + unipMatrix F u) = (∏ s : {ij : Fin n × Fin n // ¬ β ij.1 < β ij.2}, g s.1 (X s.1.1 s.1.2)) * ∏ s : UnipotentIndex n β, g s.1 (u s)`. Introduce `u`. Rewrite using `[matrixTensor, ← Fintype.prod_subtype_mul_prod_subtype (fun ij : Fin n × Fin n => β ij.1 < β ij.2), mul_comm]`. Use `congr 1`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.add_apply, unipMatrix_apply_of_not_lt u s.2, add_zero]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.add_apply, hX _ _ (ne_of_lt s.2), zero_add, unipMatrix_apply_of_lt u s.2]`. Repeatedly rewrite using `[hsplit]`. Rewrite using `[integral_const_mul, unipMeasure, integral_fintype_prod_eq_prod (f := fun (s : UnipotentIndex n β) x => g s.1 x), prod_not_unip_eq hX, tensorConst]`.

Establish `h0 : ∀ s : UnipotentIndex n β, ∫ x, g s.1 x ∂LocalField.selfDualMeasure ψ = LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g s.1) 0`. Introduce `s`. Simplify using `[LocalField.localFourier]`. Repeatedly rewrite using `[h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_matrixTensor_add_unip (g : Fin n × Fin n → F → ℂ)
    {X : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, β i ≠ β j → X i j = 0) :
    ∫ u, matrixTensor g (X + unipMatrix F u) ∂unipMeasure β ψ =
      tensorConst β ψ g * leviTensor β (fun s => g s.1) X := by
  classical
  have hsplit : ∀ u : UnipotentIndex n β → F, matrixTensor g (X + unipMatrix F u) =
      (∏ s : {ij : Fin n × Fin n // ¬ β ij.1 < β ij.2}, g s.1 (X s.1.1 s.1.2)) *
        ∏ s : UnipotentIndex n β, g s.1 (u s) := by
    intro u
    rw [matrixTensor, ← Fintype.prod_subtype_mul_prod_subtype
      (fun ij : Fin n × Fin n => β ij.1 < β ij.2), mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun s _ => ?_
      rw [Matrix.add_apply, unipMatrix_apply_of_not_lt u s.2, add_zero]
    · refine Finset.prod_congr rfl fun s _ => ?_
      rw [Matrix.add_apply, hX _ _ (ne_of_lt s.2), zero_add, unipMatrix_apply_of_lt u s.2]
  simp_rw [hsplit]
  rw [integral_const_mul, unipMeasure,
    integral_fintype_prod_eq_prod (f := fun (s : UnipotentIndex n β) x => g s.1 x),
    prod_not_unip_eq hX, tensorConst]
  have h0 : ∀ s : UnipotentIndex n β, ∫ x, g s.1 x ∂LocalField.selfDualMeasure ψ =
      LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g s.1) 0 := by
    intro s
    simp [LocalField.localFourier]
  simp_rw [h0]
  ring

/- English proof (translation)
Rewrite using `[localMatrixFourier_eq]`. Establish `: matrixTensor g ∘ (matrixCoordHomeomorph (Fin n) F).symm = localTensor g`. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression. Rewrite using `[this, localFourierPi_localTensor]`.

Both sides reduce to the same expression.
-/
theorem localMatrixFourier_matrixTensor (g : Fin n × Fin n → F → ℂ) (Y : Matrix (Fin n) (Fin n) F) :
    localMatrixFourier ψ (matrixTensor g) Y = ∏ ij : Fin n × Fin n,
      LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij) (Y ij.2 ij.1) := by
  rw [localMatrixFourier_eq]
  have : matrixTensor g ∘ (matrixCoordHomeomorph (Fin n) F).symm = localTensor g := by
    funext x
    rfl
  rw [this, localFourierPi_localTensor]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `Z`. Rewrite using `[localMatrixFourier_matrixTensor, matrixTensor]`. Conclude with `Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl`.
-/
theorem localMatrixFourier_matrixTensor_eq (g : Fin n × Fin n → F → ℂ) :
    localMatrixFourier ψ (matrixTensor g) = matrixTensor fun ij =>
      LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij.swap) := by
  funext Z
  rw [localMatrixFourier_matrixTensor, matrixTensor]
  exact Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl

omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Rewrite using `[leviTensor]`. Set `e : LeviIndex n β ≃ LeviIndex n β` to `{ toFun := fun s => ⟨s.1.swap, s.2.symm⟩ invFun := fun s => ⟨s.1.swap, s.2.symm⟩ left_inv := fun s => rfl right_inv := fun s => rfl }`. Conclude with `Fintype.prod_equiv e _ _ fun s => rfl`.
-/
theorem leviTensor_swap_eq (h : Fin n × Fin n → F → ℂ) (Y : Matrix (Fin n) (Fin n) F) :
    leviTensor β (fun s => h s.1.swap) Y = ∏ s : LeviIndex n β, h s.1 (Y s.1.2 s.1.1) := by
  rw [leviTensor]
  let e : LeviIndex n β ≃ LeviIndex n β :=
    { toFun := fun s => ⟨s.1.swap, s.2.symm⟩
      invFun := fun s => ⟨s.1.swap, s.2.symm⟩
      left_inv := fun s => rfl
      right_inv := fun s => rfl }
  exact Fintype.prod_equiv e _ _ fun s => rfl

/- English proof (translation)
The claim follows from `leviTensor_swap_eq (fun ij => LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij)) Y`.
-/
theorem leviTensor_swap_eq_hat (g : Fin n × Fin n → F → ℂ) (Y : Matrix (Fin n) (Fin n) F) :
    leviTensor β (fun s => LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g s.1.swap)) Y =
      leviTensorHat β ψ (fun s => g s.1) Y :=
  leviTensor_swap_eq (fun ij => LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij)) Y

/- English proof (translation)
Establish `h` using `integral_matrixTensor_add_unip ψ (fun ij x => ((‖g ij x‖ : ℝ) : ℂ)) hX`. Rewrite `h` using `[matrixTensor_norm]`. Rewrite `h` using `[integral_complex_ofReal]`. Establish `h2` using `congrArg (‖·‖) h`. Simplify using `only [Complex.norm_real, norm_mul] at h2`.

Rewrite `h2` using `[Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]`. Rewrite using `[h2]`. Use `congr 1`. Simplify using `[leviTensor, norm_prod]`.
-/
theorem integral_norm_matrixTensor_add_unip (g : Fin n × Fin n → F → ℂ)
    {X : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, β i ≠ β j → X i j = 0) :
    ∫ u, ‖matrixTensor g (X + unipMatrix F u)‖ ∂unipMeasure β ψ =
      ‖tensorConst β ψ (fun ij x => ((‖g ij x‖ : ℝ) : ℂ))‖ * ‖leviTensor β (fun s => g s.1) X‖ := by
  have h := integral_matrixTensor_add_unip ψ (fun ij x => ((‖g ij x‖ : ℝ) : ℂ)) hX
  simp_rw [matrixTensor_norm] at h
  rw [integral_complex_ofReal] at h
  have h2 := congrArg (‖·‖) h
  simp only [Complex.norm_real, norm_mul] at h2
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at h2
  rw [h2]
  congr 1
  simp [leviTensor, norm_prod]

variable {ψ} in

/- English proof (translation)
Use `set g' : Fin n × Fin n → F → ℂ := fun ij => LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij.swap)`. Use `⟨‖tensorConst β ψ (fun ij x => ((‖g' ij x‖ : ℝ) : ℂ))‖, norm_nonneg _, fun hY => ?_⟩` and prove the remaining obligations. Rewrite using `[localMatrixFourier_matrixTensor_eq, integral_norm_matrixTensor_add_unip ψ g' hY, leviTensor_swap_eq_hat]`.
-/
theorem integral_norm_fourier_matrixTensor_add_unip (g : Fin n × Fin n → F → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Y : Matrix (Fin n) (Fin n) F}, (∀ i j, β i ≠ β j → Y i j = 0) →
      ∫ u, ‖localMatrixFourier ψ (matrixTensor g) (Y + unipMatrix F u)‖ ∂unipMeasure β ψ =
        C * ‖leviTensorHat β ψ (fun s => g s.1) Y‖ := by
  set g' : Fin n × Fin n → F → ℂ := fun ij =>
    LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij.swap)
  refine ⟨‖tensorConst β ψ (fun ij x => ((‖g' ij x‖ : ℝ) : ℂ))‖, norm_nonneg _, fun hY => ?_⟩
  rw [localMatrixFourier_matrixTensor_eq, integral_norm_matrixTensor_add_unip ψ g' hY,
    leviTensor_swap_eq_hat]

variable {ψ} in

/- English proof (translation)
Use `set gh : Fin n × Fin n → F → ℂ := fun ij => LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij) with hgh`. Use `set g' : Fin n × Fin n → F → ℂ := fun ij => gh ij.swap with hg'`. Establish `hT : ∀ Z, localMatrixFourier ψ (matrixTensor g) Z = matrixTensor g' Z`. Introduce `Z`. Rewrite using `[localMatrixFourier_matrixTensor, matrixTensor]`.

Conclude with `Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl`. Repeatedly rewrite using `[hT]`. Rewrite using `[integral_matrixTensor_add_unip ψ g' hY]`. Use `congr 1`. Establish `hinv : ∀ ij : Fin n × Fin n, LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g' ij) 0 = g ij.swap 0`.

Introduce `ij`. Rewrite using `[hg', hgh]`. Simplify using `only`. Rewrite using `[LocalField.localFourier_localFourier_selfDual hψ hψ1 (hg _), neg_zero]`. Rewrite using `[tensorConst, tensorConst]`.

Repeatedly rewrite using `[hinv]`. Rewrite using `[mul_comm]`. Use `congr 1`. Rewrite using `[prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 < β ij.2) fun ij => gh ij 0]`. Conclude with `Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl`.

Rewrite using `[prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 < β ij.2) fun ij => g ij.swap 0]`. Conclude with `(Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl).symm`. Rewrite using `[leviTensor, leviTensorHat]`. Set `e : LeviIndex n β ≃ LeviIndex n β` to `{ toFun := fun s => ⟨s.1.swap, s.2.symm⟩ invFun := fun s => ⟨s.1.swap, s.2.symm⟩ left_inv := fun s => rfl right_inv := fun s => rfl }`. Conclude with `Fintype.prod_equiv e _ _ fun s => rfl`.
-/
theorem integral_fourier_matrixTensor_add_unip (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {g : Fin n × Fin n → F → ℂ} (hg : ∀ ij, g ij ∈ LocalField.schwartzBruhat F)
    {Y : Matrix (Fin n) (Fin n) F} (hY : ∀ i j, β i ≠ β j → Y i j = 0) :
    ∫ u, localMatrixFourier ψ (matrixTensor g) (Y + unipMatrix F u) ∂unipMeasure β ψ =
      tensorConst β ψ g * leviTensorHat β ψ (fun s => g s.1) Y := by
  classical
  set gh : Fin n × Fin n → F → ℂ := fun ij =>
    LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij) with hgh
  set g' : Fin n × Fin n → F → ℂ := fun ij => gh ij.swap with hg'
  have hT : ∀ Z, localMatrixFourier ψ (matrixTensor g) Z = matrixTensor g' Z := by
    intro Z
    rw [localMatrixFourier_matrixTensor, matrixTensor]
    exact Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl
  simp_rw [hT]
  rw [integral_matrixTensor_add_unip ψ g' hY]
  congr 1
  · have hinv : ∀ ij : Fin n × Fin n,
        LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g' ij) 0 = g ij.swap 0 := by
      intro ij
      rw [hg', hgh]
      simp only
      rw [LocalField.localFourier_localFourier_selfDual hψ hψ1 (hg _), neg_zero]
    rw [tensorConst, tensorConst]
    simp_rw [hinv]
    rw [mul_comm]
    congr 1
    · rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 < β ij.2) fun ij => gh ij 0]
      exact Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl
    · rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 < β ij.2)
        fun ij => g ij.swap 0]
      exact (Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl).symm
  · rw [leviTensor, leviTensorHat]
    let e : LeviIndex n β ≃ LeviIndex n β :=
      { toFun := fun s => ⟨s.1.swap, s.2.symm⟩
        invFun := fun s => ⟨s.1.swap, s.2.symm⟩
        left_inv := fun s => rfl
        right_inv := fun s => rfl }
    exact Fintype.prod_equiv e _ _ fun s => rfl

end Unip

section Translate

variable [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Take `⟨h₁, h₂⟩` from `(mem_integralGL_iff F n).1 hy`. Establish `key : ∀ (A B : Matrix (Fin n) (Fin n) F), (∀ i j, A i j ∈ 𝒪[F]) → (∀ i j, B i j ∈ 𝒪[F]) → ∀ i j, (A * B) i j ∈ 𝒪[F]` using `fun A B hA hB i j => by`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)`. Use `⟨fun h i j => ?_, fun h => key _ _ h h₁⟩` and prove the remaining obligations.

Use `key _ _ h h₂ i j` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Then use the resulting hypothesis.
-/
theorem mul_mem_integer_iff {y : GL (Fin n) F} (hy : y ∈ integralGL F n)
    (X : Matrix (Fin n) (Fin n) F) :
    (∀ i j, (X * (y : Matrix (Fin n) (Fin n) F)) i j ∈ 𝒪[F]) ↔ ∀ i j, X i j ∈ 𝒪[F] := by
  obtain ⟨h₁, h₂⟩ := (mem_integralGL_iff F n).1 hy
  have key : ∀ (A B : Matrix (Fin n) (Fin n) F), (∀ i j, A i j ∈ 𝒪[F]) → (∀ i j, B i j ∈ 𝒪[F]) →
      ∀ i j, (A * B) i j ∈ 𝒪[F] := fun A B hA hB i j => by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)
  refine ⟨fun h i j => ?_, fun h => key _ _ h h₁⟩
  have := key _ _ h h₂ i j
  rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this

def mulRightEquiv (y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F ≃ₜ+ Matrix (Fin n) (Fin n) F where
  toFun X := X * (y : Matrix (Fin n) (Fin n) F)
  invFun X := X * ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  left_inv X := by simp [Matrix.mul_assoc]
  right_inv X := by simp [Matrix.mul_assoc]
  map_add' X Y := Matrix.add_mul X Y _
  continuous_toFun := continuous_id.matrix_mul continuous_const
  continuous_invFun := continuous_id.matrix_mul continuous_const

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulRightEquiv_apply (y : GL (Fin n) F) (X : Matrix (Fin n) (Fin n) F) :
    mulRightEquiv y X = X * (y : Matrix (Fin n) (Fin n) F) := rfl

/- English proof (translation)
Use `set μ : Measure (Matrix (Fin n) (Fin n) F) := matrixMeasure (LocalField.selfDualMeasure ψ) with hμ`. Establish `hH : (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => LocalField.selfDualMeasure ψ : Measure (Fin n → Fin n → F)).IsAddHaarMeasure`. Establish `: (Measure.pi fun _ : Fin n => LocalField.selfDualMeasure ψ).IsAddHaarMeasure` using `inferInstance`. Use `infer_instance`. Establish `: μ.IsAddHaarMeasure` using `hH`.

Use `set e := mulRightEquiv y`. Establish `hmap : (μ.map e).IsAddHaarMeasure` using `e.isAddHaarMeasure_map μ`. Establish `hsmul` using `Measure.isAddLeftInvariant_eq_smul (μ.map e) μ`. Use `set B : Set (Matrix (Fin n) (Fin n) F) := Set.univ.pi fun _ => Set.univ.pi fun _ => (LocalField.valBall F 0 : Set F) with hB`. Establish `hBo : IsOpen B` using `isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => LocalField.isOpen_valBall 0`.

Establish `hBc : IsCompact B` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => LocalField.isCompact_valBall 0`. Establish `hmemB : ∀ X, X ∈ B ↔ ∀ i j, X i j ∈ 𝒪[F]`. Introduce `X`. Rewrite using `[hB]`. Prove the components needed by the constructor for the conclusion.

Introduce `h i j`. Conclude with `LocalField.mem_valBall_zero_iff.1 (h i (Set.mem_univ _) j (Set.mem_univ _))`. Introduce `h i _ j _`. Conclude with `LocalField.mem_valBall_zero_iff.2 (h i j)`. Establish `hpre : e ⁻¹' B = B`.

Use extensionality with `X`. Rewrite using `[Set.mem_preimage, hmemB, hmemB]`. Conclude with `mul_mem_integer_iff hy X`. Establish `h0 : μ B ≠ 0` using `hBo.measure_ne_zero μ ⟨0, fun _ _ _ _ => by simp [zero_mem]⟩`. Establish `ht : μ B ≠ ⊤` using `hBc.measure_lt_top.ne`.

Establish `hc : Measure.addHaarScalarFactor (μ.map e) μ = 1`. Establish `h1` using `congrArg (fun m : Measure (Matrix (Fin n) (Fin n) F) => m B) hsmul`. Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1`. Establish `hme : Measurable e` using `e.continuous.measurable`. Rewrite `h1` using `[Measure.map_apply hme hBo.measurableSet, hpre]`.

Establish `h2 : (Measure.addHaarScalarFactor (μ.map e) μ : ENNReal) * μ B = 1 * μ B`. Rewrite using `[one_mul, ← h1]`. Conclude with `(ENNReal.mul_left_inj h0 ht).1 h2` after adjusting the coercions. Use `⟨e.continuous.measurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hsmul, hc, one_smul]`.
-/
theorem measurePreserving_mul_right {y : GL (Fin n) F} (hy : y ∈ integralGL F n) :
    MeasurePreserving (mulRightEquiv y)
      (matrixMeasure (LocalField.selfDualMeasure ψ)) (matrixMeasure (LocalField.selfDualMeasure ψ)) := by
  set μ : Measure (Matrix (Fin n) (Fin n) F) := matrixMeasure (LocalField.selfDualMeasure ψ) with hμ
  have hH : (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n =>
      LocalField.selfDualMeasure ψ : Measure (Fin n → Fin n → F)).IsAddHaarMeasure := by
    have : (Measure.pi fun _ : Fin n => LocalField.selfDualMeasure ψ).IsAddHaarMeasure :=
      inferInstance
    infer_instance
  have : μ.IsAddHaarMeasure := hH
  set e := mulRightEquiv y
  have hmap : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hsmul := Measure.isAddLeftInvariant_eq_smul (μ.map e) μ
  set B : Set (Matrix (Fin n) (Fin n) F) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => (LocalField.valBall F 0 : Set F) with hB
  have hBo : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => LocalField.isOpen_valBall 0
  have hBc : IsCompact B := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    LocalField.isCompact_valBall 0
  have hmemB : ∀ X, X ∈ B ↔ ∀ i j, X i j ∈ 𝒪[F] := by
    intro X
    rw [hB]
    constructor
    · intro h i j
      exact LocalField.mem_valBall_zero_iff.1 (h i (Set.mem_univ _) j (Set.mem_univ _))
    · intro h i _ j _
      exact LocalField.mem_valBall_zero_iff.2 (h i j)
  have hpre : e ⁻¹' B = B := by
    ext X
    rw [Set.mem_preimage, hmemB, hmemB]
    exact mul_mem_integer_iff hy X
  have h0 : μ B ≠ 0 := hBo.measure_ne_zero μ ⟨0, fun _ _ _ _ => by simp [zero_mem]⟩
  have ht : μ B ≠ ⊤ := hBc.measure_lt_top.ne
  have hc : Measure.addHaarScalarFactor (μ.map e) μ = 1 := by
    have h1 := congrArg (fun m : Measure (Matrix (Fin n) (Fin n) F) => m B) hsmul
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    have hme : Measurable e := e.continuous.measurable
    rw [Measure.map_apply hme hBo.measurableSet, hpre] at h1
    have h2 : (Measure.addHaarScalarFactor (μ.map e) μ : ENNReal) * μ B = 1 * μ B := by
      rw [one_mul, ← h1]
    exact_mod_cast (ENNReal.mul_left_inj h0 ht).1 h2
  refine ⟨e.continuous.measurable, ?_⟩
  rw [hsmul, hc, one_smul]

/- English proof (translation)
Establish `hm` using `measurePreserving_mul_right ψ hy`. Establish `he : MeasurableEmbedding (mulRightEquiv y)` using `(mulRightEquiv y).toHomeomorph.measurableEmbedding`. Rewrite using `[localMatrixFourier, localMatrixFourier]`. Establish `key : ∀ X : Matrix (Fin n) (Fin n) F, Φ (X * (y : Matrix (Fin n) (Fin n) F)) * (ψ (trace (X * Z)) : ℂ) = (fun W => Φ W * (ψ (trace (W * (((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Z))) : ℂ)) (mulRightEquiv y X)`. Introduce `X`.

Simplify using `only [mulRightEquiv_apply]`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (y : Matrix (Fin n) (Fin n) F), ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Repeatedly rewrite using `[key]`. Conclude with `hm.integral_comp he (fun W => Φ W * (ψ (trace (W * (((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Z))) : ℂ))`.
-/
theorem localMatrixFourier_mul_right (Φ : Matrix (Fin n) (Fin n) F → ℂ) {y : GL (Fin n) F}
    (hy : y ∈ integralGL F n) (Z : Matrix (Fin n) (Fin n) F) :
    localMatrixFourier ψ (fun X => Φ (X * (y : Matrix (Fin n) (Fin n) F))) Z =
      localMatrixFourier ψ Φ (((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Z) := by
  have hm := measurePreserving_mul_right ψ hy
  have he : MeasurableEmbedding (mulRightEquiv y) :=
    (mulRightEquiv y).toHomeomorph.measurableEmbedding
  rw [localMatrixFourier, localMatrixFourier]
  have key : ∀ X : Matrix (Fin n) (Fin n) F,
      Φ (X * (y : Matrix (Fin n) (Fin n) F)) * (ψ (trace (X * Z)) : ℂ) =
        (fun W => Φ W * (ψ (trace (W * (((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Z))) :
          ℂ)) (mulRightEquiv y X) := by
    intro X
    simp only [mulRightEquiv_apply]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (y : Matrix (Fin n) (Fin n) F), ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]
  simp_rw [key]
  exact hm.integral_comp he (fun W => Φ W *
    (ψ (trace (W * (((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Z))) : ℂ))

end Translate

end GodementJacquet

end GroundTheory.Automorphic
