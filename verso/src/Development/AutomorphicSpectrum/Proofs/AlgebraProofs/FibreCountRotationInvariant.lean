import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv

noncomputable section

/- English proof (translation)
Establish `h1` using `(measurePreserving_curry_matrix m n).symm (MeasurableEquiv.curry (Fin m) (Fin n) ℂ)`. Establish `h2` using `volume_measurePreserving_piCongrLeft (fun _ : Fin n × Fin m => ℂ) (Equiv.prodComm (Fin m) (Fin n))`. Establish `h3` using `measurePreserving_curry_matrix n m`. Establish `h4` using `h3.comp (h2.comp h1)`. Establish `h5 : (fun (π : Fin m → Fin n → ℂ) (j : Fin n) (i : Fin m) => π i j) = (MeasurableEquiv.curry (Fin n) (Fin m) ℂ) ∘ (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin m => ℂ) (Equiv.prodComm (Fin m) (Fin n))) ∘ (MeasurableEquiv.curry (Fin m) (Fin n) ℂ).symm`.

Use function extensionality and compare the values at `π j i`. Simplify using `only [MeasurableEquiv.coe_curry_symm, MeasurableEquiv.curry, Function.comp]`. Simplify using `only [MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Function.curry_apply, MeasurableEquiv.coe_piCongrLeft]`. Conclude with `(Equiv.piCongrLeft_apply_apply (fun _ : Fin n × Fin m => ℂ) (Equiv.prodComm (Fin m) (Fin n)) (Function.uncurry π) (i, j)).symm`. Rewrite using `[h5]`.

Conclude with `h4`.
-/
theorem measurePreserving_swapMat (m n : ℕ) :
    MeasurePreserving (fun (π : Fin m → Fin n → ℂ) (j : Fin n) (i : Fin m) => π i j)
      volume volume := by
  have h1 := (measurePreserving_curry_matrix m n).symm (MeasurableEquiv.curry (Fin m) (Fin n) ℂ)
  have h2 := volume_measurePreserving_piCongrLeft (fun _ : Fin n × Fin m => ℂ)
    (Equiv.prodComm (Fin m) (Fin n))
  have h3 := measurePreserving_curry_matrix n m
  have h4 := h3.comp (h2.comp h1)
  have h5 : (fun (π : Fin m → Fin n → ℂ) (j : Fin n) (i : Fin m) => π i j) =
      (MeasurableEquiv.curry (Fin n) (Fin m) ℂ) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin m => ℂ)
          (Equiv.prodComm (Fin m) (Fin n))) ∘
          (MeasurableEquiv.curry (Fin m) (Fin n) ℂ).symm := by
    funext π j i
    simp only [MeasurableEquiv.coe_curry_symm, MeasurableEquiv.curry, Function.comp]
    simp only [MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Function.curry_apply,
      MeasurableEquiv.coe_piCongrLeft]
    exact (Equiv.piCongrLeft_apply_apply (fun _ : Fin n × Fin m => ℂ)
      (Equiv.prodComm (Fin m) (Fin n)) (Function.uncurry π) (i, j)).symm
  rw [h5]
  exact h4

/- English proof (translation)
Rewrite using `[Matrix.mem_unitaryGroup_iff]`. Establish `h : star A * A = 1` using `Matrix.mem_unitaryGroup_iff'.1 hA`. Establish `h2 : (star A * A)ᵀ = 1` using `by rw [h, Matrix.transpose_one]`. Rewrite `h2` using `[Matrix.transpose_mul]`. Simplify `h2` using `[Matrix.star_eq_conjTranspose, Matrix.conjTranspose, Matrix.transpose_map]`.
-/
theorem transpose_mem_unitaryGroup' {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin m) ℂ) : Aᵀ ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.1 hA
  have h2 : (star A * A)ᵀ = 1 := by rw [h, Matrix.transpose_one]
  rw [Matrix.transpose_mul] at h2
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose, Matrix.transpose_map] using h2

def colAct {m n : ℕ} (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (π : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ :=
  fun i j => ∑ k, unitMat V i k * π k j

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `[colAct, Matrix.mul_apply]`.
-/
theorem colAct_eq_mul {m n : ℕ} (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (π : Fin m → Fin n → ℂ) :
    colAct V π = (unitMat V * (Matrix.of π : Matrix (Fin m) (Fin n) ℂ)) := by
  funext i j
  simp [colAct, Matrix.mul_apply]

/- English proof (translation)
Establish `h : unitMat V.symm * unitMat V = 1` using `by simpa using unitMat_mul_symm V.symm`. Rewrite using `[colAct_eq_mul, colAct_eq_mul]`. Use `show unitMat V.symm * (unitMat V * Matrix.of π) = π`. Rewrite using `[← Matrix.mul_assoc, h, Matrix.one_mul]`. Both sides reduce to the same expression.
-/
theorem colAct_symm_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ) :
    colAct V.symm (colAct V π) = π := by
  have h : unitMat V.symm * unitMat V = 1 := by simpa using unitMat_mul_symm V.symm
  rw [colAct_eq_mul, colAct_eq_mul]
  show unitMat V.symm * (unitMat V * Matrix.of π) = π
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `[colAct, Matrix.vecMul, dotProduct, mul_comm]`.
-/
theorem colAct_eq_swap {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ) :
    colAct V π = fun i j => ((fun k => π k j) ᵥ* (unitMat V)ᵀ) i := by
  funext i j
  simp [colAct, Matrix.vecMul, dotProduct, mul_comm]

/- English proof (translation)
Establish `h1 : MeasurePreserving (fun (ρ : Fin n → Fin m → ℂ) (j : Fin n) => ρ j ᵥ* (unitMat V)ᵀ) volume volume` using `volume_preserving_pi fun _ => measurePreserving_vecMul (transpose_mem_unitaryGroup' (unitMat_mem V))`. Establish `h2` using `(measurePreserving_swapMat n m).comp (h1.comp (measurePreserving_swapMat m n))`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `π`. Rewrite using `[colAct_eq_swap]`.

Both sides reduce to the same expression.
-/
theorem measurePreserving_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    MeasurePreserving (colAct (n := n) V) volume volume := by
  have h1 : MeasurePreserving (fun (ρ : Fin n → Fin m → ℂ) (j : Fin n) => ρ j ᵥ* (unitMat V)ᵀ)
      volume volume :=
    volume_preserving_pi fun _ =>
      measurePreserving_vecMul (transpose_mem_unitaryGroup' (unitMat_mem V))
  have h2 := (measurePreserving_swapMat n m).comp (h1.comp (measurePreserving_swapMat m n))
  convert h2 using 1
  funext π
  rw [colAct_eq_swap]
  rfl

def colActEquiv {m n : ℕ} (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    (Fin m → Fin n → ℂ) ≃ᵐ (Fin m → Fin n → ℂ) where
  toFun := colAct V
  invFun := colAct V.symm
  left_inv := colAct_symm_colAct V
  right_inv π := by simpa using colAct_symm_colAct V.symm π
  measurable_toFun := (measurePreserving_colAct V).measurable
  measurable_invFun := (measurePreserving_colAct V.symm).measurable

/- English proof (translation)
Simplify using `only [matGauss]`. Use `congr 3`. Rewrite using `[colAct_eq_swap, Finset.sum_comm]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Conclude with `sum_norm_sq_vecMul (transpose_mem_unitaryGroup' (unitMat_mem V)) (fun k => π k j)`.
-/
theorem matGauss_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ) :
    matGauss (colAct V π) = matGauss π := by
  simp only [matGauss]
  congr 3
  rw [colAct_eq_swap, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact sum_norm_sq_vecMul (transpose_mem_unitaryGroup' (unitMat_mem V)) (fun k => π k j)

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[unitary_apply_eq_sum]`. Simplify using `only [linProj, colAct]`. Repeatedly rewrite using `[Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem linProj_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : linProj (colAct V π) y = V (linProj π y) := by
  ext i
  rw [unitary_apply_eq_sum]
  simp only [linProj, colAct]
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [linProj, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem linProj_smul {m n : ℕ} (π : Fin m → Fin n → ℂ) (c : ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : linProj π (c • y) = c • linProj π y := by
  ext i
  simp only [linProj, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use `set c : ℂ := ((‖w‖ : ℝ) : ℂ) with hc`. Establish `hc0 : c ≠ 0`. Rewrite using `[hc]`. Conclude with `norm_ne_zero_iff.2 hw` after adjusting the coercions. Establish `himg : ptsOver S (colAct V π) (firstCoordVec (e + 1)) = (fun y => c⁻¹ • y) '' ptsOver S π w`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hzS, hz⟩`. Use `⟨c • z, ⟨hS z hzS c hc0, ?_⟩, by simp [smul_smul, hc0]⟩` and prove the remaining obligations. Apply `V.injective` to reduce the goal to its premises.

Rewrite using `[linProj_smul, map_smul, ← linProj_colAct, hz, hV]`. Introduce and unpack `⟨y, ⟨hyS, hy⟩, rfl⟩`. Use `⟨hS y hyS _ (inv_ne_zero hc0), ?_⟩` and prove the remaining obligations. Rewrite using `[linProj_smul, linProj_colAct, hy, hV, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Establish `hinj : Set.InjOn (fun y : EuclideanSpace ℂ (Fin n) => c⁻¹ • y) (ptsOver S π w)` using `(MulAction.injective₀ (inv_ne_zero hc0)).injOn`.

Simplify using `only [cntOver]`. Rewrite using `[himg, hinj.encard_image]`.
-/
theorem cntOver_colAct {n e : ℕ} {S : Set (EuclideanSpace ℂ (Fin n))} (hS : IsScaleStable S)
    {w : EuclideanSpace ℂ (Fin (e + 1))} (hw : w ≠ 0)
    (V : EuclideanSpace ℂ (Fin (e + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (e + 1)))
    (hV : V w = ((‖w‖ : ℝ) : ℂ) • firstCoordVec (e + 1)) (π : Fin (e + 1) → Fin n → ℂ) :
    cntOver S (colAct V π) (firstCoordVec (e + 1)) = cntOver S π w := by
  set c : ℂ := ((‖w‖ : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact_mod_cast norm_ne_zero_iff.2 hw
  have himg : ptsOver S (colAct V π) (firstCoordVec (e + 1)) =
      (fun y => c⁻¹ • y) '' ptsOver S π w := by
    ext z
    constructor
    · rintro ⟨hzS, hz⟩
      refine ⟨c • z, ⟨hS z hzS c hc0, ?_⟩, by simp [smul_smul, hc0]⟩
      apply V.injective
      rw [linProj_smul, map_smul, ← linProj_colAct, hz, hV]
    · rintro ⟨y, ⟨hyS, hy⟩, rfl⟩
      refine ⟨hS y hyS _ (inv_ne_zero hc0), ?_⟩
      rw [linProj_smul, linProj_colAct, hy, hV, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hinj : Set.InjOn (fun y : EuclideanSpace ℂ (Fin n) => c⁻¹ • y) (ptsOver S π w) :=
    (MulAction.injective₀ (inv_ne_zero hc0)).injOn
  simp only [cntOver]
  rw [himg, hinj.encard_image]

/- English proof (translation)
Introduce `n e S hS w hw T`. Take `⟨U, -, -, hU⟩` from `exists_unitary_leadCoordPlane (n := e + 1) (m := e + 1) (by omega) le_rfl ⊤ (by simp) w trivial`. Establish `hV : U.symm w = ((‖w‖ : ℝ) : ℂ) • firstCoordVec (e + 1)`. Rewrite using `[U.symm_apply_eq, hU]`. Establish `hemb : MeasurableEmbedding (colAct (n` using `n) U.symm) := (colActEquiv U.symm).measurableEmbedding`.

Establish `key` using `(measurePreserving_colAct (n := n) U.symm).lintegral_comp_emb hemb (fun π => matGauss π * T (cntOver S π (firstCoordVec (e + 1))))`. Use `Eq.trans ?_ key` and prove the remaining obligations. Use `lintegral_congr fun π => ?_` and prove the remaining obligations. Simplify using `only [matGauss_colAct, cntOver_colAct hS hw U.symm hV]`.
-/
theorem lintegral_matGauss_cntOver :
    ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S →
      ∀ (w : EuclideanSpace ℂ (Fin (e + 1))), w ≠ 0 → ∀ T : ℝ≥0∞ → ℝ≥0∞,
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π w) =
          ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  intro n e S hS w hw T
  obtain ⟨U, -, -, hU⟩ := exists_unitary_leadCoordPlane (n := e + 1) (m := e + 1) (by omega) le_rfl
    ⊤ (by simp) w trivial
  have hV : U.symm w = ((‖w‖ : ℝ) : ℂ) • firstCoordVec (e + 1) := by
    rw [U.symm_apply_eq, hU]
  have hemb : MeasurableEmbedding (colAct (n := n) U.symm) :=
    (colActEquiv U.symm).measurableEmbedding
  have key := (measurePreserving_colAct (n := n) U.symm).lintegral_comp_emb hemb
    (fun π => matGauss π * T (cntOver S π (firstCoordVec (e + 1))))
  refine Eq.trans ?_ key
  refine lintegral_congr fun π => ?_
  simp only [matGauss_colAct, cntOver_colAct hS hw U.symm hV]

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv
