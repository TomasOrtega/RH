import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.TransposeMulBlockDiagMul
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.CardEqOfMulEqOne

noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
open Formalism.L2.Th1.Top.FrP Jac

set_option maxHeartbeats 400000 in
/- English proof (translation)
Introduce `l _ dK σ δ h5 hld hin hσ hδ hσδ n _ _ M₁ M₂ R₁ R₂ c hc hGram hmv`. Use `set S := setup h5 dK hld hin σ hσ δ hδ hσδ with hS`. Establish `hSσ : S.σ = σ` using `rfl`. Use `set M := lmat δ M₁ M₂ with hM`. Use `set Mb := lmat δ M₁ (-M₂) with hMb`.

Establish `hMσ : M.map σ = Mb` using `lmat_map_σ σ δ hσδ M₁ M₂`. Establish `hMbσ : Mb.map σ = M` using `by rw [hMb, lmat_map_σ σ δ hσδ, neg_neg]`. Establish `hc0 : (c : MaximalUnramifiedExtension l) ≠ 0`. Establish `: c ≠ 0` using `by rintro rfl; simp at hc`. Conclude with `this` after adjusting the coercions.

Use `set H₀ : Matrix n n (MaximalUnramifiedExtension l) := (c : MaximalUnramifiedExtension l)⁻¹ • (lmat δ R₁ R₂).map σ with hH₀`. Establish `hE : Mbᵀ * bd4 H₀ * M = 1`. Establish `h1` using `congrArg (fun X => X.map σ) hGram`. Simplify using `only [Matrix.map_mul, transpose_map, blockDiag_map', hMσ, hMbσ] at h1`. Establish `h1' : ((c : MaximalUnramifiedExtension l) • (1 : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l))).map σ = (c : MaximalUnramifiedExtension l) • 1`.

Use `Matrix.ext fun x y => ?_` and prove the remaining obligations. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite `h1` using `[h1']`. Rewrite using `[hH₀, bd4_smul, Matrix.mul_smul, Matrix.smul_mul, h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]`.

Establish `hE2 : Mbᵀ * bd4 (H₀.map σ)ᵀ * M = 1`. Establish `h1` using `congrArg (fun X => (X.map σ)ᵀ) hE`. Simplify using `only [Matrix.map_mul, transpose_map, blockDiag_map', hMσ, hMbσ, transpose_mul, transpose_transpose, Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one, bd4_transpose] at h1`. Simplify `h1` using `[Matrix.mul_assoc]`. Use `set Z : Matrix n (Fin 4 × n) (MaximalUnramifiedExtension l) := what₂ M 0 with hZ`.

Use `set Zb : Matrix n (Fin 4 × n) (MaximalUnramifiedExtension l) := what₂ Mb 0 with hZb'`. Establish `hZb : Z.map σ = Zb` using `Matrix.ext fun i w => congrFun (congrFun hMσ (0, i)) w`. Establish `hZbσ : Zb.map σ = Z` using `Matrix.ext fun i w => congrFun (congrFun hMbσ (0, i)) w`. Establish `hZZ : Z * (Zbᵀ * H₀) = 1`. Establish `h1 : M * (Mbᵀ * bd4 H₀) = 1` using `mul_eq_one_comm.mp hE`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `congrFun (congrFun h1 (0, i)) (0, j)` as an intermediate fact. Rewrite `this` using `[← Matrix.mul_assoc, mul_bd4_apply]`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_apply]`. Simplify using `only [Matrix.one_apply, Prod.mk.injEq, true_and] at this`.

Rewrite using `[Matrix.one_apply]`. Simplify `this` using `[Matrix.mul_apply, hZ, hZb', what₂]`. Take `⟨Γ, hΓ⟩ : ∃ Γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l), Γ = Zbᵀ * H₀ * Z` from `⟨_, rfl⟩`. Use `choose U₁ U₂ hUint hUeq using hmv`. Use `set U : Fin 4 → Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l) := fun b => lmat δ (U₁ b) (U₂ b) with hU`.

Establish `hUO : ∀ b x y, U b x y ∈ S.O` using `fun b x y => lmat_mem (dK := dK) (hδ := hδ) (U₁ b) (U₂ b) (hUint b) x y`. Establish `hZc : ∀ b, what₂ M b = Z * U b`. Introduce `b`. Use `Matrix.ext fun i w => ?_` and prove the remaining obligations. Use `congrFun (congrFun (hUeq b) (0, i)) w` as an intermediate fact.

Rewrite `this` using `[blockShift_mul_apply, if_pos rfl]`. Conclude with `this`. Establish `hrowsN : ∀ b, what₂ (M * U 0) b = if b = 0 then Z else 0`. Introduce `b`. Use `Matrix.ext fun i w => ?_` and prove the remaining obligations.

Use `congrFun (congrFun (hUeq 0) (b, i)) w` as an intermediate fact. Rewrite `this` using `[blockShift_mul_apply]`. Rewrite using `[what₂, ← this]`. Apply the tactic sequence `split_ifs <;> rfl`. Establish `hΓU : Γ = ((U 0).map σ)ᵀ * U 0`.

Establish `hN : ((M * U 0).map σ)ᵀ * bd4 H₀ * (M * U 0) = ((U 0).map σ)ᵀ * U 0`. Rewrite using `[Matrix.map_mul, hMσ, transpose_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hE, Matrix.mul_one]`.

Rewrite using `[← hN, transpose_mul_blockDiag_mul, Fin.sum_univ_four]`. Establish `hr : ∀ b, what₂ ((M * U 0).map σ) b = (what₂ (M * U 0) b).map σ` using `fun b => rfl`. Simplify using `only [hr, hrowsN]`. Simplify using `[hZb, hΓ]`. Establish `hΓI : S.IntM Γ`.

Introduce `w w'`. Rewrite using `[hΓU, Matrix.mul_apply]`. Conclude with `S.O.sum_mem fun k _ => S.O.mul_mem (S.hσO _ (hUO 0 k w)) (hUO 0 k w')`. Establish `hΓH : S.Herm Γ`. Introduce `w w'`.

Rewrite using `[hΓU]`. Simplify using `only [hSσ, Matrix.mul_apply, transpose_apply, Matrix.map_apply, map_sum, map_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h` using `S.hσσ _ (hUO 0 k w)`. Rewrite `h` using `[hSσ]`.

Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hidem : Γ * Γ = Γ`. Combine the equalities or inequalities in the displayed calculation. Establish `hΓUM : S.UM Γ`.

Introduce `x hx hNU`. Use `choose y hyO hy using hNU`. Use `⟨y, hyO, ?_⟩` and prove the remaining obligations. Establish `hΓx : Γ *ᵥ x = S.p • y` using `funext fun i => by rw [hy i]; rfl`. Establish `h2 : Γ *ᵥ (Γ *ᵥ x) = Γ *ᵥ x` using `by rw [mulVec_mulVec, hidem]`.

Rewrite `h2` using `[hΓx, mulVec_smul]`. Rewrite using `[hΓx, h2]`. Take `⟨k, v, hvI, hvo, hvs⟩` from `S.jac Γ hΓI hΓH hΓUM`. Use `clear_value Z Zb H₀ M Mb`. Use `set A : Matrix (Fin 4 × n) (Fin k) (MaximalUnramifiedExtension l) := Matrix.of fun w c => v c w with hA`.

Establish `hAO : ∀ w c, A w c ∈ S.O` using `fun w c => hvI c w`. Establish `hAo : (A.map σ)ᵀ * Γ * A = 1`. Use `Matrix.ext fun c c' => ?_` and prove the remaining obligations. Rewrite using `[Matrix.one_apply, ← hvo c c']`. Simplify using `only [JSetup.hf, JSetup.cv, hSσ, dotProduct, mulVec, Matrix.mul_apply, transpose_apply, Matrix.map_apply, hA, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hAs : Γ * A * ((A.map σ)ᵀ * Γ) = Γ` using `by conv_rhs => rw [← hvs]`. Use `Matrix.ext fun w w' => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply, Matrix.sum_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [vecMulVec_apply, Matrix.mul_apply, mulVec, dotProduct, vecMul, JSetup.cv, hSσ, transpose_apply, Matrix.map_apply, hA, Matrix.of_apply]`. Take `⟨V, hV⟩ : ∃ V : Matrix n (Fin k) (MaximalUnramifiedExtension l), V = Z * A` from `⟨_, rfl⟩`. Take `⟨Ti₀, hTi₀⟩ : ∃ Ti₀ : Matrix (Fin k) n (MaximalUnramifiedExtension l), Ti₀ = (V.map σ)ᵀ * H₀` from `⟨_, rfl⟩`.

Establish `hVσ : V.map σ = Zb * A.map σ` using `by rw [hV, Matrix.map_mul, hZb]`. Establish `hTZ : Ti₀ * Z = (A.map σ)ᵀ * Γ`. Rewrite using `[hTi₀, hVσ, transpose_mul, hΓ]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hTV : Ti₀ * V = 1`.

Rewrite using `[hV, ← Matrix.mul_assoc, hTZ, hAo]`. Establish `hZΓ : Z * Γ = Z`. Combine the equalities or inequalities in the displayed calculation. Establish `hGZ : Zbᵀ * H₀ = Γ * (Zbᵀ * H₀)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hTi₀' : Ti₀ = (A.map σ)ᵀ * (Zbᵀ * H₀)` using `by rw [hTi₀, hVσ, transpose_mul, Matrix.mul_assoc]`. Establish `hVT : V * Ti₀ = 1`. Establish `s1 : V * Ti₀ = Z * A * ((A.map σ)ᵀ * (Zbᵀ * H₀))` using `by rw [hV, hTi₀']`. Establish `s2 : Z * A * ((A.map σ)ᵀ * (Zbᵀ * H₀)) = Z * Γ * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀)))` using `(congrArg (fun X => Z * A * ((A.map σ)ᵀ * X)) hGZ).trans (congrArg (fun X => X * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀)))) hZΓ.symm)`. Establish `s3 : Z * Γ * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀))) = Z * (Γ * A * ((A.map σ)ᵀ * Γ)) * (Zbᵀ * H₀)`.

Simplify using `only [Matrix.mul_assoc]`. Establish `s4 : Z * (Γ * A * ((A.map σ)ᵀ * Γ)) * (Zbᵀ * H₀) = 1` using `by rw [hAs, hZΓ, hZZ]`. Conclude with `s1.trans (s2.trans (s3.trans s4))`. Establish `hk : Fintype.card n = k` using `card_eq_of_mul_eq_one V Ti₀ hVT hTV`. Use `set e : Fin k ≃ n := (Fintype.equivFinOfCardEq hk).symm with he`.

Use `set T : Matrix n n (MaximalUnramifiedExtension l) := V.submatrix id e.symm with hT`. Use `set Ti : Matrix n n (MaximalUnramifiedExtension l) := Ti₀.submatrix e.symm id with hTi`. Establish `hTTi : T * Ti = 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `h1` using `congrFun (congrFun hVT i) j`.

Rewrite `h1` using `[Matrix.mul_apply]`. Rewrite using `[← h1, Matrix.mul_apply]`. Simplify using `only [hT, hTi, submatrix_apply, id_eq]`. Conclude with `Equiv.sum_comp e.symm (fun c => V i c * Ti₀ c j)`. Establish `hAσσ : (A.map σ).map σ = A` using `Matrix.ext fun w c => by`.

Establish `h` using `S.hσσ _ (hAO w c)`. Rewrite `h` using `[hSσ]`. Simplify using `using h`. Establish `hVσσ : (V.map σ).map σ = V` using `by rw [hVσ, Matrix.map_mul, hZbσ, hAσσ, hV]`. Establish `hTi₀σ : (Ti₀.map σ)ᵀ * Ti₀ = (H₀.map σ)ᵀ`.

Establish `h1 : (Ti₀.map σ)ᵀ = (H₀.map σ)ᵀ * V`. Rewrite using `[hTi₀, Matrix.map_mul, transpose_mul, transpose_map, transpose_transpose, hVσσ]`. Rewrite using `[h1, Matrix.mul_assoc, hVT, Matrix.mul_one]`. Establish `hTiσ : (Ti.map σ)ᵀ * Ti = (H₀.map σ)ᵀ`. Rewrite using `[← hTi₀σ]`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [hTi, Matrix.mul_apply, transpose_apply, Matrix.map_apply, submatrix_apply, id_eq]`. Conclude with `Equiv.sum_comp e.symm (fun c => σ (Ti₀ c i) * Ti₀ c j)`. Establish `hU1 : ((bd4 Ti * M).map σ)ᵀ * (bd4 Ti * M) = 1`. Rewrite using `[Matrix.map_mul, blockDiag_map', hMσ, transpose_mul, bd4_transpose]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [blockDiag_mul', hTiσ]; exact hE2`. Establish `hγ : ∀ b i w, (bd4 Ti * M) (b, i) w = ((A.map σ)ᵀ * Γ * U b) (e.symm i) w`. Introduce `b i w`.

Rewrite using `[blockDiag_mul_apply']`. Establish `h1 : (Ti * what₂ M b) i w = ∑ j, Ti i j * M (b, j) w` using `rfl`. Rewrite using `[← h1, hZc b, ← Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun w' _ => ?_` and prove the remaining obligations. Use `congr 1`.

Use `show (Ti₀ * Z) (e.symm i) w' = _`. Rewrite using `[hTZ]`. Establish `hγO : ∀ x y, (bd4 Ti * M) x y ∈ S.O`. Introduce and unpack `⟨b, i⟩ w`. Rewrite using `[hγ, Matrix.mul_apply]`.

Use `S.O.sum_mem fun w' _ => S.O.mul_mem ?_ (hUO b w' w)` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `S.O.sum_mem fun x _ => S.O.mul_mem ?_ (hΓI x w')` and prove the remaining obligations. Establish `h` using `S.hσO _ (hAO x (e.symm i))`. Rewrite `h` using `[hSσ]`.

Simplify using `using h`. Use `⟨T, Ti, hTTi, ?_⟩` and prove the remaining obligations. Unfold `IsUnitaryK`. Use `⟨fun a b => ⟨norm_le_one_of_mem (dK := dK) (hδ := hδ) (hγO a b), ?_⟩, fun a b => ?_⟩` and prove the remaining obligations. Establish `h` using `S.hσσ _ (hγO a b)`.

Rewrite `h` using `[hSσ]`. Then use the resulting hypothesis. Establish `h` using `congrFun (congrFun hU1 a) b`. Rewrite `h` using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [transpose_apply, Matrix.map_apply] at h`. Conclude with `h`.
-/
theorem local_core' : LocCore := by
  intro l _ dK σ δ h5 hld hin hσ hδ hσδ n _ _ M₁ M₂ R₁ R₂ c hc hGram hmv
  set S := setup h5 dK hld hin σ hσ δ hδ hσδ with hS
  have hSσ : S.σ = σ := rfl
  set M := lmat δ M₁ M₂ with hM
  set Mb := lmat δ M₁ (-M₂) with hMb
  have hMσ : M.map σ = Mb := lmat_map_σ σ δ hσδ M₁ M₂
  have hMbσ : Mb.map σ = M := by rw [hMb, lmat_map_σ σ δ hσδ, neg_neg]
  have hc0 : (c : MaximalUnramifiedExtension l) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; simp at hc
    exact_mod_cast this
  set H₀ : Matrix n n (MaximalUnramifiedExtension l) := (c : MaximalUnramifiedExtension l)⁻¹ • (lmat δ R₁ R₂).map σ with hH₀

  have hE : Mbᵀ * bd4 H₀ * M = 1 := by
    have h1 := congrArg (fun X => X.map σ) hGram
    simp only [Matrix.map_mul, transpose_map, blockDiag_map', hMσ, hMbσ] at h1
    have h1' : ((c : MaximalUnramifiedExtension l) • (1 : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l))).map σ = (c : MaximalUnramifiedExtension l) • 1 := by
      refine Matrix.ext fun x y => ?_
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [h1'] at h1
    rw [hH₀, bd4_smul, Matrix.mul_smul, Matrix.smul_mul, h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hE2 : Mbᵀ * bd4 (H₀.map σ)ᵀ * M = 1 := by
    have h1 := congrArg (fun X => (X.map σ)ᵀ) hE
    simp only [Matrix.map_mul, transpose_map, blockDiag_map', hMσ, hMbσ, transpose_mul, transpose_transpose,
      Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one, bd4_transpose] at h1
    simpa [Matrix.mul_assoc] using h1

  set Z : Matrix n (Fin 4 × n) (MaximalUnramifiedExtension l) := what₂ M 0 with hZ
  set Zb : Matrix n (Fin 4 × n) (MaximalUnramifiedExtension l) := what₂ Mb 0 with hZb'
  have hZb : Z.map σ = Zb := Matrix.ext fun i w => congrFun (congrFun hMσ (0, i)) w
  have hZbσ : Zb.map σ = Z := Matrix.ext fun i w => congrFun (congrFun hMbσ (0, i)) w
  have hZZ : Z * (Zbᵀ * H₀) = 1 := by
    have h1 : M * (Mbᵀ * bd4 H₀) = 1 := mul_eq_one_comm.mp hE
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun h1 (0, i)) (0, j)
    rw [← Matrix.mul_assoc, mul_bd4_apply] at this
    rw [← Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.one_apply, Prod.mk.injEq, true_and] at this
    rw [Matrix.one_apply]
    simpa [Matrix.mul_apply, hZ, hZb', what₂] using this
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l), Γ = Zbᵀ * H₀ * Z := ⟨_, rfl⟩

  choose U₁ U₂ hUint hUeq using hmv
  set U : Fin 4 → Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l) := fun b => lmat δ (U₁ b) (U₂ b) with hU
  have hUO : ∀ b x y, U b x y ∈ S.O := fun b x y => lmat_mem (dK := dK) (hδ := hδ) (U₁ b) (U₂ b) (hUint b) x y
  have hZc : ∀ b, what₂ M b = Z * U b := by
    intro b; refine Matrix.ext fun i w => ?_
    have := congrFun (congrFun (hUeq b) (0, i)) w
    rw [blockShift_mul_apply, if_pos rfl] at this
    exact this
  have hrowsN : ∀ b, what₂ (M * U 0) b = if b = 0 then Z else 0 := by
    intro b; refine Matrix.ext fun i w => ?_
    have := congrFun (congrFun (hUeq 0) (b, i)) w
    rw [blockShift_mul_apply] at this
    rw [what₂, ← this]
    split_ifs <;> rfl
  have hΓU : Γ = ((U 0).map σ)ᵀ * U 0 := by
    have hN : ((M * U 0).map σ)ᵀ * bd4 H₀ * (M * U 0) = ((U 0).map σ)ᵀ * U 0 := by
      rw [Matrix.map_mul, hMσ, transpose_mul]
      calc ((U 0).map σ)ᵀ * Mbᵀ * bd4 H₀ * (M * U 0) = ((U 0).map σ)ᵀ * (Mbᵀ * bd4 H₀ * M) * U 0 := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hE, Matrix.mul_one]
    rw [← hN, transpose_mul_blockDiag_mul, Fin.sum_univ_four]
    have hr : ∀ b, what₂ ((M * U 0).map σ) b = (what₂ (M * U 0) b).map σ := fun b => rfl
    simp only [hr, hrowsN]
    simp [hZb, hΓ]
  have hΓI : S.IntM Γ := by
    intro w w'
    rw [hΓU, Matrix.mul_apply]
    exact S.O.sum_mem fun k _ => S.O.mul_mem (S.hσO _ (hUO 0 k w)) (hUO 0 k w')
  have hΓH : S.Herm Γ := by
    intro w w'
    rw [hΓU]
    simp only [hSσ, Matrix.mul_apply, transpose_apply, Matrix.map_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := S.hσσ _ (hUO 0 k w)
    rw [hSσ] at h
    rw [h]
    ring
  have hidem : Γ * Γ = Γ := by
    calc Γ * Γ = Zbᵀ * H₀ * (Z * (Zbᵀ * H₀)) * Z := by simp only [hΓ, Matrix.mul_assoc]
      _ = Γ := by rw [hZZ, Matrix.mul_one, hΓ]
  have hΓUM : S.UM Γ := by
    intro x hx hNU
    choose y hyO hy using hNU
    refine ⟨y, hyO, ?_⟩
    have hΓx : Γ *ᵥ x = S.p • y := funext fun i => by rw [hy i]; rfl
    have h2 : Γ *ᵥ (Γ *ᵥ x) = Γ *ᵥ x := by rw [mulVec_mulVec, hidem]
    rw [hΓx, mulVec_smul] at h2
    rw [hΓx, h2]
  obtain ⟨k, v, hvI, hvo, hvs⟩ := S.jac Γ hΓI hΓH hΓUM
  clear_value Z Zb H₀ M Mb

  set A : Matrix (Fin 4 × n) (Fin k) (MaximalUnramifiedExtension l) := Matrix.of fun w c => v c w with hA
  have hAO : ∀ w c, A w c ∈ S.O := fun w c => hvI c w
  have hAo : (A.map σ)ᵀ * Γ * A = 1 := by
    refine Matrix.ext fun c c' => ?_
    rw [Matrix.one_apply, ← hvo c c']
    simp only [JSetup.hf, JSetup.cv, hSσ, dotProduct, mulVec, Matrix.mul_apply, transpose_apply,
      Matrix.map_apply, hA, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hAs : Γ * A * ((A.map σ)ᵀ * Γ) = Γ := by
    conv_rhs => rw [← hvs]
    refine Matrix.ext fun w w' => ?_
    rw [Matrix.mul_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [vecMulVec_apply, Matrix.mul_apply, mulVec, dotProduct, vecMul, JSetup.cv, hSσ, transpose_apply,
      Matrix.map_apply, hA, Matrix.of_apply]
  obtain ⟨V, hV⟩ : ∃ V : Matrix n (Fin k) (MaximalUnramifiedExtension l), V = Z * A := ⟨_, rfl⟩
  obtain ⟨Ti₀, hTi₀⟩ : ∃ Ti₀ : Matrix (Fin k) n (MaximalUnramifiedExtension l), Ti₀ = (V.map σ)ᵀ * H₀ := ⟨_, rfl⟩
  have hVσ : V.map σ = Zb * A.map σ := by rw [hV, Matrix.map_mul, hZb]
  have hTZ : Ti₀ * Z = (A.map σ)ᵀ * Γ := by
    rw [hTi₀, hVσ, transpose_mul, hΓ]; simp only [Matrix.mul_assoc]
  have hTV : Ti₀ * V = 1 := by
    rw [hV, ← Matrix.mul_assoc, hTZ, hAo]
  have hZΓ : Z * Γ = Z := by
    calc Z * Γ = Z * (Zbᵀ * H₀) * Z := by simp only [hΓ, Matrix.mul_assoc]
      _ = Z := by rw [hZZ, Matrix.one_mul]
  have hGZ : Zbᵀ * H₀ = Γ * (Zbᵀ * H₀) := by
    calc Zbᵀ * H₀ = Zbᵀ * H₀ * (Z * (Zbᵀ * H₀)) := by rw [hZZ, Matrix.mul_one]
      _ = Γ * (Zbᵀ * H₀) := by simp only [hΓ, Matrix.mul_assoc]
  have hTi₀' : Ti₀ = (A.map σ)ᵀ * (Zbᵀ * H₀) := by rw [hTi₀, hVσ, transpose_mul, Matrix.mul_assoc]
  have hVT : V * Ti₀ = 1 := by
    have s1 : V * Ti₀ = Z * A * ((A.map σ)ᵀ * (Zbᵀ * H₀)) := by rw [hV, hTi₀']
    have s2 : Z * A * ((A.map σ)ᵀ * (Zbᵀ * H₀)) = Z * Γ * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀))) :=
      (congrArg (fun X => Z * A * ((A.map σ)ᵀ * X)) hGZ).trans
        (congrArg (fun X => X * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀)))) hZΓ.symm)
    have s3 : Z * Γ * A * ((A.map σ)ᵀ * (Γ * (Zbᵀ * H₀))) = Z * (Γ * A * ((A.map σ)ᵀ * Γ)) * (Zbᵀ * H₀) := by
      simp only [Matrix.mul_assoc]
    have s4 : Z * (Γ * A * ((A.map σ)ᵀ * Γ)) * (Zbᵀ * H₀) = 1 := by rw [hAs, hZΓ, hZZ]
    exact s1.trans (s2.trans (s3.trans s4))

  have hk : Fintype.card n = k := card_eq_of_mul_eq_one V Ti₀ hVT hTV
  set e : Fin k ≃ n := (Fintype.equivFinOfCardEq hk).symm with he
  set T : Matrix n n (MaximalUnramifiedExtension l) := V.submatrix id e.symm with hT
  set Ti : Matrix n n (MaximalUnramifiedExtension l) := Ti₀.submatrix e.symm id with hTi
  have hTTi : T * Ti = 1 := by
    refine Matrix.ext fun i j => ?_
    have h1 := congrFun (congrFun hVT i) j
    rw [Matrix.mul_apply] at h1
    rw [← h1, Matrix.mul_apply]
    simp only [hT, hTi, submatrix_apply, id_eq]
    exact Equiv.sum_comp e.symm (fun c => V i c * Ti₀ c j)

  have hAσσ : (A.map σ).map σ = A := Matrix.ext fun w c => by
    have h := S.hσσ _ (hAO w c)
    rw [hSσ] at h
    simpa using h
  have hVσσ : (V.map σ).map σ = V := by rw [hVσ, Matrix.map_mul, hZbσ, hAσσ, hV]
  have hTi₀σ : (Ti₀.map σ)ᵀ * Ti₀ = (H₀.map σ)ᵀ := by
    have h1 : (Ti₀.map σ)ᵀ = (H₀.map σ)ᵀ * V := by
      rw [hTi₀, Matrix.map_mul, transpose_mul, transpose_map, transpose_transpose, hVσσ]
    rw [h1, Matrix.mul_assoc, hVT, Matrix.mul_one]
  have hTiσ : (Ti.map σ)ᵀ * Ti = (H₀.map σ)ᵀ := by
    rw [← hTi₀σ]
    refine Matrix.ext fun i j => ?_
    simp only [hTi, Matrix.mul_apply, transpose_apply, Matrix.map_apply, submatrix_apply, id_eq]
    exact Equiv.sum_comp e.symm (fun c => σ (Ti₀ c i) * Ti₀ c j)
  have hU1 : ((bd4 Ti * M).map σ)ᵀ * (bd4 Ti * M) = 1 := by
    rw [Matrix.map_mul, blockDiag_map', hMσ, transpose_mul, bd4_transpose]
    calc Mbᵀ * bd4 (Ti.map σ)ᵀ * (bd4 Ti * M) = Mbᵀ * (bd4 (Ti.map σ)ᵀ * bd4 Ti) * M := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [blockDiag_mul', hTiσ]; exact hE2

  have hγ : ∀ b i w, (bd4 Ti * M) (b, i) w = ((A.map σ)ᵀ * Γ * U b) (e.symm i) w := by
    intro b i w
    rw [blockDiag_mul_apply']
    have h1 : (Ti * what₂ M b) i w = ∑ j, Ti i j * M (b, j) w := rfl
    rw [← h1, hZc b, ← Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun w' _ => ?_
    congr 1
    show (Ti₀ * Z) (e.symm i) w' = _
    rw [hTZ]
  have hγO : ∀ x y, (bd4 Ti * M) x y ∈ S.O := by
    rintro ⟨b, i⟩ w
    rw [hγ, Matrix.mul_apply]
    refine S.O.sum_mem fun w' _ => S.O.mul_mem ?_ (hUO b w' w)
    rw [Matrix.mul_apply]
    refine S.O.sum_mem fun x _ => S.O.mul_mem ?_ (hΓI x w')
    have h := S.hσO _ (hAO x (e.symm i))
    rw [hSσ] at h
    simpa using h
  refine ⟨T, Ti, hTTi, ?_⟩
  unfold IsUnitaryK
  refine ⟨fun a b => ⟨norm_le_one_of_mem (dK := dK) (hδ := hδ) (hγO a b), ?_⟩, fun a b => ?_⟩
  · have h := S.hσσ _ (hγO a b)
    rwa [hSσ] at h
  · have h := congrFun (congrFun hU1 a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [transpose_apply, Matrix.map_apply] at h
    exact h

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
