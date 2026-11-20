import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExpCut

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Metric Formalism.MainNotions.S Formalism.MainNotions.S.Gauge

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

def unrLin (n : ℕ) : EuclideanSpace ℝ (Fin n × Fin n × Bool) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := unrealify
  map_add' x y := by funext i j; apply Complex.ext <;> simp [unrealify]
  map_smul' c x := by funext i j; apply Complex.ext <;> simp [unrealify]

def reLin (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n × Bool) where
  toFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  map_add' X Y := by
    ext q; rcases q with ⟨i, j, b⟩; cases b <;> simp [realifyFun]
  map_smul' c X := by
    ext q; rcases q with ⟨i, j, b⟩; cases b <;> simp [realifyFun]

/- English proof (translation)
Use extensionality with `q`. Break down `q with ⟨i, j, b⟩` into its components or cases. Apply the tactic sequence `cases b <;> simp [reLin, unrLin, realifyFun, unrealify, LinearMap.coe_mk, AddHom.coe_mk] <;> rfl`.
-/
theorem re_unr (n : ℕ) (v : EuclideanSpace ℝ (Fin n × Fin n × Bool)) : reLin n (unrLin n v) = v := by
  ext q
  rcases q with ⟨i, j, b⟩
  cases b <;> simp [reLin, unrLin, realifyFun, unrealify, LinearMap.coe_mk, AddHom.coe_mk] <;> rfl

def unit2 (n : ℕ) : (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := 1 + 1
  inv := (1 / 2 : ℂ) • 1
  val_inv := by rw [Matrix.mul_smul, mul_one, smul_add, ← add_smul]; norm_num
  inv_val := by rw [Matrix.smul_mul, one_mul, smul_add, ← add_smul]; norm_num

/- English proof (translation)
Introduce `n ε m h hmh horth ι η _ _ L₀ L₁`. Use `set P := EuclideanSpace ℝ ι`. Use `set Q := EuclideanSpace ℝ η`. Use `set A : P × Q →L[ℝ] Matrix (Fin n) (Fin n) ℂ := (unrLin n).toContinuousLinearMap ∘L m.subtypeL ∘L (L₀.toContinuousLinearEquiv : P →L[ℝ] m) ∘L ContinuousLinearMap.fst ℝ P Q with hA`. Use `set Bm : P × Q →L[ℝ] Matrix (Fin n) (Fin n) ℂ := (unrLin n).toContinuousLinearMap ∘L h.subtypeL ∘L (L₁.toContinuousLinearEquiv : Q →L[ℝ] h) ∘L ContinuousLinearMap.snd ℝ P Q with hBm`.

Use `set Gm : Matrix (Fin n) (Fin n) ℂ →L[ℝ] P × Q := ((L₀.symm.toContinuousLinearEquiv : m →L[ℝ] P) ∘L m.orthogonalProjectionOnto ∘L (reLin n).toContinuousLinearMap).prod ((L₁.symm.toContinuousLinearEquiv : h →L[ℝ] Q) ∘L h.orthogonalProjectionOnto ∘L (reLin n).toContinuousLinearMap) …`. Use `set Mf : P × Q → Matrix (Fin n) (Fin n) ℂ := fun p => NormedSpace.exp (A p) * NormedSpace.exp (Bm p) with hMf`. Use `set Ff : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun M => (2 : ℂ) • ((M - 1) * Ring.inverse (M + 1)) with hFf`. Establish `hpsi : psiE ε m h L₀ L₁ = fun p => Gm (Ff (Mf p))`. Use function extensionality and compare the values at `p`.

Simplify using `only [psiE, hGm, hFf, hMf, hA, hBm, Matrix.nonsing_inv_eq_ringInverse]`. Both sides reduce to the same expression. Establish `hM0 : Mf 0 = 1` using `by simp [hMf]`. Establish `hexpA : HasFDerivAt (fun p => NormedSpace.exp (A p)) A 0`. Establish `h0 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _) (A 0)` using `by rw [map_zero]; exact hasFDerivAt_exp_zero`.

Establish `h1` using `h0.comp (0 : P × Q) A.hasFDerivAt`. Conclude with `h1.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)`. Establish `hexpB : HasFDerivAt (fun p => NormedSpace.exp (Bm p)) Bm 0`. Establish `h0 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _) (Bm 0)` using `by rw [map_zero]; exact hasFDerivAt_exp_zero`. Establish `h1` using `h0.comp (0 : P × Q) Bm.hasFDerivAt`.

Conclude with `h1.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)`. Establish `hMd : HasFDerivAt Mf (A + Bm) 0`. Establish `h1` using `hexpA.mul' hexpB`. Establish `e1 : NormedSpace.exp (A 0) = 1` using `by rw [map_zero, NormedSpace.exp_zero]`. Establish `e2 : NormedSpace.exp (Bm 0) = 1` using `by rw [map_zero, NormedSpace.exp_zero]`.

Use `h1.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `NormedSpace.exp (A 0) * Bm v + A v * NormedSpace.exp (Bm 0) = A v + Bm v`. Rewrite using `[e1, e2, one_mul, mul_one, add_comm]`. Establish `hFd : HasFDerivAt Ff (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)) 1`. Establish `hs : HasFDerivAt (fun M : Matrix (Fin n) (Fin n) ℂ => M - 1) (ContinuousLinearMap.id ℝ _) 1` using `(hasFDerivAt_id (1 : Matrix (Fin n) (Fin n) ℂ)).sub_const 1`.

Establish `hi` using `(hasFDerivAt_ringInverse (𝕜 := ℝ) (unit2 n)).comp (1 : Matrix (Fin n) (Fin n) ℂ) ((hasFDerivAt_id (1 : Matrix (Fin n) (Fin n) ℂ)).add_const 1)`. Establish `hp` using `(hs.mul' hi).const_smul (2 : ℂ)`. Use `hp.congr_fderiv ?_` and prove the remaining obligations. Establish `hinv : Ring.inverse ((1 : Matrix (Fin n) (Fin n) ℂ) + 1) = (1 / 2 : ℂ) • 1`. Rewrite using `[show (1 : Matrix (Fin n) (Fin n) ℂ) + 1 = ((unit2 n : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix _ _ ℂ) from rfl, Ring.inverse_unit]`.

Both sides reduce to the same expression. Use `ContinuousLinearMap.ext fun X => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(2 : ℂ) • (((1 : Matrix (Fin n) (Fin n) ℂ) - 1) * _ + X * Ring.inverse ((1 : Matrix (Fin n) (Fin n) ℂ) + 1)) = X`. Rewrite using `[sub_self, zero_mul, zero_add, hinv, Matrix.mul_smul, mul_one, smul_smul]`. Evaluate the numerical expressions.

Establish `hall : HasFDerivAt (psiE ε m h L₀ L₁) (Gm ∘L (ContinuousLinearMap.id ℝ _) ∘L (A + Bm)) 0`. Rewrite using `[hpsi]`. Establish `hF' : HasFDerivAt Ff (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)) (Mf 0)` using `by rw [hM0]; exact hFd`. Conclude with `Gm.hasFDerivAt.comp (0 : P × Q) (hF'.comp (0 : P × Q) hMd)`. Establish `hid : Gm ∘L (ContinuousLinearMap.id ℝ _) ∘L (A + Bm) = ContinuousLinearMap.id ℝ (P × Q)`.

Use `ContinuousLinearMap.ext fun q => ?_` and prove the remaining obligations. Take `⟨x, y⟩` from `q`. Establish `hre : reLin n (A (x, y) + Bm (x, y)) = (L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ y : _)` using `by show reLin n (unrLin n (L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + unrLin n (L₁ y : EuclideanSpace ℝ (Fin n × Fin n × Bool))) = _`. Rewrite using `[map_add, re_unr, re_unr]`. Establish `h1 : (L₁ y : EuclideanSpace ℝ (Fin n × Fin n × Bool)) ∈ mᗮ`.

Rewrite using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Conclude with `horth u hu _ (L₁ y).2`. Establish `h2 : (L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) ∈ hᗮ`. Rewrite using `[Submodule.mem_orthogonal]`.

Introduce `u hu`. Rewrite using `[real_inner_comm]`. Conclude with `horth _ (L₀ x).2 u hu`. Simplify using `only [hGm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.add_apply, LinearMap.coe_toContinuousLinearMap']`. Rewrite using `[hre]`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show L₀.symm (m.orthogonalProjectionOnto ((L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ y : _))) = x`. Rewrite using `[map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal h1, add_zero, LinearIsometryEquiv.symm_apply_apply]`. Use `show L₁.symm (h.orthogonalProjectionOnto ((L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ y : _))) = y`. Rewrite using `[map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal h2, zero_add, LinearIsometryEquiv.symm_apply_apply]`.

Use `⟨?_, by rw [hall.fderiv, hid]⟩` and prove the remaining obligations. Rewrite using `[hpsi]`. Establish `hMc : ContDiffAt ℝ 1 Mf 0`. Establish `ha : ContDiffAt ℝ 1 (fun p => NormedSpace.exp (A p)) 0` using `((NormedSpace.exp_analytic (𝕂 := ℝ) (A 0)).contDiffAt).comp (0 : P × Q) A.contDiff.contDiffAt`. Establish `hb : ContDiffAt ℝ 1 (fun p => NormedSpace.exp (Bm p)) 0` using `((NormedSpace.exp_analytic (𝕂 := ℝ) (Bm 0)).contDiffAt).comp (0 : P × Q) Bm.contDiff.contDiffAt`.

Conclude with `ha.mul hb`. Establish `hFc : ContDiffAt ℝ 1 Ff (Mf 0)`. Rewrite using `[hM0]`. Establish `hi : ContDiffAt ℝ 1 (fun M : Matrix (Fin n) (Fin n) ℂ => Ring.inverse (M + 1)) 1` using `(contDiffAt_ringInverse ℝ (unit2 n)).comp (1 : Matrix (Fin n) (Fin n) ℂ) (contDiffAt_id.add contDiffAt_const)`. Conclude with `((contDiffAt_id.sub contDiffAt_const).mul hi).const_smul (2 : ℂ)`.

Conclude with `Gm.contDiff.contDiffAt.comp (0 : P × Q) (hFc.comp (0 : P × Q) hMc)`.
-/
theorem psiSmooth_holds : PsiSmoothU := by
  intro n ε m h hmh horth ι η _ _ L₀ L₁
  set P := EuclideanSpace ℝ ι
  set Q := EuclideanSpace ℝ η
  set A : P × Q →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (unrLin n).toContinuousLinearMap ∘L m.subtypeL ∘L (L₀.toContinuousLinearEquiv : P →L[ℝ] m) ∘L
      ContinuousLinearMap.fst ℝ P Q with hA
  set Bm : P × Q →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (unrLin n).toContinuousLinearMap ∘L h.subtypeL ∘L (L₁.toContinuousLinearEquiv : Q →L[ℝ] h) ∘L
      ContinuousLinearMap.snd ℝ P Q with hBm
  set Gm : Matrix (Fin n) (Fin n) ℂ →L[ℝ] P × Q :=
    ((L₀.symm.toContinuousLinearEquiv : m →L[ℝ] P) ∘L m.orthogonalProjectionOnto ∘L (reLin n).toContinuousLinearMap).prod
      ((L₁.symm.toContinuousLinearEquiv : h →L[ℝ] Q) ∘L h.orthogonalProjectionOnto ∘L (reLin n).toContinuousLinearMap)
    with hGm
  set Mf : P × Q → Matrix (Fin n) (Fin n) ℂ := fun p => NormedSpace.exp (A p) * NormedSpace.exp (Bm p) with hMf
  set Ff : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun M => (2 : ℂ) • ((M - 1) * Ring.inverse (M + 1)) with hFf
  have hpsi : psiE ε m h L₀ L₁ = fun p => Gm (Ff (Mf p)) := by
    funext p
    simp only [psiE, hGm, hFf, hMf, hA, hBm, Matrix.nonsing_inv_eq_ringInverse]
    rfl
  have hM0 : Mf 0 = 1 := by simp [hMf]

  have hexpA : HasFDerivAt (fun p => NormedSpace.exp (A p)) A 0 := by
    have h0 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _)
        (A 0) := by rw [map_zero]; exact hasFDerivAt_exp_zero
    have h1 := h0.comp (0 : P × Q) A.hasFDerivAt
    exact h1.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  have hexpB : HasFDerivAt (fun p => NormedSpace.exp (Bm p)) Bm 0 := by
    have h0 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _)
        (Bm 0) := by rw [map_zero]; exact hasFDerivAt_exp_zero
    have h1 := h0.comp (0 : P × Q) Bm.hasFDerivAt
    exact h1.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  have hMd : HasFDerivAt Mf (A + Bm) 0 := by
    have h1 := hexpA.mul' hexpB
    have e1 : NormedSpace.exp (A 0) = 1 := by rw [map_zero, NormedSpace.exp_zero]
    have e2 : NormedSpace.exp (Bm 0) = 1 := by rw [map_zero, NormedSpace.exp_zero]
    refine h1.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    change NormedSpace.exp (A 0) * Bm v + A v * NormedSpace.exp (Bm 0) = A v + Bm v
    rw [e1, e2, one_mul, mul_one, add_comm]
  have hFd : HasFDerivAt Ff (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)) 1 := by
    have hs : HasFDerivAt (fun M : Matrix (Fin n) (Fin n) ℂ => M - 1) (ContinuousLinearMap.id ℝ _) 1 :=
      (hasFDerivAt_id (1 : Matrix (Fin n) (Fin n) ℂ)).sub_const 1
    have hi :=
      (hasFDerivAt_ringInverse (𝕜 := ℝ) (unit2 n)).comp (1 : Matrix (Fin n) (Fin n) ℂ)
        ((hasFDerivAt_id (1 : Matrix (Fin n) (Fin n) ℂ)).add_const 1)
    have hp := (hs.mul' hi).const_smul (2 : ℂ)
    refine hp.congr_fderiv ?_
    have hinv : Ring.inverse ((1 : Matrix (Fin n) (Fin n) ℂ) + 1) = (1 / 2 : ℂ) • 1 := by
      rw [show (1 : Matrix (Fin n) (Fin n) ℂ) + 1 = ((unit2 n : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix _ _ ℂ) from rfl,
        Ring.inverse_unit]
      rfl
    refine ContinuousLinearMap.ext fun X => ?_
    change (2 : ℂ) • (((1 : Matrix (Fin n) (Fin n) ℂ) - 1) * _ + X * Ring.inverse ((1 : Matrix (Fin n) (Fin n) ℂ) + 1)) = X
    rw [sub_self, zero_mul, zero_add, hinv, Matrix.mul_smul, mul_one, smul_smul]
    norm_num
  have hall : HasFDerivAt (psiE ε m h L₀ L₁) (Gm ∘L (ContinuousLinearMap.id ℝ _) ∘L (A + Bm)) 0 := by
    rw [hpsi]
    have hF' : HasFDerivAt Ff (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)) (Mf 0) := by rw [hM0]; exact hFd
    exact Gm.hasFDerivAt.comp (0 : P × Q) (hF'.comp (0 : P × Q) hMd)
  have hid : Gm ∘L (ContinuousLinearMap.id ℝ _) ∘L (A + Bm) = ContinuousLinearMap.id ℝ (P × Q) := by
    refine ContinuousLinearMap.ext fun q => ?_
    obtain ⟨x, y⟩ := q
    have hre : reLin n (A (x, y) + Bm (x, y)) = (L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ y : _) := by
      show reLin n (unrLin n (L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
        unrLin n (L₁ y : EuclideanSpace ℝ (Fin n × Fin n × Bool))) = _
      rw [map_add, re_unr, re_unr]
    have h1 : (L₁ y : EuclideanSpace ℝ (Fin n × Fin n × Bool)) ∈ mᗮ := by
      rw [Submodule.mem_orthogonal]; intro u hu; exact horth u hu _ (L₁ y).2
    have h2 : (L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) ∈ hᗮ := by
      rw [Submodule.mem_orthogonal]; intro u hu; rw [real_inner_comm]; exact horth _ (L₀ x).2 u hu
    simp only [hGm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.add_apply, LinearMap.coe_toContinuousLinearMap']
    rw [hre]
    refine Prod.ext ?_ ?_
    · show L₀.symm (m.orthogonalProjectionOnto ((L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ y : _))) = x
      rw [map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal h1, add_zero, LinearIsometryEquiv.symm_apply_apply]
    · show L₁.symm (h.orthogonalProjectionOnto ((L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ y : _))) = y
      rw [map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal h2, zero_add, LinearIsometryEquiv.symm_apply_apply]
  refine ⟨?_, by rw [hall.fderiv, hid]⟩

  rw [hpsi]
  have hMc : ContDiffAt ℝ 1 Mf 0 := by
    have ha : ContDiffAt ℝ 1 (fun p => NormedSpace.exp (A p)) 0 :=
      ((NormedSpace.exp_analytic (𝕂 := ℝ) (A 0)).contDiffAt).comp (0 : P × Q) A.contDiff.contDiffAt
    have hb : ContDiffAt ℝ 1 (fun p => NormedSpace.exp (Bm p)) 0 :=
      ((NormedSpace.exp_analytic (𝕂 := ℝ) (Bm 0)).contDiffAt).comp (0 : P × Q) Bm.contDiff.contDiffAt
    exact ha.mul hb
  have hFc : ContDiffAt ℝ 1 Ff (Mf 0) := by
    rw [hM0]
    have hi : ContDiffAt ℝ 1 (fun M : Matrix (Fin n) (Fin n) ℂ => Ring.inverse (M + 1)) 1 :=
      (contDiffAt_ringInverse ℝ (unit2 n)).comp (1 : Matrix (Fin n) (Fin n) ℂ)
        (contDiffAt_id.add contDiffAt_const)
    exact ((contDiffAt_id.sub contDiffAt_const).mul hi).const_smul (2 : ℂ)
  exact Gm.contDiff.contDiffAt.comp (0 : P × Q) (hFc.comp (0 : P × Q) hMc)

/- English proof (translation)
The claim follows from `expProdU_of_parts hC psiSmooth_holds hM hI`.
-/
theorem expProdU_of_two (hC : CayProdU) (hM : PsiMeasU) (hI : PsiInvU) : ExpProdU :=
  expProdU_of_parts hC psiSmooth_holds hM hI

end PI.AprimeInfW
