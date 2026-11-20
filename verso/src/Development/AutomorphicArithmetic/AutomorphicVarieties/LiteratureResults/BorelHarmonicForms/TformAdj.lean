import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul φ v`. Simplify using `only [LinearMap.lTensor_tmul, cmp_tmul, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.sum_smul, smul_smul]`. Consider the case `add a b ha hb`.

Simplify using `only [map_add, ha, hb, smul_add, Finset.sum_add_distrib]`.
-/
private theorem cmp_lTensor_toLin {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j ((Matrix.toLin' Q).lTensor W y) = ∑ k, Q j k • cmp k y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    simp only [LinearMap.lTensor_tmul, cmp_tmul, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Finset.sum_smul, smul_smul]
  | add a b ha hb =>
    simp only [map_add, ha, hb, smul_add, Finset.sum_add_distrib]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]`.
-/
private theorem cmp_rTensor_end {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (S : Module.End ℂ W)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j (S.rTensor (Fin d → ℂ) y) = S (cmp j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

/- English proof (translation)
Introduce `W _ _ d H N G P Q S T`. Use `⟨fun hPQ x y => ?_, fun hST x hx y hy => ?_⟩` and prove the remaining obligations. Establish `key : ∀ a b, (G * Q) a b = (Pᴴ * G) a b` using `fun a b => by rw [hPQ]`. Establish `hL : tform H G x ((Matrix.toLin' Q).lTensor W y) = ∑ a, ∑ b, (G * Q) a b * H (cmp a x) (cmp b y)`. Rewrite using `[tform_apply]`.

Simplify using `only [cmp_lTensor_toLin, map_sum, map_smul, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring`. Establish `hR : tform H G ((Matrix.toLin' P).lTensor W x) y = ∑ a, ∑ b, (Pᴴ * G) a b * H (cmp a x) (cmp b y)`.

Rewrite using `[tform_apply]`. Simplify using `only [cmp_lTensor_toLin, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `conv_lhs => enter [2, j]`. Rewrite using `[Finset.sum_comm]`.

Use `conv_lhs => rw [Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[hL, hR]`. Simplify using `only [key]`. Rewrite `hx`, `hy` using `[mem_tens]`.

Rewrite using `[tform_apply, tform_apply]`. Simplify using `only [cmp_rTensor_end, hST _ (hx _) _ (hy _)]`.
-/
theorem UpperTheory.V.Lit.Bor.tformAdj :
    UpperTheory.V.Lit.Bor.TformAdj := by
  intro W _ _ d H N G P Q S T
  refine ⟨fun hPQ x y => ?_, fun hST x hx y hy => ?_⟩
  · have key : ∀ a b, (G * Q) a b = (Pᴴ * G) a b := fun a b => by rw [hPQ]
    have hL : tform H G x ((Matrix.toLin' Q).lTensor W y)
        = ∑ a, ∑ b, (G * Q) a b * H (cmp a x) (cmp b y) := by
      rw [tform_apply]
      simp only [cmp_lTensor_toLin, map_sum, map_smul, smul_eq_mul, Matrix.mul_apply,
        Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    have hR : tform H G ((Matrix.toLin' P).lTensor W x) y
        = ∑ a, ∑ b, (Pᴴ * G) a b * H (cmp a x) (cmp b y) := by
      rw [tform_apply]
      simp only [cmp_lTensor_toLin, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply,
        starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
      conv_lhs => rw [Finset.sum_comm]
      conv_lhs => enter [2, j]; rw [Finset.sum_comm]
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun i _ => by ring
    rw [hL, hR]
    simp only [key]
  · rw [mem_tens] at hx hy
    rw [tform_apply, tform_apply]
    simp only [cmp_rTensor_end, hST _ (hx _) _ (hy _)]
