import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

open scoped Matrix.Norms.Operator in

/- English proof (translation)
Establish `h1 : ∀ t, HasDerivAt F (F t * D) t`. Introduce `t`. Establish `h2 : HasDerivAt (fun s => F (s - t)) D t`. Establish `h` using `HasDerivAt.comp_sub_const (f := F) (f' := D) t t (by rw [sub_self]; exact hD)`. Conclude with `h`.

Establish `h3` using `h2.const_mul (F t)`. Use `h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F s = F t * F (s - t)`. Rewrite using `[← hadd, add_sub_cancel]`. Establish `h4 : ∀ t, HasDerivAt (fun t : ℝ => F t * NormedSpace.exp (t • -D)) 0 t`.

Introduce `t`. Establish `h` using `(h1 t).mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-D) t)`. Establish `e : F t * D * NormedSpace.exp (t • -D) + F t * (-D * NormedSpace.exp (t • -D)) = 0`. Rewrite using `[neg_mul, mul_neg, mul_assoc, add_neg_cancel]`. Conclude with `h.congr_deriv e`.

Establish `h5` using `is_const_of_deriv_eq_zero (fun t => (h4 t).differentiableAt) (fun t => (h4 t).deriv) 1 0`. Simplify using `only [one_smul, zero_smul, NormedSpace.exp_zero, h0, mul_one] at h5`. Establish `h6 : NormedSpace.exp (-D) * NormedSpace.exp D = 1`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.refl D).neg_left, neg_add_cancel, NormedSpace.exp_zero]`. Rewrite using `[← mul_one (F 1), ← h6, ← mul_assoc, h5, one_mul]`.
-/
private theorem oneParam_eq_exp {n : ℕ} (F : ℝ → Matrix (Fin n) (Fin n) ℂ) (D : Matrix (Fin n) (Fin n) ℂ)
    (h0 : F 0 = 1) (hadd : ∀ s t, F (s + t) = F s * F t) (hD : HasDerivAt F D 0) :
    F 1 = NormedSpace.exp D := by
  have h1 : ∀ t, HasDerivAt F (F t * D) t := by
    intro t
    have h2 : HasDerivAt (fun s => F (s - t)) D t := by
      have h := HasDerivAt.comp_sub_const (f := F) (f' := D) t t (by rw [sub_self]; exact hD)
      exact h
    have h3 := h2.const_mul (F t)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    change F s = F t * F (s - t)
    rw [← hadd, add_sub_cancel]
  have h4 : ∀ t, HasDerivAt (fun t : ℝ => F t * NormedSpace.exp (t • -D)) 0 t := by
    intro t
    have h := (h1 t).mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-D) t)
    have e : F t * D * NormedSpace.exp (t • -D) + F t * (-D * NormedSpace.exp (t • -D)) = 0 := by
      rw [neg_mul, mul_neg, mul_assoc, add_neg_cancel]
    exact h.congr_deriv e
  have h5 := is_const_of_deriv_eq_zero (fun t => (h4 t).differentiableAt) (fun t => (h4 t).deriv) 1 0
  simp only [one_smul, zero_smul, NormedSpace.exp_zero, h0, mul_one] at h5
  have h6 : NormedSpace.exp (-D) * NormedSpace.exp D = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl D).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  rw [← mul_one (F 1), ← h6, ← mul_assoc, h5, one_mul]

open scoped Matrix.Norms.Operator in
/- English proof (translation)
Set `c : ℝ → GL (Fin a) (Cinf E)` to `fun t => (Matrix.isUnit_exp (t • X)).unit`. Establish `hc : ∀ t, (c t).val = NormedSpace.exp (t • X)` using `fun t => rfl`. Establish `h0 : c 0 = 1` using `Units.ext (by simp [c])`. Establish `hadd : ∀ s t, c (s + t) = c s * c t` using `fun s t => Units.ext (by`. Rewrite using `[Units.val_mul, hc, hc, hc, add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)])`.

Establish `h1 : HasDerivAt (fun t => (c t).val) X 0`. Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0`. Rewrite `h` using `[zero_smul, NormedSpace.exp_zero, one_mul]`. Conclude with `h`. Establish `h2` using `GlobalTheory.AlgInfChar.hasDerivAt_mat Ξ c (toL X) h0 h1`.

Establish `h3` using `oneParam_eq_exp (fun t => Ξ.mat (c t)) _ (by simp only [h0, map_one]) (fun s t => by simp only [hadd, map_mul]) h2`. Establish `e : (Matrix.isUnit_exp X).unit = c 1` using `Units.ext (by rw [hc, one_smul]; rfl)`. Rewrite using `[e]`. Conclude with `h3`.
-/
private theorem representation_exp_eq_exp_derivative {E : Type} [Field E] [NumberField E] {a : ℕ} (Ξ : AlgRep E a)
    (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    Ξ.mat (Matrix.isUnit_exp X).unit = NormedSpace.exp (Ξ.dmat (toL X)) := by
  let c : ℝ → GL (Fin a) (Cinf E) := fun t => (Matrix.isUnit_exp (t • X)).unit
  have hc : ∀ t, (c t).val = NormedSpace.exp (t • X) := fun t => rfl
  have h0 : c 0 = 1 := Units.ext (by simp [c])
  have hadd : ∀ s t, c (s + t) = c s * c t := fun s t => Units.ext (by
    rw [Units.val_mul, hc, hc, hc, add_smul,
      Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)])
  have h1 : HasDerivAt (fun t => (c t).val) X 0 := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  have h2 := GlobalTheory.AlgInfChar.hasDerivAt_mat Ξ c (toL X) h0 h1
  have h3 := oneParam_eq_exp (fun t => Ξ.mat (c t)) _ (by simp only [h0, map_one])
    (fun s t => by simp only [hadd, map_mul]) h2
  have e : (Matrix.isUnit_exp X).unit = c 1 := Units.ext (by rw [hc, one_smul]; rfl)
  rw [e]
  exact h3

/- English proof (translation)
Introduce `E _ _ _ a Ξ X y hy`. Establish `e : y = (Matrix.isUnit_exp X).unit` using `Units.ext hy`. Rewrite using `[e]`. Conclude with `representation_exp_eq_exp_derivative Ξ X`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.expMat :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (X : Matrix (Fin a) (Fin a) (Cinf E)) (y : GL (Fin a) (Cinf E)),
      y.val = NormedSpace.exp X → Ξ.mat y = NormedSpace.exp (Ξ.dmat (toL X)) := by
  intro E _ _ _ a Ξ X y hy
  have e : y = (Matrix.isUnit_exp X).unit := Units.ext hy
  rw [e]
  exact representation_exp_eq_exp_derivative Ξ X
