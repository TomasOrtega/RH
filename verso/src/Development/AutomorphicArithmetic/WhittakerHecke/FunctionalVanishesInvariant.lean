import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CapRDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreDerivativeLieAction
open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

/- English proof (translation)
Establish `h` using `GlobalTheory.CuspBoundSiegel.diagUnits_posIdele (E := E) r (Real.rpow_pos_of_pos (Real.exp_pos t) ((r * Module.finrank ℚ E : ℝ))⁻¹)`. Rewrite `h` using `[Real.log_rpow (Real.exp_pos t), Real.log_exp, mul_comm _ t]`. Conclude with `h`.
-/
private theorem zt_eq (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r : ℕ) (t : ℝ) :
    zt E r t = GlobalTheory.UnitaryBC.splitCentre E r (t * ((r * Module.finrank ℚ E : ℝ))⁻¹) := by
  have h := GlobalTheory.CuspBoundSiegel.diagUnits_posIdele (E := E) r
    (Real.rpow_pos_of_pos (Real.exp_pos t) ((r * Module.finrank ℚ E : ℝ))⁻¹)
  rw [Real.log_rpow (Real.exp_pos t), Real.log_exp, mul_comm _ t] at h
  exact h

/- English proof (translation)
Introduce `E _ _ _ r f hf`. Break down `Nat.eq_zero_or_pos r with rfl | hr` into its components or cases. Simplify using `[j0]`. Establish `hd : ((r * Module.finrank ℚ E : ℝ)) ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.2 hr.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')`. Establish `h : ∀ t g, f.1 (GlobalTheory.UnitaryBC.splitCentre E r t * g) = f.1 g` using `fun t g => by`.

Use `hf (t * (r * Module.finrank ℚ E : ℝ)) g` as an intermediate fact. Rewrite `this` using `[zt_eq, mul_inv_cancel_right₀ hd]`. Then use the resulting hypothesis. Establish `h0 : lie E r (oneL E r) f = 0`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Establish `h1` using `GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre E r f g 0`.

Establish `h2 : (fun t : ℝ => f.1 (g * GlobalTheory.UnitaryBC.splitCentre E r t)) = fun _ => f.1 g`. Use function extensionality and compare the values at `t`. Rewrite using `[← CuspidalL2GL.splitCentre_comm, h]`. Rewrite `h1` using `[h2]`. Establish `h3` using `h1.unique (hasDerivAt_const (0 : ℝ) (f.1 g))`.

Rewrite `h3` using `[CuspidalL2GL.splitCentre_zero, mul_one]`. Conclude with `h3`. Establish `h4 : lie E r (oneL E r) = ∑ τ : E →+* ℂ, ∑ i : Fin r, Eop τ i i`. Rewrite using `[UpperTheory.V.Cm.lie_eq_sum]`. Establish `hc : ∀ (τ : E →+* ℂ) (i k : Fin r), coord τ (oneL E r i k) = if i = k then 1 else 0` using `fun τ i k => by`.

Establish `: oneL E r i k = (1 : Matrix (Fin r) (Fin r) (Cinf E)) i k` using `rfl`. Rewrite using `[this, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[j0, LinearMap.smul_apply, ← h4, h0, smul_zero]`.
-/
theorem UpperTheory.functional_vanishes_invariant :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r : ℕ) (f : Sm E r), (∀ t g, f.1 (zt E r t * g) = f.1 g) → j0 E r f = 0 := by
  intro E _ _ _ r f hf
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [j0]
  have hd : ((r * Module.finrank ℚ E : ℝ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hr.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  have h : ∀ t g, f.1 (GlobalTheory.UnitaryBC.splitCentre E r t * g) = f.1 g := fun t g => by
    have := hf (t * (r * Module.finrank ℚ E : ℝ)) g
    rwa [zt_eq, mul_inv_cancel_right₀ hd] at this
  have h0 : lie E r (oneL E r) f = 0 := by
    refine Subtype.ext (funext fun g => ?_)
    have h1 := GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre E r f g 0
    have h2 : (fun t : ℝ => f.1 (g * GlobalTheory.UnitaryBC.splitCentre E r t)) = fun _ => f.1 g := by
      funext t
      rw [← CuspidalL2GL.splitCentre_comm, h]
    rw [h2] at h1
    have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (f.1 g))
    rw [CuspidalL2GL.splitCentre_zero, mul_one] at h3
    exact h3
  have h4 : lie E r (oneL E r) = ∑ τ : E →+* ℂ, ∑ i : Fin r, Eop τ i i := by
    rw [UpperTheory.V.Cm.lie_eq_sum]
    have hc : ∀ (τ : E →+* ℂ) (i k : Fin r), coord τ (oneL E r i k) = if i = k then 1 else 0 := fun τ i k => by
      have : oneL E r i k = (1 : Matrix (Fin r) (Fin r) (Cinf E)) i k := rfl
      rw [this, Matrix.one_apply]
      split_ifs <;> simp
    simp only [hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [j0, LinearMap.smul_apply, ← h4, h0, smul_zero]
