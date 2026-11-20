import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TauL
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection
open scoped NumberField.AdeleRing ValuativeRel ENNReal
open Ad3 Ad3.K Ad3.K.GPK GlobalTheory.CompanionTheory.GPKIntB

noncomputable section

namespace GlobalTheory.CompanionTheory.GPKIntB.Compl

/- English proof (translation)
Establish `h : volC = ((2 : NNReal) • (volume : Measure ℂ))`. Unfold `volC`. Use extensionality with `s hs`. Simplify using the standard rewrite rules. Rewrite using `[h]`.

Use `infer_instance`.
-/
theorem sfinite_volC : SFinite volC := by
  have h : volC = ((2 : NNReal) • (volume : Measure ℂ)) := by
    unfold volC
    ext s hs
    simp
  rw [h]
  infer_instance

/- English proof (translation)
Establish `hd : (Matrix.of (Matrix.of.symm g.val)).det ≠ 0`. Simplify using `using (Matrix.GeneralLinearGroup.det g).ne_zero`. Unfold `extC`. Rewrite using `[dif_pos hd]`. Use `congr 1`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.
-/
theorem extC_val (W : GL (Fin 3) ℂ → ℂ) (g : GL (Fin 3) ℂ) :
    extC W (Matrix.of.symm g.val) = W g := by
  have hd : (Matrix.of (Matrix.of.symm g.val)).det ≠ 0 := by
    simpa using (Matrix.GeneralLinearGroup.det g).ne_zero
  unfold extC
  rw [dif_pos hd]
  congr 1
  apply Units.ext
  simp

/- English proof (translation)
Establish `hc : ContinuousOn (extC W) {m : complexMatrix3 | (Matrix.of m).det ≠ 0}` using `h.continuousOn`. Establish `hv : Continuous (fun g : GL (Fin 3) ℂ => (Matrix.of.symm g.val : complexMatrix3))`. Establish `h0 : Continuous (Units.val : GL (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) ℂ)` using `Units.continuous_val`. Conclude with `h0`. Establish `hm : ∀ g : GL (Fin 3) ℂ, (Matrix.of.symm g.val : complexMatrix3) ∈ {m : complexMatrix3 | (Matrix.of m).det ≠ 0}`.

Introduce `g`. Simplify using `using (Matrix.GeneralLinearGroup.det g).ne_zero`. Use `hc.comp_continuous hv hm` as an intermediate fact. Simplify `this` using `[Function.comp_def, extC_val]`.
-/
theorem continuous_of_smoothC {W : GL (Fin 3) ℂ → ℂ} (h : SmoothC W) : Continuous W := by
  have hc : ContinuousOn (extC W) {m : complexMatrix3 | (Matrix.of m).det ≠ 0} := h.continuousOn
  have hv : Continuous (fun g : GL (Fin 3) ℂ => (Matrix.of.symm g.val : complexMatrix3)) := by
    have h0 : Continuous (Units.val : GL (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) ℂ) := Units.continuous_val
    exact h0
  have hm : ∀ g : GL (Fin 3) ℂ, (Matrix.of.symm g.val : complexMatrix3) ∈ {m : complexMatrix3 | (Matrix.of m).det ≠ 0} := by
    intro g
    simpa using (Matrix.GeneralLinearGroup.det g).ne_zero
  have := hc.comp_continuous hv hm
  simpa [Function.comp_def, extC_val] using this

/- English proof (translation)
Establish `hpos : 0 < ‖(t : ℂ)‖ ^ 2`. Use `norm_pos_iff.mpr t.ne_zero` as an intermediate fact. Check the signs of the components of the expression. Establish `hn : ‖chC 0 ((-(5 / 2 : ℝ) : ℝ) : ℂ) t‖ = (‖(t : ℂ)‖ ^ 2) ^ (-(5 / 2 : ℝ))`. Unfold `chC`.

Rewrite using `[zpow_zero, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]`. Simplify using the standard rewrite rules. Rewrite using `[← ofReal_norm_eq_enorm, hn]`.
-/
theorem enorm_chC (t : ℂˣ) :
    ‖chC 0 ((-(5 / 2 : ℝ) : ℝ) : ℂ) t‖ₑ = ENNReal.ofReal ((‖(t : ℂ)‖ ^ 2) ^ (-(5 / 2 : ℝ))) := by
  have hpos : 0 < ‖(t : ℂ)‖ ^ 2 := by
    have := norm_pos_iff.mpr t.ne_zero
    positivity
  have hn : ‖chC 0 ((-(5 / 2 : ℝ) : ℝ) : ℂ) t‖ = (‖(t : ℂ)‖ ^ 2) ^ (-(5 / 2 : ℝ)) := by
    unfold chC
    rw [zpow_zero, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  rw [← ofReal_norm_eq_enorm, hn]

/- English proof (translation)
Introduce `k V E E' h W hW`. Use `⟨continuous_of_smoothC (h.smooth W hW), ?_⟩` and prove the remaining obligations. Use `haveI := sfinite_volC`. Establish `hint` using `h.int' W hW ((-(5 / 2 : ℝ) : ℝ) : ℂ) (by norm_num)`. Establish `hfin` using `hint.2`.

Establish `hne : ∫⁻ p : ℂˣ × ℂ, ‖W (mm p.1 p.2) * chC 0 ((-(5 / 2 : ℝ) : ℝ) : ℂ) p.1‖ₑ ∂(mulC.prod volC) ≠ ∞` using `hfin.ne`. Rewrite `hne` using `[lintegral_prod _ hint.1.enorm]`. Use `ne_of_eq_of_ne ?_ hne` and prove the remaining obligations. Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Simplify using `only [enorm_mul, enorm_chC]`.

Rewrite using `[lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]`.
-/
theorem main : ∀ (k : ℕ) (V : Submodule ℂ (GL (Fin 3) ℂ → ℂ)) (E E' : Fin 3 → Fin 3 → Module.End ℂ V), WhC k V E E' → ∀ W ∈ V, Continuous W ∧ ∫⁻ t : ℂˣ, (∫⁻ z, ‖W (mm t z)‖ₑ ∂volC) * ENNReal.ofReal ((‖(t : ℂ)‖ ^ 2) ^ (-(5 / 2 : ℝ))) ∂mulC ≠ ∞ := by
  intro k V E E' h W hW
  refine ⟨continuous_of_smoothC (h.smooth W hW), ?_⟩
  haveI := sfinite_volC
  have hint := h.int' W hW ((-(5 / 2 : ℝ) : ℝ) : ℂ) (by norm_num)
  have hfin := hint.2
  have hne : ∫⁻ p : ℂˣ × ℂ, ‖W (mm p.1 p.2) * chC 0 ((-(5 / 2 : ℝ) : ℝ) : ℂ) p.1‖ₑ ∂(mulC.prod volC) ≠ ∞ :=
    hfin.ne
  rw [lintegral_prod _ hint.1.enorm] at hne
  refine ne_of_eq_of_ne ?_ hne
  refine lintegral_congr fun t => ?_
  simp only [enorm_mul, enorm_chC]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]

end GlobalTheory.CompanionTheory.GPKIntB.Compl
