import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowExpIOrInvInjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectorsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

/- English proof (translation)
Rewrite `h` using `[← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]`. Take `⟨n, hn⟩` from `h`. Establish `him` using `congrArg Complex.im hn`. Simplify using `only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im, Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.mul_re] at him`. Establish `hre : ((a : ℝ) - b) = n * (2 * Real.pi)` using `by linarith`.

Distinguish the cases in `h0 : n = 0`. Substitute `h0` using the available equality. Establish `: (a : ℝ) = b` using `by simpa [sub_eq_zero] using hre`. Conclude with `this` after adjusting the coercions. It suffices to derive a contradiction.

Establish `hn0 : (n : ℝ) ≠ 0` using `by exact_mod_cast h0`. Establish `hpi : Real.pi = ((((a : ℚ) - b) / (2 * n) : ℚ) : ℝ)`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `irrational_pi ⟨_, hpi.symm⟩`.
-/
private theorem pow_exp_I_injective (a b : ℕ)
    (h : Complex.exp Complex.I ^ a = Complex.exp Complex.I ^ b) : a = b := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  have him := congrArg Complex.im hn
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.natCast_re,
    Complex.natCast_im, Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.mul_re] at him
  have hre : ((a : ℝ) - b) = n * (2 * Real.pi) := by linarith
  by_cases h0 : n = 0
  · subst h0
    have : (a : ℝ) = b := by simpa [sub_eq_zero] using hre
    exact_mod_cast this
  · exfalso
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast h0
    have hpi : Real.pi = ((((a : ℚ) - b) / (2 * n) : ℚ) : ℝ) := by
      push_cast
      field_simp
      linarith
    exact irrational_pi ⟨_, hpi.symm⟩

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `a b w hw hab`. Break down `hw with rfl | rfl` into its components or cases. Conclude with `pow_exp_I_injective a b hab`. Rewrite `hab` using `[inv_pow, inv_pow, _root_.inv_inj]`. Conclude with `pow_exp_I_injective a b hab`.
-/
theorem _root_.GlobalTheory.T.eq_of_pow_eq_pow_of_eq_exp_I_or_inv : ∀ (a b : ℕ) (w : ℂ), (w = Complex.exp Complex.I ∨ w = (Complex.exp Complex.I)⁻¹) → w ^ a = w ^ b → a = b := by
  intro a b w hw hab
  rcases hw with rfl | rfl
  · exact pow_exp_I_injective a b hab
  · rw [inv_pow, inv_pow, _root_.inv_inj] at hab
    exact pow_exp_I_injective a b hab
