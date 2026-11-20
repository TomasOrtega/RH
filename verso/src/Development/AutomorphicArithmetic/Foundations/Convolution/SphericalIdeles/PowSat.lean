import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist

noncomputable section

open NumberField IsDedekindDomain
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC

namespace UpperTheory.ConvolutionTheory.Sph.PW

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `e : Neutral.B1.localIdele K v x = GroundTheory.Global.IdeleGroup.finiteEmbedding v x` using `Units.ext rfl`. Rewrite using `[e]`. Conclude with `GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x`.
-/
private theorem ideleModule_localIdele (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule K (Neutral.B1.localIdele K v x)).1 : ℝ) =
      ‖(x : v.adicCompletion K)‖ := by
  have e : Neutral.B1.localIdele K v x = GroundTheory.Global.IdeleGroup.finiteEmbedding v x :=
    Units.ext rfl
  rw [e]
  exact GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x

/- English proof (translation)
Rewrite using `[FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]`. Simplify using `[WithZero.exp]`.
-/
private theorem norm_eq_zpow (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) (n : ℤ)
    (h : Valued.v x = WithZero.exp n) : ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  rw [FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp [WithZero.exp]

/- English proof (translation)
Rewrite using `[← ideleModule_localIdele]`. Conclude with `h _`.
-/
private theorem loc_eq {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← ideleModule_localIdele]
  exact h _

end UpperTheory.ConvolutionTheory.Sph.PW

open UpperTheory.ConvolutionTheory.Sph.PW in
/- English proof (translation)
Introduce `K _ _ χ s h v`. Use `⟨fun x hx => Units.ext ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[loc_eq h, norm_eq_zpow v _ 0 (by simpa [Formalism.L2.Host.IsUnitAt] using hx)]`. Simplify using the standard rewrite rules. Establish `e : χ.val v = χ.loc v (Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v))` using `rfl`.

Rewrite using `[e, loc_eq h, norm_eq_zpow v _ (-1) (Formalism.L2.Host.unif_spec v), zpow_neg_one, Complex.ofReal_inv, Complex.inv_cpow _ _ (by`. Rewrite using `[Complex.arg_ofReal_of_nonneg (by positivity)]`. Conclude with `Real.pi_pos.ne), Complex.cpow_neg]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.ConvolutionTheory.Sph.powSat :
    UpperTheory.ConvolutionTheory.Sph.PowSat := by
  intro K _ _ χ s h v
  refine ⟨fun x hx => Units.ext ?_, ?_⟩
  · rw [loc_eq h, norm_eq_zpow v _ 0 (by simpa [Formalism.L2.Host.IsUnitAt] using hx)]
    simp
  · have e : χ.val v = χ.loc v (Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v)) := rfl
    rw [e, loc_eq h, norm_eq_zpow v _ (-1) (Formalism.L2.Host.unif_spec v), zpow_neg_one,
      Complex.ofReal_inv, Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg (by positivity)]
        exact Real.pi_pos.ne), Complex.cpow_neg]
    simp
