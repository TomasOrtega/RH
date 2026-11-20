import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish `hx : ‖(x : Fv F v)‖ ≤ 1` using `(Valued.toNormedField.norm_le_one_iff).mpr x.2`. Establish `hy : ‖(y : Fv F v)‖ ≤ 1` using `(Valued.toNormedField.norm_le_one_iff).mpr y.2`. Establish `hxy : ‖(x : Fv F v)‖ * ‖(y : Fv F v)‖ = 1`. Rewrite using `[← norm_mul]`. Establish `: ((x : Fv F v) * (y : Fv F v)) = 1`.

Use `congrArg (fun z : v.adicCompletionIntegers F => (z : Fv F v)) h` as an intermediate fact. Simplify using `using this`. Rewrite using `[this, norm_one]`. Establish `h0` using `norm_nonneg (x : Fv F v)`. Establish `h0'` using `norm_nonneg (y : Fv F v)`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem adicCompletionIntegers_norm_eq_one_of_mul_eq_one (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletionIntegers F) (h : x * y = 1) : ‖(x : Fv F v)‖ = 1 := by
  have hx : ‖(x : Fv F v)‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).mpr x.2
  have hy : ‖(y : Fv F v)‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).mpr y.2
  have hxy : ‖(x : Fv F v)‖ * ‖(y : Fv F v)‖ = 1 := by
    rw [← norm_mul]
    have : ((x : Fv F v) * (y : Fv F v)) = 1 := by
      have := congrArg (fun z : v.adicCompletionIntegers F => (z : Fv F v)) h
      simpa using this
    rw [this, norm_one]
  have h0 := norm_nonneg (x : Fv F v)
  have h0' := norm_nonneg (y : Fv F v)
  nlinarith

end GlobalTheory
