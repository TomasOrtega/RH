import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousNilpotentFramePart
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.IsClosedDiagonalStabiliser
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `ha` using `continuous_a' d`. Establish `e : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁)) = fun x => ((d.a x : ℝ) : ℂ) ^ (z - s₁)`. Use function extensionality and compare the values at `x`. Rewrite using `[kunf.ht_eq]`. Establish `h1 : Continuous fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁)`.

Rewrite using `[e]`. Conclude with `(Complex.continuous_ofReal.comp ha).cpow continuous_const (fun x => Complex.ofReal_mem_slitPlane.2 (kunf.a_pos d x))`. Conclude with `h1.mul hf`.
-/
theorem continuous_phz (d : SD σ) {f : d.G → ℂ} (hf : Continuous f) (s₁ z : ℂ) : Continuous (phz d f s₁ z) := by
  have ha := continuous_a' d
  have e : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁)) = fun x => ((d.a x : ℝ) : ℂ) ^ (z - s₁) := by
    funext x; rw [kunf.ht_eq]
  have h1 : Continuous fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) := by
    rw [e]
    exact (Complex.continuous_ofReal.comp ha).cpow continuous_const
      (fun x => Complex.ofReal_mem_slitPlane.2 (kunf.a_pos d x))
  exact h1.mul hf

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
