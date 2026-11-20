import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplitAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Substitute using the available equality. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Simplify to obtain the desired conclusion from the available facts.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.T.splitStrong :
    UpperTheory.ConvolutionTheory.T.DescStep → UpperTheory.ConvolutionTheory.T.SplitStrong := by
  intro hD F E _ _ _ _ _ _ _ _ σ hσ hp n hn π P hc hw v w i hi hcomp τ τ' hτ hτ'
  obtain ⟨-, -, -, -, -, hpl⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨hs, u, rfl, hiu⟩ := hpl v w i hi hcomp
  obtain ⟨π', hl, hloc⟩ := hD F E σ hσ hp n hn P hc v u hs
  obtain ⟨η, hη, hiso⟩ := (UpperTheory.ConvolutionTheory.R.fibre_holds F E hp n hn (.cx π') (.cx P) hl.1).2 (.cx π) hw
  have he : π'.twist η = π := (UpperTheory.ConvolutionTheory.Dp.isoEq F n (π'.twist η) π).1 hiso
  subst he
  have hτ₀ : (UpperTheory.CBC.Cusp.cx π').locComp v τ := by
    rcases hη with rfl | hη
    · simpa [GlobalTheory.CuspRep.CuspSub.twist_one] using hτ
    · exact (UpperTheory.ConvolutionTheory.T.normCharSplit F E σ hσ hp n hn η hη v hs π' τ).1 hτ
  obtain ⟨e, he⟩ := hloc τ τ' hτ₀ hτ'
  have hm : i.toRingHom = GroundTheory.Global.SemiLocal.completionMap v u.1 := RingHom.ext hiu
  refine ⟨e, fun g x => ?_⟩
  rw [hm]
  exact he g x
