import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW

/- English proof (translation)
Introduce `E _ _ w`. Use `⟨psiLocChar w, fun x => rfl, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : Continuous (psiLocChar w)`. Establish `: (psiLocChar w : w.adicCompletion E → ℂ) = fun x => ((GroundTheory.Global.localAdelicChar E w x : Circle) : ℂ)`. Use function extensionality and compare the values at `x`.

Conclude with `GlobalTheory.JSW.WhitModel.psiLoc_eq w x`. Rewrite using `[this]`. Conclude with `continuous_subtype_val.comp (GroundTheory.Global.continuous_localAdelicChar w)`. Conclude with `GlobalTheory.SchrSBFin.isLocallyConstant_addChar _ hc`. Introduce `h`.

Apply `GroundTheory.Global.localAdelicChar_ne_one (K := E) (v := w)` to reduce the goal to its premises. Use `AddChar.ext _ _ fun x => ?_` and prove the remaining obligations. Establish `h1 : psiLocChar w x = 1` using `by rw [h]; rfl`. Establish `h2 : ((GroundTheory.Global.localAdelicChar E w x : Circle) : ℂ) = 1`. Rewrite using `[← GlobalTheory.JSW.WhitModel.psiLoc_eq]`.

Conclude with `h1`. Conclude with `Subtype.ext h2`.
-/
theorem psiLoc_addChar_locallyConstant_ne_one :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ ψ : AddChar (w.adicCompletion E) ℂ,
      (∀ x, ψ x = GlobalTheory.JSW.psiLoc w x) ∧ IsLocallyConstant ψ ∧ ψ ≠ 1 := by
  intro E _ _ w
  refine ⟨psiLocChar w, fun x => rfl, ?_, ?_⟩
  · have hc : Continuous (psiLocChar w) := by
      have : (psiLocChar w : w.adicCompletion E → ℂ) = fun x => ((GroundTheory.Global.localAdelicChar E w x : Circle) : ℂ) := by
        funext x; exact GlobalTheory.JSW.WhitModel.psiLoc_eq w x
      rw [this]
      exact continuous_subtype_val.comp (GroundTheory.Global.continuous_localAdelicChar w)
    exact GlobalTheory.SchrSBFin.isLocallyConstant_addChar _ hc
  · intro h
    apply GroundTheory.Global.localAdelicChar_ne_one (K := E) (v := w)
    refine AddChar.ext _ _ fun x => ?_
    have h1 : psiLocChar w x = 1 := by rw [h]; rfl
    have h2 : ((GroundTheory.Global.localAdelicChar E w x : Circle) : ℂ) = 1 := by
      rw [← GlobalTheory.JSW.WhitModel.psiLoc_eq]; exact h1
    exact Subtype.ext h2

end GlobalTheory.JSW
