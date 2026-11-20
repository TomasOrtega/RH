import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def resQ (φ : GA E a → ℂ) : RightCosetSpace (rationalGLOne E a) → ℂ :=
  fun q => φ ((Quotient.out q : normOneGL E a) : GA E a)

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem resQ_mk {φ : GA E a → ℂ} (h : ∀ γ g, φ (ratGL E a γ * g) = φ g) (x : normOneGL E a) :
    resQ φ (RightCosetSpace.mk _ x) = φ x := by
  have e : RightCosetSpace.mk (rationalGLOne E a)
      (Quotient.out (RightCosetSpace.mk (rationalGLOne E a) x)) = RightCosetSpace.mk _ x :=
    Quotient.out_eq _
  obtain ⟨γ, hγ⟩ := RightCosetSpace.mk_eq_mk_iff.1 e
  obtain ⟨δ, hδ⟩ : ((γ : normOneGL E a) : GA E a) ∈ AdelicGLn.rationalGL E a := γ.2
  unfold resQ
  rw [← hγ]
  change φ (((γ : normOneGL E a) : GA E a) * (x : GA E a)) = _
  rw [← hδ]
  exact h δ x.1

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_resQ {φ : GA E a → ℂ} (hc : Continuous φ) (h : ∀ γ g, φ (ratGL E a γ * g) = φ g) :
    Continuous (resQ φ) := by
  refine (RightCosetSpace.isOpenQuotientMap_mk (rationalGLOne E a)).isQuotientMap.continuous_iff.2 ?_
  have : resQ φ ∘ RightCosetSpace.mk (rationalGLOne E a) = fun x : normOneGL E a => φ x :=
    funext fun x => resQ_mk h x
  rw [this]
  exact hc.comp continuous_subtype_val

end GlobalTheory.CompanionTheory.CuspTransfer
end
