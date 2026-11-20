import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CutOff

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem latS_isOpen_isCompact : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (S : Finset (Pl E)) (B : ∀ w : Pl E, AddSubgroup (w.adicCompletion E)), (∀ w ∈ S, IsOpen (B w : Set (w.adicCompletion E))) → (∀ w ∈ S, (B w : Set (w.adicCompletion E)) ⊆ (Formalism.UG.Ov E w : Set (w.adicCompletion E))) → IsOpen (latS S B : Set (Af E)) ∧ IsCompact (latS S B : Set (Af E)) := by
  intro E _ _ _ S B hO hI
  have hc : ∀ w : Pl E, Continuous (pLoc E w) := fun w => RestrictedProduct.continuous_eval w
  have heq : (latS S B : Set (Af E)) =
      (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) ∩
        ⋂ w ∈ S, (pLoc E w) ⁻¹' (B w : Set (w.adicCompletion E)) := by
    ext a
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨GroundTheory.Global.mem_integralFiniteAdeles.2 fun w => ?_, ?_⟩
      · by_cases hw : w ∈ S
        · exact hI w hw (h2 w hw)
        · exact h1 w hw
      · exact Set.mem_iInter₂.2 fun w hw => h2 w hw
    · rintro ⟨h1, h2⟩
      exact ⟨fun w _ => GroundTheory.Global.mem_integralFiniteAdeles.1 h1 w,
        fun w hw => Set.mem_iInter₂.1 h2 w hw⟩
  rw [heq]
  constructor
  · exact GroundTheory.Global.isOpen_integralFiniteAdeles.inter
      (isOpen_biInter_finset fun w hw => (hO w hw).preimage (hc w))
  · refine (GroundTheory.Global.isCompact_integralFiniteAdeles E).inter_right ?_
    refine isClosed_biInter fun w hw => IsClosed.preimage (hc w) ?_
    exact AddSubgroup.isClosed_of_isOpen (B w) (hO w hw)

end GlobalTheory.CompanionTheory.CutOff
