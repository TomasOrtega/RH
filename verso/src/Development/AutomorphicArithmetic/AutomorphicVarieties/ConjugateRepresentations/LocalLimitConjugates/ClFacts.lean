import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConvolutionL2Class
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Cj.H.clFacts :
    UpperTheory.V.Cj.H.ClFacts := by
  intro E _ _ _ a μ _ _
  refine ⟨fun φ ψ s t hφ hψ => ?_, fun φ hl hφ h0 => ?_, fun φ g hφ => ?_, fun ψ φ F hψ e => ?_⟩
  · have hm : InL μ (s • φ + t • ψ) := by
      refine ⟨fun γ hγ g => ?_, ?_⟩
      · change s • φ.1 (γ * g) + t • ψ.1 (γ * g) = s • φ.1 g + t • ψ.1 g
        rw [hφ.1 γ hγ g, hψ.1 γ hγ g]
      · exact (hφ.2.const_smul s).add (hψ.2.const_smul t)
    refine ⟨hm, ?_⟩
    rw [cl_eq hm, cl_eq hφ, cl_eq hψ]
    exact (MemLp.toLp_add (hφ.2.const_smul s) (hψ.2.const_smul t)).trans
      (congrArg₂ (· + ·) (MemLp.toLp_const_smul s hφ.2) (MemLp.toLp_const_smul t hψ.2))
  · by_contra hne
    rw [cl_eq hφ] at h0
    exact GlobalTheory.CuspRep.CuspidalL2GL.toL2_ne_zero hφ (ContAut.continuous_of_isOpen_stab E a φ hl)
      (fun h => hne (Subtype.ext h)) h0
  · have hm : InL μ (rt E a g φ) := hφ.mul_right g
    rw [cl_eq hm, cl_eq hφ]
    exact (GlobalTheory.AutomorphicL2Unitary.right_translate_toL2 hφ g).symm
  · obtain ⟨h, hh⟩ := UpperTheory.V.Cj.H.convolution_L2_class (GA E a) (latticeGL E a) μ ψ.1
      (ContAut.continuous_of_isOpen_stab E a ψ hψ.2) hψ.1 F
    have hm : InL μ φ := by
      unfold InL
      rw [e]
      exact h
    rw [cl_eq hm, ← hh]
    congr 1
