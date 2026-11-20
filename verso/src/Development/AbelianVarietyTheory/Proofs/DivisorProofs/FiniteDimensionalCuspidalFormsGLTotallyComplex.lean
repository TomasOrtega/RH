import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfTotallyBoundedSupNormBallStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeSupWiderBandGenCentralEigenformsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalHarishChandraFiniteFormBoundedDetNormBanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFormsEquicontinuousOnBandStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsUniformlySmallOutsideCompactBandStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyBoundedSupOfEquicontinuousInvariantTailsStatement

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Treat this case separately.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

A detailed English derivation is pending.
-/
theorem finiteDimensional_cuspGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ V : Submodule ℂ (Sm E a), V ≤ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) → (∀ φ ∈ V, IsCuspidal φ.1) → FiniteDimensional ℂ V := by
  intro E _ _ _ a L hL W hW X hX N V hV hc
  have hleft : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ (γ : GL (Fin a) E) (g : GA E a),
      φ.1 (ratGL E a γ * g) = φ.1 g := by
    intro φ hφ γ g
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hx.1.left γ g
    | zero => rfl
    | add x y _ _ hx hy =>
      change x.1 (ratGL E a γ * g) + y.1 (ratGL E a γ * g) = x.1 g + y.1 g
      rw [hx, hy]
    | smul c x _ hx =>
      change c * x.1 (ratGL E a γ * g) = c * x.1 g
      rw [hx]
  let V' : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  have hfin : FiniteDimensional ℂ V' := by
    refine GlobalTheory.T.finiteDimensional_of_totallyBounded_supNormBall (GA E a) V' (band E a) ?_ ?_ ?_
    · rintro _ ⟨φ, hφ, rfl⟩ h0
      funext g
      obtain ⟨C, hC⟩ := GlobalTheory.T.norm_le_sup_wider_band_genCentralEigenforms E a L hL W hW X hX N (max 1 (max (absDetA g) (absDetA g)⁻¹)) (le_max_left _ _)
      have hp := absDetA_pos g
      have h1 : (max 1 (max (absDetA g) (absDetA g)⁻¹))⁻¹ ≤ absDetA g := by
        rw [inv_le_comm₀ (by positivity) hp]
        exact (le_max_right _ _).trans (le_max_right _ _)
      have h2 : absDetA g ≤ 2 * max 1 (max (absDetA g) (absDetA g)⁻¹) := by
        have := (le_max_left (absDetA g) (absDetA g)⁻¹).trans (le_max_right 1 _)
        have := le_max_left 1 (max (absDetA g) (absDetA g)⁻¹)
        linarith
      have := hC φ (hV hφ) 0 (fun h hh => by rw [show φ.1 h = 0 from h0 h hh, norm_zero]) g h1 h2
      simpa using this
    · rintro _ ⟨φ, hφ, rfl⟩
      exact GlobalTheory.T.cuspidal_harishChandraFiniteForm_bounded_detNormBand E a L hL W hW X hX N φ (hV hφ) (hc φ hφ)
    · intro ε hε
      obtain ⟨F, hF⟩ := GlobalTheory.T.totallyBounded_sup_of_equicontinuous_invariant_tails (GA E a) (Set.range (ratGL E a)) (band E a)
        {f | ∃ φ ∈ V, φ.1 = f ∧ ∀ x ∈ band E a, ‖f x‖ ≤ 1}
        (by rintro f ⟨φ, hφ, rfl, -⟩ s ⟨γ, rfl⟩ g; exact hleft φ (hV hφ) γ g)
        (by rintro f ⟨φ, -, rfl, hb⟩; exact hb)
        (by
          intro ε hε
          obtain ⟨U, hU, h⟩ := GlobalTheory.T.harishChandraForms_equicontinuous_on_band E a L hL W hW X hX N ε hε
          refine ⟨U, hU, ?_⟩
          rintro f ⟨φ, hφ, rfl, hb⟩ g hg u hu hgu
          simpa using h φ (hV hφ) 1 hb g hg u hu hgu)
        (by
          intro ε hε
          obtain ⟨C, hC, hCB, h⟩ := GlobalTheory.T.cuspForms_uniformly_small_outside_compact_band E a L hL W hW X hX N ε hε
          refine ⟨C, hC, hCB, fun g hg => ?_⟩
          rcases h g hg with ⟨γ, hγ⟩ | h'
          · exact Or.inl ⟨_, ⟨γ, rfl⟩, hγ⟩
          · refine Or.inr ?_
            rintro f ⟨φ, hφ, rfl, hb⟩
            simpa using h' φ (hV hφ) (hc φ hφ) 1 hb) ε hε
      refine ⟨F, ?_⟩
      rintro _ ⟨φ, hφ, rfl⟩ hb
      exact hF _ ⟨φ, hφ, rfl, hb⟩
  exact (Submodule.equivMapOfInjective (Sm E a).subtype Subtype.val_injective V).symm.finiteDimensional

end GlobalTheory.HCF

end
