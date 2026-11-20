import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace SmoothVectorOrbit

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem orb_smul {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (c : ℂ) (v : X) :
    orb ρ (c • v) = c • orb ρ v := by
  funext M
  simp only [PositivityTheory.jumpWindows.orb, Pi.smul_apply]
  split_ifs <;> simp

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem smV_smul {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (c : ℂ) (v : X) (h : SmV ρ v) : SmV ρ (c • v) := by
  unfold PositivityTheory.jumpWindows.SmV at h ⊢
  rw [PositivityTheory.jumpWindows.SmoothVectorOrbit.orb_smul]
  exact h.const_smul c

end SmoothVectorOrbit

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem smooth_vector_orbit_invariance : G0 → G5 → G5b → G9 → PlacewiseToOutsideS → G8 := by
  intro hAC hSW hSP hWS hWV
  unfold PositivityTheory.jumpWindows.G8 PositivityTheory.jumpWindows.ForE
  intro E _ _ _ a ψ hψ S hS Y hY φ hφY hφ0 hφsm hφsph hφeig
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hreg, -⟩ := hAC E a
  obtain ⟨hΛ, htr, -, hW⟩ := hSW E a ψ hψ
  obtain ⟨hsmooth, hsph, hsph_smul, -, -⟩ := hSP E a S
  obtain ⟨-, hYtr, hYmir⟩ := hY
  obtain ⟨hWcont, hWne, -⟩ := hW φ (hYmir φ hφY)
  obtain ⟨g, hg⟩ := hWne hφ0
  obtain ⟨g₀, harch, hloc, hsupp⟩ := hreg S g
  have hg₀ : PositivityTheory.jumpWindows.Wh ψ φ g₀ ≠ 0 := by
    intro h0
    refine hg (hWV E a S _ hWcont ?_ g g₀ harch hloc hsupp h0)
    intro w hw h hh h0' u
    obtain ⟨B, hB⟩ := hφeig w hw
    exact hWS E a ψ hψ w (hS w hw) B φ (hYmir φ hφY) hB h hh h0' u
  have hφ'Y : PositivityTheory.jumpWindows.Rt E a g₀ φ ∈ Y := hYtr g₀ hsupp φ hφY
  have hW1 : PositivityTheory.jumpWindows.Wh ψ (PositivityTheory.jumpWindows.Rt E a g₀ φ) 1 ≠ 0 := by
    rw [htr, one_mul]
    exact hg₀
  refine ⟨(PositivityTheory.jumpWindows.Wh ψ (PositivityTheory.jumpWindows.Rt E a g₀ φ) 1)⁻¹ •
      PositivityTheory.jumpWindows.Rt E a g₀ φ, Y.smul_mem _ hφ'Y, ?_, ?_, ?_⟩
  · exact PositivityTheory.jumpWindows.SmoothVectorOrbit.smV_smul _ _ _ (hsmooth g₀ φ hφsm)
  · exact hsph_smul _ _ (hsph g₀ φ hφsph)
  · obtain ⟨Λ, hΛ1⟩ := hΛ 1
    rw [← hΛ1 _ (hYmir _ (Y.smul_mem _ hφ'Y)), map_smul, hΛ1 _ (hYmir _ hφ'Y), smul_eq_mul,
      inv_mul_cancel₀ hW1]

end PositivityTheory.jumpWindows

end
