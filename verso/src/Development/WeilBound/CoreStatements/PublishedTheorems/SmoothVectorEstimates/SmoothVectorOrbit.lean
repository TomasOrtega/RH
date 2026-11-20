import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace SmoothVectorOrbit

/- English proof (translation)
Use function extensionality and compare the values at `M`. Simplify using `only [PositivityTheory.jumpWindows.orb, Pi.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem orb_smul {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (c : ℂ) (v : X) :
    orb ρ (c • v) = c • orb ρ v := by
  funext M
  simp only [PositivityTheory.jumpWindows.orb, Pi.smul_apply]
  split_ifs <;> simp

/- English proof (translation)
Unfold `PositivityTheory.jumpWindows.SmV at h ⊢`. Rewrite using `[PositivityTheory.jumpWindows.SmoothVectorOrbit.orb_smul]`. Conclude with `h.const_smul c`.
-/
theorem smV_smul {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (c : ℂ) (v : X) (h : SmV ρ v) : SmV ρ (c • v) := by
  unfold PositivityTheory.jumpWindows.SmV at h ⊢
  rw [PositivityTheory.jumpWindows.SmoothVectorOrbit.orb_smul]
  exact h.const_smul c

end SmoothVectorOrbit

/- English proof (translation)
Introduce `hAC hSW hSP hWS hWV`. Unfold `PositivityTheory.jumpWindows.G8 PositivityTheory.jumpWindows.ForE`. Introduce `E _ _ _ a ψ hψ S hS Y hY φ hφY hφ0 hφsm hφsph hφeig`. Take `⟨-, -, -, -, -, -, -, -, -, -, hreg, -⟩` from `hAC E a`. Take `⟨hΛ, htr, -, hW⟩` from `hSW E a ψ hψ`.

Take `⟨hsmooth, hsph, hsph_smul, -, -⟩` from `hSP E a S`. Take `⟨-, hYtr, hYmir⟩` from `hY`. Take `⟨hWcont, hWne, -⟩` from `hW φ (hYmir φ hφY)`. Take `⟨g, hg⟩` from `hWne hφ0`. Take `⟨g₀, harch, hloc, hsupp⟩` from `hreg S g`.

Establish `hg₀ : PositivityTheory.jumpWindows.Wh ψ φ g₀ ≠ 0`. Introduce `h0`. Use `hg (hWV E a S _ hWcont ?_ g g₀ harch hloc hsupp h0)` and prove the remaining obligations. Introduce `w hw h hh h0' u`. Take `⟨B, hB⟩` from `hφeig w hw`.

Conclude with `hWS E a ψ hψ w (hS w hw) B φ (hYmir φ hφY) hB h hh h0' u`. Establish `hφ'Y : PositivityTheory.jumpWindows.Rt E a g₀ φ ∈ Y` using `hYtr g₀ hsupp φ hφY`. Establish `hW1 : PositivityTheory.jumpWindows.Wh ψ (PositivityTheory.jumpWindows.Rt E a g₀ φ) 1 ≠ 0`. Rewrite using `[htr, one_mul]`. Conclude with `hg₀`.

Use `⟨(PositivityTheory.jumpWindows.Wh ψ (PositivityTheory.jumpWindows.Rt E a g₀ φ) 1)⁻¹ • PositivityTheory.jumpWindows.Rt E a g₀ φ, Y.smul_mem _ hφ'Y, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `PositivityTheory.jumpWindows.SmoothVectorOrbit.smV_smul _ _ _ (hsmooth g₀ φ hφsm)`. Conclude with `hsph_smul _ _ (hsph g₀ φ hφsph)`. Take `⟨Λ, hΛ1⟩` from `hΛ 1`. Rewrite using `[← hΛ1 _ (hYmir _ (Y.smul_mem _ hφ'Y)), map_smul, hΛ1 _ (hYmir _ hφ'Y), smul_eq_mul, inv_mul_cancel₀ hW1]`.
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
