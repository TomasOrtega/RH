import Formalism.LocalToGlobal.GlobalTheory.GL5.TheoremThreeAllUnitary

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice

/- English proof (translation)
Use `letI := D.host.cmStar`. Introduce `W P Q hS hsig hM s hs`. Take `⟨x, hx, W', ι, hι, hr, hS', hsig', hvol⟩` from `hV W P Q hS hsig hM s hs`. Use `⟨x, hx, W', ι, hι, hr, hS', hsig', ?_⟩` and prove the remaining obligations. Take `⟨⟨μ, hμ⟩, hall⟩` from `hT W P Q hS hsig`.

Take `⟨⟨F0, hF0⟩, hF⟩` from `hall μ hμ`. Establish `hsig'' : ∀ τ, W'.sig τ = ((if s then P - 1 else P), (if s then Q else Q - 1))`. Apply the tactic sequence `intro τ; rw [hsig' τ]; cases s <;> rfl`. Take `⟨⟨μ', hμ'⟩, hall'⟩` from `hT W' _ _ hS' hsig''`. Take `⟨⟨F1, hF1⟩, hF'⟩` from `hall' μ' hμ'`.

Establish `e` using `hvol μ F0 μ' F1 hμ hF0 hμ' hF1`. Rewrite `e` using `[hF F0 hF0, hF' F1 hF1, ENNReal.toReal_ofReal (D.vol_pos W).le, ENNReal.toReal_ofReal (D.vol_pos W').le]`. Conclude with `e`.
-/
theorem theorem_two_of_volume_ratio (D : D7) (hV : VolRatioTrue D) (hT : VolTie D) : Conclusion2 D := by
  letI := D.host.cmStar
  intro W P Q hS hsig hM s hs
  obtain ⟨x, hx, W', ι, hι, hr, hS', hsig', hvol⟩ := hV W P Q hS hsig hM s hs
  refine ⟨x, hx, W', ι, hι, hr, hS', hsig', ?_⟩
  obtain ⟨⟨μ, hμ⟩, hall⟩ := hT W P Q hS hsig
  obtain ⟨⟨F0, hF0⟩, hF⟩ := hall μ hμ
  have hsig'' : ∀ τ, W'.sig τ = ((if s then P - 1 else P), (if s then Q else Q - 1)) := by
    intro τ; rw [hsig' τ]; cases s <;> rfl
  obtain ⟨⟨μ', hμ'⟩, hall'⟩ := hT W' _ _ hS' hsig''
  obtain ⟨⟨F1, hF1⟩, hF'⟩ := hall' μ' hμ'
  have e := hvol μ F0 μ' F1 hμ hF0 hμ' hF1
  rw [hF F0 hF0, hF' F1 hF1, ENNReal.toReal_ofReal (D.vol_pos W).le,
    ENNReal.toReal_ofReal (D.vol_pos W').le] at e
  exact e

/- English proof (translation)
Use `letI := D.host.cmStar`. Introduce `W hW hsig _`. Take `⟨b, -, hb⟩` from `h W hW hsig`. Conclude with `⟨b, hb⟩`.
-/
theorem landherrSmall_of_hasse (D : D7) (h : LandherrHasse D) : LandherrSmall D := by
  letI := D.host.cmStar
  intro W hW hsig _
  obtain ⟨b, -, hb⟩ := h W hW hsig
  exact ⟨b, hb⟩

/- English proof (translation)
Introduce `x i` and use `volumeMass_of_definiteVolume (Fm.D x i) (theorem_two_of_volume_ratio (Fm.D x i) (hV x i) (Formalism.L2.Theta.VolTieG.volTie (hR x i).vol)) (v0 x i)`.
-/
theorem theorem_two_family_of_volume {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hR : TiedRealF Fm) (hV : VolRatioTrueF Fm)
    (v0 : ∀ x (i : Fm.Ix x), DefiniteVolumeEqMass (Fm.D x i)) : FamilyMassVolumeBounds Fm :=
  fun x i => volumeMass_of_definiteVolume (Fm.D x i)
    (theorem_two_of_volume_ratio (Fm.D x i) (hV x i) (Formalism.L2.Theta.VolTieG.volTie (hR x i).vol)) (v0 x i)

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
