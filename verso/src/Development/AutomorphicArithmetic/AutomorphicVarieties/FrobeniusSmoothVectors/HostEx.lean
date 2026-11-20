import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GenHost
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrameEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SeedCl

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Fr.host_ex :
    GC.Hypotheses₂ → HostFrameEx := by
  intro hP Ω _ _ _ l _ c _ N _ e ψ o₁ hD σ hσ B hB
  obtain ⟨Hb, hG⟩ := gen_host Ω l c N e ψ o₁ hD σ hσ B hB
  obtain ⟨Q, hQ, hS⟩ := seed_cl Ω l c _ _ σ B _ Hb hG
  obtain ⟨L, i1, i2, i3, i4, g₁, Φ, C₀, w, ⟨k, -⟩, hok, hbig, hw, hwQ, hle⟩ := frame_ex hP l _ _ σ B _ Hb hG Q hQ
  refine ⟨L, i1, i2, i3, i4, g₁, Φ, C₀, ⟨k⟩, hok, hbig, hS L w k.ab k.gal hw hwQ hle ?_⟩
  obtain ⟨h, hg⟩ := k.g0
  refine ⟨g₁, ?_, ?_⟩
  · rw [k.gal]
    refine ⟨h, ?_⟩
    have h1 := k.del ⟨g₁, h⟩
    rw [hg] at h1
    exact h1.symm.trans Φ.g0.2
  · have h1 := k.psi ⟨g₁, h⟩
    rw [hg] at h1
    have h2 := hok.baseSubgroup_spec
    rw [h1] at h2
    exact h2
