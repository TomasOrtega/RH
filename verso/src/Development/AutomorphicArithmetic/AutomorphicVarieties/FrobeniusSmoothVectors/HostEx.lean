import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GenHost
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrameEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SeedCl

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

/- English proof (translation)
Introduce `hP Ω _ _ _ l _ c _ N _ e ψ o₁ hD σ hσ B hB`. Take `⟨Hb, hG⟩` from `gen_host Ω l c N e ψ o₁ hD σ hσ B hB`. Take `⟨Q, hQ, hS⟩` from `seed_cl Ω l c _ _ σ B _ Hb hG`. Take `⟨L, i1, i2, i3, i4, g₁, Φ, C₀, w, ⟨k, -⟩, hok, hbig, hw, hwQ, hle⟩` from `frame_ex hP l _ _ σ B _ Hb hG Q hQ`. Use `⟨L, i1, i2, i3, i4, g₁, Φ, C₀, ⟨k⟩, hok, hbig, hS L w k.ab k.gal hw hwQ hle ?_⟩` and prove the remaining obligations.

Take `⟨h, hg⟩` from `k.g0`. Use `⟨g₁, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[k.gal]`. Use `⟨h, ?_⟩` and prove the remaining obligations. Establish `h1` using `k.del ⟨g₁, h⟩`.

Rewrite `h1` using `[hg]`. Conclude with `h1.symm.trans Φ.g0.2`. Establish `h1` using `k.psi ⟨g₁, h⟩`. Rewrite `h1` using `[hg]`. Establish `h2` using `hok.baseSubgroup_spec`.

Rewrite `h2` using `[h1]`. Conclude with `h2`.
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
