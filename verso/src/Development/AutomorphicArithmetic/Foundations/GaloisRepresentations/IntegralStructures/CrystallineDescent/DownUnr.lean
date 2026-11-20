import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsAlt
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ _ l _ ι a π Q P hP ρ w B hB hQdec hyp hl A h`. Take `⟨w', hunder, h', hN⟩` from `GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A h (hQdec A h)`. Establish `hB' : (CG.mk P).HasSat w' B`. Establish `e` using `hP.sat w' 1 B (by rw [pow_one, hunder, hN]) (hunder ▸ hB)`. Simplify using `using e`.

Establish `hlw : ((l : ℕ) : 𝓞 Q.K) ∉ w'.asIdeal`. Introduce `hw`. Apply `hl` to reduce the goal to its premises. Establish `e1` using `(h ((l : ℕ) : 𝓞 E))`. Establish `e2` using `(h' ((l : ℕ) : 𝓞 Q.K))`.

Simplify using `only [map_natCast] at e1 e2`. Conclude with `e1.1 (e2.2 hw)`. Establish `hcl` using `hyp w' hunder hB' hlw A h'`. Rewrite `hcl` using `[hN]`. Use `⟨fun s hs => ?_, fun σ hσ => ?_⟩` and prove the remaining obligations.

Take `⟨s', rfl⟩` from `hQdec A h (Ine_le_Dec A hs)`. Conclude with `hcl.1 s' hs`. Take `⟨σ', rfl⟩` from `hQdec A h hσ.1`. Establish `e` using `hcl.2 σ' hσ`. Rewrite using `[← map_inv]`.

Conclude with `e`.
-/
theorem UpperTheory.Gal.Int.Core.downUnr_holds :
    SphDown .unr := by
  intro E Ω _ _ _ _ _ _ l _ ι a π Q P hP ρ w B hB hQdec hyp hl A h
  obtain ⟨w', hunder, h', hN⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A h (hQdec A h)
  have hB' : (CG.mk P).HasSat w' B := by
    have e := hP.sat w' 1 B (by rw [pow_one, hunder, hN]) (hunder ▸ hB)
    simpa using e
  have hlw : ((l : ℕ) : 𝓞 Q.K) ∉ w'.asIdeal := by
    intro hw
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 E))
    have e2 := (h' ((l : ℕ) : 𝓞 Q.K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have hcl := hyp w' hunder hB' hlw A h'
  rw [hN] at hcl
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · obtain ⟨s', rfl⟩ := hQdec A h (Ine_le_Dec A hs)
    exact hcl.1 s' hs
  · obtain ⟨σ', rfl⟩ := hQdec A h hσ.1
    have e := hcl.2 σ' hσ
    rw [← map_inv]
    exact e
