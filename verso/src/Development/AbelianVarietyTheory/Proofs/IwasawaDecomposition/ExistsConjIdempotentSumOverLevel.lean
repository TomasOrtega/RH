import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.HalfLevelConj

/- English proof (translation)
Introduce `D N e P hE hN`. Use `⟨cA D e, P.image Formalism.L2.DIV.conjPl, Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj hE, ?_, ?_⟩` and prove the remaining obligations. Introduce `Q hQ`. Take `⟨PP, hPP, rfl⟩` from `Finset.mem_image.1 hQ`. Establish `hmem : ((N : ℕ) : 𝓞 D.host.E) ∈ (Formalism.L2.DIV.conjPl PP).asIdeal ↔ Formalism.L2.DIV.starO ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal` using `Iff.rfl`.

Establish `hs : Formalism.L2.DIV.starO ((N : ℕ) : 𝓞 D.host.E) = ((N : ℕ) : 𝓞 D.host.E)`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[Formalism.L2.DIV.starO_coe]`. Simplify using the standard rewrite rules. Rewrite using `[hmem, hs]`.

Conclude with `hN PP hPP`. Rewrite using `[Formalism.L2.Theta.cA_cA]`.
-/
theorem exists_conj_idemSum : ∀ (D : D7) (N : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P →
    (∀ PP ∈ P, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ (e' : AE D) (P' : Finset (Formalism.L2.DIV.Pl D.host.E)),
    IsIdemSum e' P' ∧ (∀ PP ∈ P', ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ cA D e' = e := by
  intro D N e P hE hN
  classical
  refine ⟨cA D e, P.image Formalism.L2.DIV.conjPl, Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj hE, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ
    have hmem : ((N : ℕ) : 𝓞 D.host.E) ∈ (Formalism.L2.DIV.conjPl PP).asIdeal ↔
        Formalism.L2.DIV.starO ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := Iff.rfl
    have hs : Formalism.L2.DIV.starO ((N : ℕ) : 𝓞 D.host.E) = ((N : ℕ) : 𝓞 D.host.E) := by
      apply RingOfIntegers.ext
      rw [Formalism.L2.DIV.starO_coe]
      simp
    rw [hmem, hs]
    exact hN PP hPP
  · rw [Formalism.L2.Theta.cA_cA]

end GlobalTheory.HalfLevelConj
