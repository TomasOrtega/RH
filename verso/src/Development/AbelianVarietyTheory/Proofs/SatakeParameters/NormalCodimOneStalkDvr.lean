import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.X0OfStarCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeakRepIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRepConjInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClauseAtOfRepIso

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut

namespace GlobalTheory.RoadW

/- English proof (translation)
Consider the cases of `c with`. Consider the case `unr`. Take `⟨p, hp⟩` from `hiso`. Introduce `hl A hA`. Take `⟨h1, h2⟩` from `hc hl A hA`.

Use `⟨fun s hs => by rw [hp, h1 s hs]; group, fun σ hσ => ?_⟩` and prove the remaining obligations. Rewrite using `[← h2 σ hσ, hp, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]`. Consider the case `dR => exact clauseAt_of_repIso E Ω l ι a π r r' hr hiso .dR w hc`. Consider the case `crys => exact clauseAt_of_repIso E Ω l ι a π r r' hr hiso .crys w hc`. Consider the case `phi`.

Take `⟨p, hp⟩` from `hiso`. Establish `hcd : ∀ (A : ValuationSubring Ω) (g : ↥(Dec (F` using `E) A)), r'.comp (Dec (F := E) A).subtype g = p * r.comp (Dec (F := E) A).subtype g * p⁻¹ := fun A g => hp g`. Introduce `P AI hT A h O _ _ _ Bw hj g`. Establish `e` using `GlobalTheory.AboveL.RepConj.wdAt_conj P ι Bw h hj p (hcd A)`. Conclude with `(congrArg (fun x => WD.charPol x g) e).trans (hc P AI hT A h O Bw hj g)`.
-/
theorem sphAt_of_repIso {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : CuspSub E a) {r r' : G E Ω →* GL (Fin a) (Qbar l)}
    (hr : Continuous r) (hiso : UpperTheory.V.Af.RepIso r r') (c : GlobalTheory.RoadU.Sph) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ)
    (hc : GlobalTheory.RoadU.SphAt c π ι r w B) : GlobalTheory.RoadU.SphAt c π ι r' w B := by
  cases c with
  | unr =>
    obtain ⟨p, hp⟩ := hiso
    intro hl A hA
    obtain ⟨h1, h2⟩ := hc hl A hA
    refine ⟨fun s hs => by rw [hp, h1 s hs]; group, fun σ hσ => ?_⟩
    rw [← h2 σ hσ, hp, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  | dR => exact clauseAt_of_repIso E Ω l ι a π r r' hr hiso .dR w hc
  | crys => exact clauseAt_of_repIso E Ω l ι a π r r' hr hiso .crys w hc
  | phi =>
    obtain ⟨p, hp⟩ := hiso
    have hcd : ∀ (A : ValuationSubring Ω) (g : ↥(Dec (F := E) A)), r'.comp (Dec (F := E) A).subtype g =
        p * r.comp (Dec (F := E) A).subtype g * p⁻¹ := fun A g => hp g
    intro P AI hT A h O _ _ _ Bw hj g
    have e := GlobalTheory.AboveL.RepConj.wdAt_conj P ι Bw h hj p (hcd A)
    exact (congrArg (fun x => WD.charPol x g) e).trans (hc P AI hT A h O Bw hj g)

/- English proof (translation)
Introduce `h`. Use `⟨fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hs => ?_, fun c E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w _ B hB => ?_⟩` and prove the remaining obligations. Take `rfl : χ = quadChar E ^ a` from `hs.2.2.2`. Take `⟨r, hr, -⟩` from `h E Ω l ι a ha π hs`. Conclude with `⟨r, hr⟩`.

Take `rfl : χ = quadChar E ^ a` from `hs.2.2.2`. Take `⟨r₀, hr₀, hc⟩` from `h E Ω l ι a ha π hs`. Use `sphAt_of_repIso ι π hr₀.1 (weak_repIso E Ω l ι a π r₀ r hr₀ hr) c w B ?_` and prove the remaining obligations. Take `⟨h1, h2, h3, h4⟩` from `hc w B hB`. Consider the cases of `c`.

Use `exacts [h1, h2, h3, h4]`.
-/
theorem core_of_rowStarCore : GlobalTheory.RoadW.RowStarCore → GlobalTheory.RoadU.Core := by
  intro h
  refine ⟨fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hs => ?_, fun c E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w _ B hB => ?_⟩
  · obtain rfl : χ = quadChar E ^ a := hs.2.2.2
    obtain ⟨r, hr, -⟩ := h E Ω l ι a ha π hs
    exact ⟨r, hr⟩
  · obtain rfl : χ = quadChar E ^ a := hs.2.2.2
    obtain ⟨r₀, hr₀, hc⟩ := h E Ω l ι a ha π hs
    refine sphAt_of_repIso ι π hr₀.1 (weak_repIso E Ω l ι a π r₀ r hr₀ hr) c w B ?_
    obtain ⟨h1, h2, h3, h4⟩ := hc w B hB
    cases c
    exacts [h1, h2, h3, h4]

end GlobalTheory.RoadW
