import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjPlace

/- English proof (translation)
Unfold `GlobalTheory.SW.conjI`. Rewrite using `[Ideal.map, Set.image]`. Use `congr 1`. Use extensionality with `a`. Simplify using `only [Set.mem_setOf_eq, SetLike.mem_coe]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, h⟩`. Use `⟨b, hb, ?_⟩` and prove the remaining obligations. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj, h]`.

Both sides reduce to the same expression. Introduce and unpack `⟨b, hb, rfl⟩`. Conclude with `⟨b, hb, by rw [IsCMField.coe_ringOfIntegersComplexConj]; rfl⟩`.
-/
theorem conjI_eq_map {E : Type} [Field E] [NumberField E] [IsCMField E] (P : Ideal (𝓞 E)) :
    GlobalTheory.SW.conjI P = P.map (IsCMField.ringOfIntegersComplexConj E) := by
  unfold GlobalTheory.SW.conjI
  rw [Ideal.map, Set.image]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, by rw [IsCMField.coe_ringOfIntegersComplexConj]; rfl⟩

/- English proof (translation)
Introduce `D PP`. Set `σ` to `IsCMField.ringOfIntegersComplexConj D.host.E`. Use `haveI : (PP.asIdeal.map σ).IsPrime := Ideal.map_isPrime_of_equiv σ`. Establish `hne : PP.asIdeal.map σ ≠ ⊥`. Rewrite using `[Ne, Ideal.map_eq_bot_iff_of_injective σ.injective]`.

Conclude with `PP.ne_bot`. Use `⟨⟨PP.asIdeal.map σ, this, hne⟩, (conjI_eq_map PP.asIdeal).symm, ?_⟩` and prove the remaining obligations. Introduce `c hc`. Take `⟨b, hb, rfl⟩` from `(Ideal.mem_map_of_equiv σ c).1 hc`. Use `⟨b, hb, ?_⟩` and prove the remaining obligations.

Use `show ((b : 𝓞 D.host.E) : D.host.E) = star (((σ b : 𝓞 D.host.E)) : D.host.E)`. Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj]`. Conclude with `(IsCMField.complexConj_apply_apply D.host.E _).symm`.
-/
theorem exists_conj_place : ∀ (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E), ∃ PP' : Formalism.L2.DIV.Pl D.host.E, PP'.asIdeal = conjI PP.asIdeal ∧ Formalism.IndefR.Lev.IsConjPl PP' PP := by
  intro D PP
  let σ := IsCMField.ringOfIntegersComplexConj D.host.E
  haveI : (PP.asIdeal.map σ).IsPrime := Ideal.map_isPrime_of_equiv σ
  have hne : PP.asIdeal.map σ ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective σ.injective]
    exact PP.ne_bot
  refine ⟨⟨PP.asIdeal.map σ, this, hne⟩, (conjI_eq_map PP.asIdeal).symm, ?_⟩
  intro c hc
  obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_of_equiv σ c).1 hc
  refine ⟨b, hb, ?_⟩
  show ((b : 𝓞 D.host.E) : D.host.E) = star (((σ b : 𝓞 D.host.E)) : D.host.E)
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact (IsCMField.complexConj_apply_apply D.host.E _).symm

end GlobalTheory.ConjPlace
