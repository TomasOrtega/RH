import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.HeckeLevelWordBase

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `h1 : Valued.v (u : w.adicCompletion E) ≠ 0` using `(Valuation.ne_zero_iff _).mpr u.ne_zero`. Unfold `ordL at hu`. Rewrite `hu` using `[dif_neg h1]`. Rewrite using `[← WithZero.coe_unzero h1]`. Establish `e : Multiplicative.toAdd (WithZero.unzero h1) = 0` using `by omega`.

Establish `e' : WithZero.unzero h1 = 1`. Rewrite using `[← ofAdd_toAdd (WithZero.unzero h1), e]`. Both sides reduce to the same expression. Rewrite using `[e']`. Both sides reduce to the same expression.
-/
private theorem val_one_of_ordL {E : Type} [Field E] [NumberField E] {w : Pl E} (u : (w.adicCompletion E)ˣ)
    (hu : ordL (u : w.adicCompletion E) = 0) : Valued.v (u : w.adicCompletion E) = 1 := by
  have h1 : Valued.v (u : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
  unfold ordL at hu
  rw [dif_neg h1] at hu
  rw [← WithZero.coe_unzero h1]
  have e : Multiplicative.toAdd (WithZero.unzero h1) = 0 := by omega
  have e' : WithZero.unzero h1 = 1 := by
    rw [← ofAdd_toAdd (WithZero.unzero h1), e]; rfl
  rw [e']; rfl

/- English proof (translation)
Introduce `hR E _ _ _ n π S T F₀ F`. Establish `hsame` using `F.same`. Unfold `RF_same at hsame`. Take `⟨hS₀, hBad, hμ, -⟩` from `hsame`. Establish `hloc : ∀ w, F.d.μ w = F₀.μ.loc w` using `fun w => by rw [hμ]; exact F₀.μloc w`.

Use `⟨hloc, fun w u => ?_, fun w hw hB hs => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hloc]`. Conclude with `F₀.hμ.1 _`. Establish `hT : w ∉ F.d.T` using `fun h => hB (by simp [LocData.B, h])`. Establish `hS : w ∉ F.d.S₀` using `fun h => hB (by simp [LocData.B, h])`.

Establish `hb : w ∉ F.d.Bad` using `fun h => hB (by simp [LocData.B, h])`. Use `⟨hs, hT, hS, hb, fun u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[hloc]`. Conclude with `(F₀.good w hw (hS₀ ▸ hS) (hBad ▸ hb)).2 u (val_one_of_ordL u hu)`. Introduce `w hw`.

Establish `hw' : w ∈ F.d.T ∪ F.d.S₀` using `by simpa [LocData.P] using hw`. Break down `Finset.mem_union.mp hw' with h | h` into its components or cases. Conclude with `(F.T_in w h).1`. Conclude with `(F₀.S₀ w (hS₀ ▸ h)).1`.
-/
theorem frfacts_pf : FrFacts := by
  intro hR E _ _ _ n π S T F₀ F
  have hsame := F.same
  unfold RF_same at hsame
  obtain ⟨hS₀, hBad, hμ, -⟩ := hsame
  have hloc : ∀ w, F.d.μ w = F₀.μ.loc w := fun w => by rw [hμ]; exact F₀.μloc w
  refine ⟨hloc, fun w u => ?_, fun w hw hB hs => ?_, ?_⟩
  · rw [hloc]
    exact F₀.hμ.1 _
  · have hT : w ∉ F.d.T := fun h => hB (by simp [LocData.B, h])
    have hS : w ∉ F.d.S₀ := fun h => hB (by simp [LocData.B, h])
    have hb : w ∉ F.d.Bad := fun h => hB (by simp [LocData.B, h])
    refine ⟨hs, hT, hS, hb, fun u hu => ?_⟩
    rw [hloc]
    exact (F₀.good w hw (hS₀ ▸ hS) (hBad ▸ hb)).2 u (val_one_of_ordL u hu)
  · intro w hw
    have hw' : w ∈ F.d.T ∪ F.d.S₀ := by simpa [LocData.P] using hw
    rcases Finset.mem_union.mp hw' with h | h
    · exact (F.T_in w h).1
    · exact (F₀.S₀ w (hS₀ ▸ h)).1

end UpperTheory.BaseChangeIdentities.FrameWordIdentity

end
