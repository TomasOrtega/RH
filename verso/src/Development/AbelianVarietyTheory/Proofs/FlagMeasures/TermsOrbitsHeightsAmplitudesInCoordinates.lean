import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairChangedDualVectorsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesLocalHeightEqResidueCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairAmplitudeMassRepsEqOrbits
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.WCoordTerms

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c`. Take `⟨P₂, c₂, φ, he, hSt, hK0, hUW, hHp, hPT, hdat, hterm, hom, hmov⟩` from `GlobalTheory.T.framePair_changed_dualVectors M hM H r k P S c`. Establish `hlat : ∀ Λ, c₂.lat Λ = c.lat Λ` using `fun Λ => by simp only [Coord.lat, WCoord.lat, he]`. Establish `hrel : ∀ d d', LocNG.Datum.Rel d d' ↔ LocNG.Datum.Rel (φ d) (φ d')`. Introduce `d d'`.

Unfold `LocNG.Datum.Rel`. Rewrite using `[hUW]`. Conclude with `exists_congr fun g => and_congr_right fun _ => hmov g d d'`. Establish `hTR : LocNG.TRel P₂ = LocNG.TRel P`. Use function extensionality and compare the values at `t t'`.

Unfold `LocNG.TRel`. Rewrite using `[hSt]`. Establish `hmu : ∀ t, LocNG.mu P₂ t = LocNG.mu P t` using `fun t => by`. Unfold `LocNG.mu`. Rewrite using `[hSt, hK0]`.

Establish `T2` using `GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P₂ S c₂`. Establish `TD` using `GlobalTheory.HL.CoordDatum.transport M hM H r k P₂ S c₂`. Establish `TH` using `GlobalTheory.HL.CoordHeight.height_eq M hM H r k P₂ S c₂`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `d t ht`.

Establish `h` using `T2.1 (φ d) t ((hterm d t).1 ht)`. Rewrite `h` using `[hdat, hlat, hom d t ht]`. Conclude with `h`. Introduce `d d'`. Rewrite using `[hrel, TD.2.2.1, hdat, hdat]`.

Rewrite using `[← hHp]`. Conclude with `TH.1`. Introduce `hp`. Take `⟨h1, h2, h3⟩` from `TH.2.2 ((hPT).2 hp)`. Establish `hvth : S.vth = 0` using `by simp [Frames.vth, h1]`.

Establish `ha : S.a = 0` using `by simp [Frames.a, h2, hvth]`. Establish `hvD : S.vD = 0` using `Finset.sum_eq_zero fun l _ => by split_ifs with h`. Conclude with `h3 l h.2`. Both sides reduce to the same expression. Simplify using `[Frames.Hp, hvth, ha, hvD]`.

Introduce `R d`. Set `R₂ : LocNG.Reps P₂` to `{ RD := φ '' R.RD RT := fun d₂ => R.RT (φ.symm d₂) hRD := by`. Use `⟨Set.subset_univ _, fun x _ => ?_, ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hr⟩` from `R.hRD.2.1 (φ.symm x) trivial`. Use `⟨φ y, ⟨y, hy, rfl⟩, ?_⟩` and prove the remaining obligations.

Use `(hrel y (φ.symm x)).1 hr` as an intermediate fact. Rewrite `this` using `[φ.apply_symm_apply]`. Then use the resulting hypothesis. Introduce and unpack `_ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h`. Conclude with `congrArg φ (R.hRD.2.2 a ha b hb ((hrel a b).2 h))`. Use `hRT := fun d₂ => by`.

Establish `hs : {t | LocNG.IsTermOver P₂ d₂ t} = {t | LocNG.IsTermOver P (φ.symm d₂) t}`. Use extensionality with `t`. Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[hterm, φ.apply_symm_apply]`. Rewrite using `[hs, hTR]`.

Conclude with `R.hRT _ }`. Establish `hamp : ∀ Q, LocNG.amp R d Q = LocNG.amp R₂ (φ d) Q`. Introduce `Q`. Unfold `LocNG.amp`. Establish `e : R₂.RT (φ d) = R.RT d` using `by simp [R₂]`.

Rewrite using `[e]`. Use `tsum_congr fun t => ?_` and prove the remaining obligations. Rewrite using `[hmu, hom d t.1 ((R.hRT d).1 t.2.1)]`. Establish `A` using `GlobalTheory.HL.CoordAmp.amp_mass_eq M hM H r k P₂ S c₂ R₂ (φ d)`. Rewrite `A` using `[hdat]`.

Conclude with `⟨(hamp _).trans A.1, (hamp _).trans A.2.1⟩`.
-/
theorem terms_orbits_heights_amps : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : WCoord P S), (∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → S.IsTerm (c.dat d) (c.lat t.abelian₂) ∧ LocNG.om P t = S.om (c.dat d) (c.lat t.abelian₂) ∧ (LocNG.BBne (H := H) t ↔ ¬ S.BBzero (c.dat d) (c.lat t.abelian₂))) ∧ (∀ d d' : LocNG.Datum P, LocNG.Datum.Rel d d' ↔ ∃ h ∈ S.H0, h • c.dat d = c.dat d') ∧ P.Hp = S.Hp ∧ (P.PrimeTo → S.Hp = 1) ∧ ∀ (R : LocNG.Reps P) (d : LocNG.Datum P), LocNG.amp R d (LocNG.BBne (H := H)) = S.amp (c.dat d) (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧ LocNG.amp R d (fun t => ¬ LocNG.BBne (H := H) t) = S.amp (c.dat d) (S.BBzero (c.dat d)) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  obtain ⟨P₂, c₂, φ, he, hSt, hK0, hUW, hHp, hPT, hdat, hterm, hom, hmov⟩ := GlobalTheory.T.framePair_changed_dualVectors M hM H r k P S c
  have hlat : ∀ Λ, c₂.lat Λ = c.lat Λ := fun Λ => by simp only [Coord.lat, WCoord.lat, he]
  have hrel : ∀ d d', LocNG.Datum.Rel d d' ↔ LocNG.Datum.Rel (φ d) (φ d') := by
    intro d d'
    unfold LocNG.Datum.Rel
    rw [hUW]
    exact exists_congr fun g => and_congr_right fun _ => hmov g d d'
  have hTR : LocNG.TRel P₂ = LocNG.TRel P := by
    funext t t'
    unfold LocNG.TRel
    rw [hSt]
  have hmu : ∀ t, LocNG.mu P₂ t = LocNG.mu P t := fun t => by
    unfold LocNG.mu
    rw [hSt, hK0]
  have T2 := GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P₂ S c₂
  have TD := GlobalTheory.HL.CoordDatum.transport M hM H r k P₂ S c₂
  have TH := GlobalTheory.HL.CoordHeight.height_eq M hM H r k P₂ S c₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d t ht
    have h := T2.1 (φ d) t ((hterm d t).1 ht)
    rw [hdat, hlat, hom d t ht] at h
    exact h
  · intro d d'
    rw [hrel, TD.2.2.1, hdat, hdat]
  · rw [← hHp]
    exact TH.1
  · intro hp
    obtain ⟨h1, h2, h3⟩ := TH.2.2 ((hPT).2 hp)
    have hvth : S.vth = 0 := by simp [Frames.vth, h1]
    have ha : S.a = 0 := by simp [Frames.a, h2, hvth]
    have hvD : S.vD = 0 := Finset.sum_eq_zero fun l _ => by
      split_ifs with h
      · exact h3 l h.2
      · rfl
    simp [Frames.Hp, hvth, ha, hvD]
  · intro R d
    let R₂ : LocNG.Reps P₂ :=
      { RD := φ '' R.RD
        RT := fun d₂ => R.RT (φ.symm d₂)
        hRD := by
          refine ⟨Set.subset_univ _, fun x _ => ?_, ?_⟩
          · obtain ⟨y, hy, hr⟩ := R.hRD.2.1 (φ.symm x) trivial
            refine ⟨φ y, ⟨y, hy, rfl⟩, ?_⟩
            have := (hrel y (φ.symm x)).1 hr
            rwa [φ.apply_symm_apply] at this
          · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
            exact congrArg φ (R.hRD.2.2 a ha b hb ((hrel a b).2 h))
        hRT := fun d₂ => by
          have hs : {t | LocNG.IsTermOver P₂ d₂ t} = {t | LocNG.IsTermOver P (φ.symm d₂) t} := by
            ext t
            simp only [Set.mem_setOf_eq]
            rw [hterm, φ.apply_symm_apply]
          rw [hs, hTR]
          exact R.hRT _ }
    have hamp : ∀ Q, LocNG.amp R d Q = LocNG.amp R₂ (φ d) Q := by
      intro Q
      unfold LocNG.amp
      have e : R₂.RT (φ d) = R.RT d := by simp [R₂]
      rw [e]
      refine tsum_congr fun t => ?_
      rw [hmu, hom d t.1 ((R.hRT d).1 t.2.1)]
    have A := GlobalTheory.HL.CoordAmp.amp_mass_eq M hM H r k P₂ S c₂ R₂ (φ d)
    rw [hdat] at A
    exact ⟨(hamp _).trans A.1, (hamp _).trans A.2.1⟩

end GlobalTheory.HL.WCoordTerms
