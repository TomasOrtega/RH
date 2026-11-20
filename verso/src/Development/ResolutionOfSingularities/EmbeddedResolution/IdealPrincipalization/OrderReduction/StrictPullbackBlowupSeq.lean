import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure StrictPullbackBlowupSeq {X' X : Scheme.{u}} (g : X' ⟶ X)
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) where
  comp : ∀ i : ℕ, i ≤ t.length → (t.schemeAt i ⟶ s.schemeAt i)
  comp_zero : comp 0 (Nat.zero_le _) ≫ s.isoZero.hom = t.isoZero.hom ≫ g
  pullback : ∀ i : ℕ, ∀ hi : i < t.length,
    IsPullback (comp (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) (comp i hi.le)
  length_eq : t.length = s.length
  center_eq : ∀ i : ℕ, ∀ hi : i < t.length,
    t.center i = (s.center i).comap (comp i hi.le)

namespace StrictPullbackBlowupSeq

variable {X' X : Scheme.{u}} {g : X' ⟶ X} {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}

/- English proof (authored)
The comparison data supply equal lengths, the stage maps, their compatibility at stage zero, the pullback square at each blowup, and pullback of each center. These are precisely the conditions for a strict pullback.
-/
theorem isStrictPullback (D : StrictPullbackBlowupSeq g t s) : IsStrictPullbackBlowupSeq g t s :=
  ⟨D.length_eq, D.comp, D.comp_zero, D.pullback, D.center_eq⟩

/- English proof (authored)
The stage-zero compatibility identifies the stage comparison followed by the downstairs initial isomorphism with the upstairs initial isomorphism followed by the base map. Compose with the inverse downstairs isomorphism to solve for the stage comparison.
-/
theorem map_zero_eq (D : StrictPullbackBlowupSeq g t s) :
    D.comp 0 (Nat.zero_le _) = t.isoZero.hom ≫ g ≫ s.isoZero.inv := by
  rw [← Category.assoc, ← D.comp_zero, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/- English proof (authored)
The second projection is the base change of the given flat morphism. Flatness is stable under base change.
-/
private theorem flat_snd_of_isPullback {W₁ W₂ W₃ W₄ : Scheme.{u}}
    {fst : W₁ ⟶ W₂} {snd : W₁ ⟶ W₃} {f : W₂ ⟶ W₄} {gg : W₃ ⟶ W₄}
    (sq : IsPullback fst snd f gg) (hf : AlgebraicGeometry.Flat f) :
    AlgebraicGeometry.Flat snd :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Flat) sq hf

/- English proof (authored)
At stage zero the compatibility square has the two initial isomorphisms on opposite sides, so it is a pullback. The initial stage map is therefore a base change of the flat base map. At each successor the strict pullback square makes the next map a base change of the preceding flat map. Induct to the stated stage.
-/
theorem flat_map [AlgebraicGeometry.Flat g] (D : StrictPullbackBlowupSeq g t s)
    (i : ℕ) (hi : i ≤ t.length) : AlgebraicGeometry.Flat (D.comp i hi) := by
  revert hi
  induction i with
  | zero =>
      intro hi
      have sq : IsPullback t.isoZero.hom (D.comp 0 hi) g s.isoZero.hom :=
        IsPullback.of_horiz_isIso ⟨D.comp_zero.symm⟩
      exact flat_snd_of_isPullback sq inferInstance
  | succ j ih =>
      intro hi
      have hjl : j < t.length := hi
      exact flat_snd_of_isPullback (D.pullback j hjl).flip (ih hjl.le)

/- English proof (authored)
The pullback squares and the initial compatibility make every stage comparison a base change of the original morphism. The base-change theorem for flat surjections gives surjectivity at the chosen stage.
-/
theorem surjective_map [AlgebraicGeometry.Flat g] [AlgebraicGeometry.Surjective g]
    (D : StrictPullbackBlowupSeq g t s) (i : ℕ) (hi : i ≤ t.length) :
    AlgebraicGeometry.Surjective (D.comp i hi) :=
  (flat_and_surjective_of_isPullback_blowupMorphism g t s t.length D.comp D.comp_zero D.pullback i hi).2

end StrictPullbackBlowupSeq

noncomputable def IsStrictPullbackBlowupSeq.toStrictPullbackBlowupSeq {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq g t s) :
    StrictPullbackBlowupSeq g t s where
  comp := h.2.choose
  comp_zero := h.2.choose_spec.1
  pullback := h.2.choose_spec.2.1
  length_eq := h.length_eq
  center_eq := h.2.choose_spec.2.2

/- English proof (authored)
Passing from marked data to the underlying blowup sequence preserves its length. Substitute this equality into the given weak bound.
-/
theorem MarkedBlowupSequenceData.le_toSequenceOfBlowups_length {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (t : MarkedBlowupSequenceData p I m E) {i : ℕ} (hi : i ≤ t.length) :
    i ≤ t.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length := by
  rw [MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups, BlowupSequenceData.toSequenceOfBlowups_length]
  exact hi

/- English proof (authored)
The underlying blowup sequence has the same length as the marked data, so the given strict bound holds for that sequence as well.
-/
theorem MarkedBlowupSequenceData.lt_toSequenceOfBlowups_length {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (t : MarkedBlowupSequenceData p I m E) {i : ℕ} (hi : i < t.length) :
    i < t.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length := by
  rw [MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups, BlowupSequenceData.toSequenceOfBlowups_length]
  exact hi

section

variable {k : Type u} [Field k] {X' X : Scheme.{u}} {q : X' ⟶ Spec (CommRingCat.of k)}
  {g : X' ⟶ X} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} {d : BlowupSequenceData X}

def MarkedBlowupSequenceData.strictPullbackComparisonMap
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ t.length) : t.obj i ⟶ d.obj i :=
  D.comp i (t.le_toSequenceOfBlowups_length hi)

/- English proof (authored)
The marked comparison is defined to be the corresponding comparison map of the underlying sequences, at the same stage.
-/
theorem MarkedBlowupSequenceData.strictPullbackComparisonMap_eq_map
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ t.length) :
    t.strictPullbackComparisonMap D i hi = D.comp i (t.le_toSequenceOfBlowups_length hi) := rfl

/- English proof (authored)
The initial compatibility of the strict pullback says that the two composites to the original downstairs scheme agree. The marked comparison uses this same stage-zero map.
-/
theorem MarkedBlowupSequenceData.strictPullbackComparisonMap_zero
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups) :
    t.strictPullbackComparisonMap D 0 (Nat.zero_le _) ≫ d.isoZero.hom = t.isoZero.hom ≫ g :=
  D.comp_zero

/- English proof (authored)
The marked comparison map is the stage map of the strict pullback of the underlying sequences. The flat stage-map theorem applies at the same index because passing to underlying sequences preserves length.
-/
theorem MarkedBlowupSequenceData.flat_strictPullbackComparisonMap [AlgebraicGeometry.Flat g]
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ t.length) : AlgebraicGeometry.Flat (t.strictPullbackComparisonMap D i hi) := by
  rw [MarkedBlowupSequenceData.strictPullbackComparisonMap_eq_map]
  exact D.flat_map i (t.le_toSequenceOfBlowups_length hi)

/- English proof (authored)
The comparison map is the stage map of the underlying strict pullback. The original base map is flat and surjective, so the stage-map theorem gives surjectivity.
-/
theorem MarkedBlowupSequenceData.surjective_strictPullbackComparisonMap [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.Surjective g]
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ t.length) : AlgebraicGeometry.Surjective (t.strictPullbackComparisonMap D i hi) := by
  rw [MarkedBlowupSequenceData.strictPullbackComparisonMap_eq_map]
  exact D.surjective_map i (t.le_toSequenceOfBlowups_length hi)

/- English proof (authored)
The strict pullback gives equality of lengths of the underlying sequences. Passing from either set of data to its underlying sequence preserves length, which gives the stated equality.
-/
theorem MarkedBlowupSequenceData.length_eq_of_strictPullbackBlowupSeq
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups) :
    t.length = d.length := by
  have h := D.length_eq
  rw [MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups] at h
  simpa only [BlowupSequenceData.toSequenceOfBlowups_length] using h

/- English proof (authored)
Take the strict pullback square for the same index in the underlying sequences. The marked comparison maps and the two blowup maps are the same maps that appear there.
-/
theorem MarkedBlowupSequenceData.isPullback_strictPullbackComparisonMap
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i < t.length) :
    IsPullback (t.strictPullbackComparisonMap D (i + 1) (show i + 1 ≤ t.length from hi)) (t.map i) (d.map i)
      (t.strictPullbackComparisonMap D i hi.le) := by
  have h := D.pullback i (t.lt_toSequenceOfBlowups_length hi)
  rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, BlowupSequenceData.toSequenceOfBlowups_blowupMorphism] at h
  exact h

/- English proof (authored)
The successive comparison maps and the two blowup morphisms form a pullback square. Its commutativity gives equality of these composites.
-/
theorem MarkedBlowupSequenceData.strictPullbackComparisonMap_comp_blowupMorphism
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i < t.length) :
    t.strictPullbackComparisonMap D (i + 1) (show i + 1 ≤ t.length from hi) ≫ d.map i =
      t.map i ≫ t.strictPullbackComparisonMap D i hi.le :=
  (t.isPullback_strictPullbackComparisonMap D i hi).w

/- English proof (authored)
The center condition of a strict pullback gives the upstairs center as the pullback of the downstairs one at the step. The marked centers and comparison map are those of the underlying sequences.
-/
theorem MarkedBlowupSequenceData.center_eq_comap_strictPullbackComparisonMap
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i < t.length) :
    t.center i = (d.center i).comap (t.strictPullbackComparisonMap D i hi.le) :=
  D.center_eq i (t.lt_toSequenceOfBlowups_length hi)

/- English proof (authored)
An exceptional ideal is the pullback of the center along the blowup. Substitute the pullback description of the upstairs center and combine the two consecutive pullbacks. Commutativity of the blowup square gives the other composite, whose pullback is the downstairs exceptional ideal pulled back to the upstairs stage.
-/
theorem MarkedBlowupSequenceData.exceptionalIdeal_eq_comap_strictPullbackComparisonMap
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i < t.length) :
    Blowup.exceptionalIdeal (t.map i) (t.center i) =
      (Blowup.exceptionalIdeal (d.map i) (d.center i)).comap
        (t.strictPullbackComparisonMap D (i + 1) (show i + 1 ≤ t.length from hi)) := by
  have hc : t.center i = (d.center i).comap (t.strictPullbackComparisonMap D i hi.le) := t.center_eq_comap_strictPullbackComparisonMap D i hi
  have hsq : t.strictPullbackComparisonMap D (i + 1) (show i + 1 ≤ t.length from hi) ≫ d.map i =
      t.map i ≫ t.strictPullbackComparisonMap D i hi.le := t.strictPullbackComparisonMap_comp_blowupMorphism D i hi
  rw [Blowup.exceptionalIdeal_eq_comap, Blowup.exceptionalIdeal_eq_comap, hc, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, hsq]

/- English proof (authored)
Induct on the stage. At stage zero both ideals come from the initial ideal, and the stage-zero comparison identity equates the two pullbacks. At a successor, divisibility gives the downstairs controlled-transform identity. Pull it back along the next stage map. The exceptional ideal pulls back to the upstairs exceptional ideal, and pullback commutes with powers and products. By the inductive identity and commutativity of the step square, the other side is the total transform of the preceding upstairs ideal. The upstairs controlled-transform identity has that same total transform. Cancel the common exceptional power, which is locally generated by a nonzerodivisor, to equate the next ideals.
-/
theorem MarkedBlowupSequenceData.ideal_eq_comap_controlledTransform
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hdiv : ∀ i < d.length, ∃ B : (d.obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * B =
        (d.controlledTransform I m i).comap (d.map i))
    (i : ℕ) (hi : i ≤ t.length) :
    t.ideal i = (d.controlledTransform I m i).comap (t.strictPullbackComparisonMap D i hi) := by
  revert hi
  induction i with
  | zero =>
      intro hi
      have h0 : t.strictPullbackComparisonMap D 0 hi ≫ d.isoZero.hom = t.isoZero.hom ≫ g := t.strictPullbackComparisonMap_zero D
      rw [t.ideal_zero, d.controlledTransform_zero I m, ← Scheme.IdealSheafData.comap_comp,
        ← Scheme.IdealSheafData.comap_comp, h0]
  | succ j ih =>
      intro hi
      have hj : j < t.length := hi
      have hjd : j < d.length := by
        have hlen := t.length_eq_of_strictPullbackBlowupSeq D
        omega
      have hct : Blowup.exceptionalIdeal (d.map j) (d.center j) ^ m * d.controlledTransform I m (j + 1) =
          (d.controlledTransform I m j).comap (d.map j) :=
        d.pow_exceptionalIdeal_mul_controlledTransform_succ I m j (hdiv j hjd)
      have hexc : Blowup.exceptionalIdeal (t.map j) (t.center j) =
          (Blowup.exceptionalIdeal (d.map j) (d.center j)).comap (t.strictPullbackComparisonMap D (j + 1) hi) :=
        t.exceptionalIdeal_eq_comap_strictPullbackComparisonMap D j hj
      have hcomp : t.strictPullbackComparisonMap D (j + 1) hi ≫ d.map j = t.map j ≫ t.strictPullbackComparisonMap D j hj.le :=
        t.strictPullbackComparisonMap_comp_blowupMorphism D j hj
      have hih : t.ideal j = (d.controlledTransform I m j).comap (t.strictPullbackComparisonMap D j hj.le) := ih hj.le
      have hsucc : Blowup.exceptionalIdeal (t.map j) (t.center j) ^ m * t.ideal (j + 1) =
          (t.ideal j).comap (t.map j) := t.ideal_succ j hj
      have main : Blowup.exceptionalIdeal (t.map j) (t.center j) ^ m *
          (d.controlledTransform I m (j + 1)).comap (t.strictPullbackComparisonMap D (j + 1) hi) =
          Blowup.exceptionalIdeal (t.map j) (t.center j) ^ m * t.ideal (j + 1) := by
        rw [hsucc, hih, hexc, ← Scheme.IdealSheafData.comap_pow,
          ← Scheme.IdealSheafData.comap_mul, hct, ← Scheme.IdealSheafData.comap_comp,
          ← Scheme.IdealSheafData.comap_comp, hcomp]
      exact (((isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal
        (t.isBlowup j hj)).pow m).eq_of_mul_eq_mul main).symm

/- English proof (authored)
At stage zero both lists come from the original boundary, and compatibility of the initial maps equates the entrywise pullbacks. At a successor, each list consists of the strict transforms of the preceding entries followed by the exceptional ideal. The comparison map on the preceding stages is flat. With the local Noetherian hypotheses, flat pullback commutes with the strict transform across the blowup square. Apply this to each entry using the inductive equality. The exceptional ideals also agree by pullback, giving equality of the entire lists.
-/
theorem MarkedBlowupSequenceData.boundary_eq_comap_strictPullbackComparisonMap [AlgebraicGeometry.Flat g]
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hNd : ∀ i ≤ d.length, IsLocallyNoetherian (d.obj i))
    (hNt : ∀ i ≤ t.length, IsLocallyNoetherian (t.obj i))
    (i : ℕ) (hi : i ≤ t.length) :
    t.boundary i = (d.boundaryFrom E i).map (fun A => A.comap (t.strictPullbackComparisonMap D i hi)) := by
  revert hi
  induction i with
  | zero =>
      intro hi
      have h0 : t.strictPullbackComparisonMap D 0 hi ≫ d.isoZero.hom = t.isoZero.hom ≫ g := t.strictPullbackComparisonMap_zero D
      have key : ∀ A : X.IdealSheafData,
          (A.comap g).comap t.isoZero.hom =
            (A.comap d.isoZero.hom).comap (t.strictPullbackComparisonMap D 0 hi) := by
        intro A
        rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, h0]
      rw [MarkedBlowupSequenceData.boundary_zero, BlowupSequenceData.boundary_zero]
      simp only [List.map_map, Function.comp_def, key]
  | succ j ih =>
      intro hi
      have hj : j < t.length := hi
      have hlen : t.length = d.length := t.length_eq_of_strictPullbackBlowupSeq D
      have hjd : j < d.length := by omega
      have : IsLocallyNoetherian (d.obj (j + 1)) := hNd (j + 1) hjd
      have : IsLocallyNoetherian (t.obj (j + 1)) := hNt (j + 1) hi
      have : AlgebraicGeometry.Flat (t.strictPullbackComparisonMap D j hj.le) := t.flat_strictPullbackComparisonMap D j hj.le
      have hst : ∀ A : (d.obj j).IdealSheafData,
          Blowup.strictTransform (t.map j) (t.center j) (A.comap (t.strictPullbackComparisonMap D j hj.le)) =
            (Blowup.strictTransform (d.map j) (d.center j) A).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by
        intro A
        have h := comap_strictTransform_of_flat_of_isLocallyNoetherian (d.map j)
          (t.strictPullbackComparisonMap D j hj.le) (t.map j) (t.strictPullbackComparisonMap D (j + 1) hi)
          (t.isPullback_strictPullbackComparisonMap D j hj) (d.center j) A (d.isBlowup j hjd)
        rw [h, t.center_eq_comap_strictPullbackComparisonMap D j hj]
      have hexc : Blowup.exceptionalIdeal (t.map j) (t.center j) =
          (Blowup.exceptionalIdeal (d.map j) (d.center j)).comap (t.strictPullbackComparisonMap D (j + 1) hi) :=
        t.exceptionalIdeal_eq_comap_strictPullbackComparisonMap D j hj
      rw [t.boundary_succ j hj, ih hj.le, d.boundary_succ E j]
      simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
        Function.comp_def, hst, hexc]

end

end FunctorialResolution.EmbeddedResolution

end
