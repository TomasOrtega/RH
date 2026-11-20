import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransformOffCenter
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The nontrivial boundary is obtained by deleting every unit entry. The appended unit is deleted, so the filtered list is the same as the original filtered list.
-/
private theorem sameNontrivialBoundary_append_top {X : Scheme.{u}} (L : List X.IdealSheafData) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (L ++ [⊤]) L := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff]
  induction L with
  | nil => simp [MarkedIdealWithBoundary.nontrivialPart]
  | cons D t ih =>
      simp only [MarkedIdealWithBoundary.nontrivialPart, List.cons_append, List.filter_cons] at ih ⊢
      rw [ih]

/- English proof (authored)
Substitute the equality of the second and third lists in the boundary equivalence. The given equivalence then has the required form.
-/
private theorem sameNontrivialBoundary_of_eq {X : Scheme.{u}} {A B C : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary A B) (e : C = B) : MarkedIdealWithBoundary.SameNontrivialBoundary A C := by
  subst e
  exact h

/- English proof (authored)
The unit ideal is the multiplicative identity. Every power of it is the identity, which leaves J fixed under multiplication.
-/
private theorem top_pow_mul {X : Scheme.{u}} (J : X.IdealSheafData) (m : ℕ) :
    (⊤ : X.IdealSheafData) ^ m * J = J := by
  have e : (1 : X.IdealSheafData) = ⊤ := rfl
  rw [← e, one_pow, one_mul]

/- English proof (authored)
After substituting the equality of indices, the induced comparison between the schemes is the identity and the two stage ideals are the same. The composite is simply f, giving equal pullbacks.
-/
private theorem comap_comp_eqToHom {F : ℕ → Scheme.{u}} (G : ∀ n, (F n).IdealSheafData)
    {a b : ℕ} (h : a = b) {W : Scheme.{u}} (f : W ⟶ F a) :
    (G b).comap (f ≫ eqToHom (congrArg F h)) = (G a).comap f := by
  cases h
  have e : (eqToHom (congrArg F (rfl : a = a)) : F a ⟶ F a) = 𝟙 (F a) := rfl
  rw [e, Category.comp_id]

/- English proof (authored)
Substitute the equality of indices to identify the two lists and make the last map in the composite the identity. Every entry is now pulled back along f on both sides.
-/
private theorem map_comap_comp_eqToHom {F : ℕ → Scheme.{u}} (G : ∀ n, List (F n).IdealSheafData)
    {a b : ℕ} (h : a = b) {W : Scheme.{u}} (f : W ⟶ F a) :
    (G b).map (fun D => D.comap (f ≫ eqToHom (congrArg F h)))
      = (G a).map (fun D => D.comap f) := by
  cases h
  have e : (eqToHom (congrArg F (rfl : a = a)) : F a ⟶ F a) = 𝟙 (F a) := rfl
  rw [e]
  simp

/- English proof (authored)
On W the pullback of the center ideal is the unit ideal. Pulling back the controlled-transform factorization therefore removes the exceptional power, leaving equality of the old ideal pulled back through the transition and the new ideal pulled back directly. Every strict transform pulls back to the pullback of its original ideal because W lies off the center support. The new exceptional entry pulls back to the unit ideal, which disappears from the nontrivial boundary. This gives the boundary equivalence.
-/
private theorem comap_ideal_boundary_succ_of_comap_center_eq_top {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (n : ℕ) (hn : n < s.length)
    {W : Scheme.{u}} (f : W ⟶ s.obj (n + 1))
    (hnoe : AlgebraicGeometry.IsNoetherian (s.obj (n + 1)))
    (hf : (s.center n).comap (f ≫ s.map n) = ⊤) :
    (s.ideal n).comap (f ≫ s.map n) = (s.ideal (n + 1)).comap f ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary ((s.boundary (n + 1)).map (fun D => D.comap f))
        ((s.boundary n).map (fun D => D.comap (f ≫ s.map n))) := by
  have := hnoe
  have he : ((s.center n).comap (s.map n)).comap f = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp]
    exact hf
  have hST : ∀ D : (s.obj n).IdealSheafData,
      (Blowup.strictTransform (s.map n) (s.center n) D).comap f = D.comap (f ≫ s.map n) := by
    intro D
    rw [strictTransform_comap_of_comap_center_eq_top (s.map n) (s.center n) D f he,
      ← Scheme.IdealSheafData.comap_comp]
  constructor
  · have h1 := s.ideal_succ n hn
    simp only [Blowup.exceptionalIdeal_eq_comap] at h1
    have h2 := congrArg (fun J : (s.obj (n + 1)).IdealSheafData => J.comap f) h1
    rw [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow, he,
      top_pow_mul] at h2
    simpa [Scheme.IdealSheafData.comap_comp] using h2.symm
  · have hfun : ((fun D : (s.obj (n + 1)).IdealSheafData => D.comap f) ∘
        Blowup.strictTransform (s.map n) (s.center n))
        = fun D => D.comap (f ≫ s.map n) := by
      funext D
      exact hST D
    rw [s.boundary_succ n hn, List.map_append, List.map_map, List.map_cons, List.map_nil,
      Blowup.exceptionalIdeal_eq_comap, he, hfun]
    exact sameNontrivialBoundary_append_top _

namespace SequenceOfBlowupsPullback

variable {X X' : Scheme.{u}} {φ : X' ⟶ X}

def mapToEarlierScheme {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)
    (j : ℕ) (hj : j ≤ s'.length) (i : ℕ) (hi : i ≤ c.idx j) : s'.schemeAt j ⟶ s.schemeAt i :=
  c.map j hj ≫ s.transitionMap hi

/- English proof (authored)
By definition, the map to the earlier stage first takes the pullback comparison map to the matched stage, then follows the original sequence's transition to the earlier index.
-/
theorem mapToEarlierScheme_eq_map_comp_transitionMap {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)
    (j : ℕ) (hj : j ≤ s'.length) (i : ℕ) (hi : i ≤ c.idx j) :
    c.mapToEarlierScheme j hj i hi = c.map j hj ≫ s.transitionMap hi := rfl

/- English proof (authored)
At the matched index the extra transition goes from that stage to itself and is the identity. The composite is the original comparison map.
-/
theorem mapToEarlierScheme_index {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)
    (j : ℕ) (hj : j ≤ s'.length) :
    c.mapToEarlierScheme j hj (c.idx j) le_rfl = c.map j hj := by
  rw [mapToEarlierScheme_eq_map_comp_transitionMap, SequenceOfBlowups.transitionMap_self_eq_id, Category.comp_id]

/- English proof (authored)
The transition from the matched stage down to i factors through i+1, followed by the single blowup map. Compose this factorization with the comparison map on the pulled back stage.
-/
theorem mapToEarlierScheme_eq_comp_blowupMorphism {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)
    (j : ℕ) (hj : j ≤ s'.length) (i : ℕ) (hi : i < c.idx j) :
    c.mapToEarlierScheme j hj i (le_of_lt hi) = c.mapToEarlierScheme j hj (i + 1) hi ≫ s.transitionMapSucc i := by
  simp only [mapToEarlierScheme_eq_map_comp_transitionMap, SequenceOfBlowups.blowupMorphism_eq_transitionMap, Category.assoc, SequenceOfBlowups.transitionMap_trans]

/- English proof (authored)
The projection from the earlier original stage composed with the transition from the matched original stage is the matched stage's projection. The pullback square at the matched stage then identifies the composite with the projection from the new stage followed by the original base map.
-/
theorem mapToEarlierScheme_comp_projectionToBase {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)
    (j : ℕ) (hj : j ≤ s'.length) (i : ℕ) (hi : i ≤ c.idx j) :
    c.mapToEarlierScheme j hj i hi ≫ s.projectionToBase i = s'.projectionToBase j ≫ φ := by
  rw [mapToEarlierScheme_eq_map_comp_transitionMap, Category.assoc, SequenceOfBlowups.transitionMap_comp_projectionToBase]
  exact (c.isPullback j hj).w

/- English proof (authored)
Induct on the upper index b. At zero the two indices must agree. At b equal to n+1, if a is at most n, induction gives the comparison with the matched index of n, and strict increase then gives the comparison with the matched index of n+1. If a equals n+1 the comparison is reflexive.
-/
private theorem index_mono {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ b : ℕ, b ≤ s'.length → ∀ a : ℕ, a ≤ b → c.idx a ≤ c.idx b := by
  intro b
  induction b with
  | zero =>
      intro _ a ha
      rw [Nat.le_zero.1 ha]
  | succ n ih =>
      intro hb a ha
      rcases Nat.lt_or_ge a (n + 1) with h | h
      · exact le_trans (ih (Nat.le_of_succ_le hb) a (Nat.lt_succ_iff.1 h))
          (le_of_lt (c.idx_strictMono n hb))
      · have hae : a = n + 1 := le_antisymm ha h
        subst hae
        exact le_rfl

/- English proof (authored)
At a stage strictly before the end of the pulled back sequence the matched index is strictly smaller than the original length. At the last stage the matched index equals the original length. Both cases give the bound.
-/
theorem index_le_length {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)
    (j : ℕ) (hj : j ≤ s'.length) : c.idx j ≤ s.length := by
  rcases Nat.lt_or_ge j s'.length with h | h
  · exact le_of_lt (c.idx_lt j h)
  · have hje : j = s'.length := le_antisymm hj h
    subst hje
    exact le_of_eq c.idx_length

/- English proof (authored)
The bound on the matched index puts i within the original steps. If the pulled back center had a point in its support, its image in stage i would be a center point. Its further image in the initial scheme lies in the image of the base map because the comparison commutes with projections. This contradicts the omission property for an unmatched step. The pulled back support is therefore empty and the ideal is the unit ideal.
-/
theorem comap_center_mapToEarlierScheme_eq_top_of_unmatched {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (c : SequenceOfBlowupsPullback φ s' s) (j : ℕ) (hj : j ≤ s'.length) (i : ℕ) (hi : i < c.idx j)
    (hmiss : ∀ j' : ℕ, j' < s'.length → c.idx j' ≠ i) :
    (s.center i).comap (c.mapToEarlierScheme j hj i (le_of_lt hi)) = ⊤ := by
  have hilt : i < s.length := lt_of_lt_of_le hi (c.index_le_length j hj)
  have hw : c.mapToEarlierScheme j hj i (le_of_lt hi) ≫ s.projectionToBase i = s'.projectionToBase j ≫ φ :=
    c.mapToEarlierScheme_comp_projectionToBase j hj i (le_of_lt hi)
  rw [Scheme.IdealSheafData.eq_top_iff_support_eq_empty]
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  rw [Scheme.IdealSheafData.support_comap] at hy
  refine c.omitted i hilt hmiss _ hy ((s'.projectionToBase j).base y) ?_
  have hb : (c.mapToEarlierScheme j hj i (le_of_lt hi) ≫ s.projectionToBase i).base y
      = (s'.projectionToBase j ≫ φ).base y := by rw [hw]
  simpa using hb.symm

/- English proof (authored)
If a pulled back index is at most j, monotonicity puts its matched index at most the match of j and below i. If it is at least j+1, monotonicity puts its match at least the match of j+1 and above i. Thus no pulled back step matches i.
-/
theorem index_ne_of_index_lt_of_lt_index_succ {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (c : SequenceOfBlowupsPullback φ s' s) (j : ℕ) (hj : j + 1 ≤ s'.length) (i : ℕ)
    (hlo : c.idx j < i) (hhi : i < c.idx (j + 1)) :
    ∀ j' : ℕ, j' < s'.length → c.idx j' ≠ i := by
  intro j' hj' hEq
  rcases Nat.lt_or_ge j' (j + 1) with h | h
  · have hm := index_mono c j (Nat.le_of_succ_le hj) j' (Nat.lt_succ_iff.1 h)
    omega
  · have hm := index_mono c j' (le_of_lt hj') (j + 1) h
    omega

/- English proof (authored)
Monotonicity makes the matched index at stage zero a lower bound on all matched indices. Since i is smaller, no actual step has i as its match.
-/
theorem index_ne_of_lt_index_zero {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (c : SequenceOfBlowupsPullback φ s' s) (i : ℕ) (hi : i < c.idx 0) :
    ∀ j' : ℕ, j' < s'.length → c.idx j' ≠ i := by
  intro j' hj' hEq
  have hm := index_mono c j' (le_of_lt hj') 0 (Nat.zero_le _)
  omega

/- English proof (authored)
The matched stage comparison occurs in a pullback square for the given flat base map. Therefore it is flat by stability under base change.
-/
theorem flat_map {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)
    [AlgebraicGeometry.Flat φ] (j : ℕ) (hj : j ≤ s'.length) :
    AlgebraicGeometry.Flat (c.map j hj) := by
  have h : MorphismProperty.IsStableUnderBaseChange (@AlgebraicGeometry.Flat) := inferInstance
  exact h.of_isPullback (c.isPullback j hj).flip inferInstance

/- English proof (authored)
The matched original step is a blowup, and the new center is the pullback of its center under the flat stage comparison. Flat base change of blowup gives a comparison map from the new next stage to the original next stage making a pullback square. On the other hand, the compatibility of transitions shows that the map obtained by going back from the next matched stage also has the required composite to the original current stage. On the new scheme the pulled back center is locally generated by a nonzero divisor, since it is the exceptional ideal of its blowup. Uniqueness in the blowup universal property therefore identifies the two comparison maps. The stated square is the pullback square.
-/
theorem isPullback_blowupMorphism {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)
    [AlgebraicGeometry.Flat φ] (j : ℕ) (hj : j < s'.length) :
    IsPullback (c.mapToEarlierScheme (j + 1) hj (c.idx j + 1) (c.idx_strictMono j hj))
      (s'.transitionMapSucc j) (s.transitionMapSucc (c.idx j)) (c.map j (le_of_lt hj)) := by
  have hidxlt : c.idx j < s.length := c.idx_lt j hj
  have hbl : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc (c.idx j)) (s.center (c.idx j)) :=
    s.isBlowupAlongIdealSheaf_blowupMorphism _ hidxlt
  have : AlgebraicGeometry.Flat (c.map j (le_of_lt hj)) := c.flat_map j (le_of_lt hj)
  have hbj : Blowup.IsBlowupAlongIdealSheaf (s'.transitionMapSucc j) (s'.center j) := s'.isBlowupAlongIdealSheaf_blowupMorphism j hj
  have hbl' : Blowup.IsBlowupAlongIdealSheaf (s'.transitionMapSucc j) ((s.center (c.idx j)).comap (c.map j (le_of_lt hj))) := by
    rw [← c.center_comap j hj]
    exact hbj
  obtain ⟨q, hq, hsq⟩ := hbl.exists_isPullback_of_flat (c.map j (le_of_lt hj)) hbl'
  have hcart0 : Blowup.IsLocallyGeneratedByNonZeroDivisor ((s'.center j).comap (s'.transitionMapSucc j)) := by
    unfold FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf at hbj
    exact hbj.1
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor
      ((s.center (c.idx j)).comap (s'.transitionMapSucc j ≫ c.map j (le_of_lt hj))) := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, ← c.center_comap j hj]
    exact hcart0
  have hstep : c.mapToEarlierScheme (j + 1) hj (c.idx j + 1) (c.idx_strictMono j hj) ≫ s.transitionMapSucc (c.idx j)
      = s'.transitionMapSucc j ≫ c.map j (le_of_lt hj) := by
    rw [← c.mapToEarlierScheme_eq_comp_blowupMorphism (j + 1) hj (c.idx j) (c.idx_strictMono j hj), mapToEarlierScheme_eq_map_comp_transitionMap]
    exact (c.step j hj).symm
  have heq : c.mapToEarlierScheme (j + 1) hj (c.idx j + 1) (c.idx_strictMono j hj) = q :=
    hbl.hom_ext_of_comp_eq hcart hstep hq
  rw [heq]
  exact hsq

private def markedMapToEarlierScheme {k k' : Type u} [Field k] [Field k'] {A B : Scheme.{u}}
    {p : A ⟶ Spec (CommRingCat.of k)} {q : B ⟶ Spec (CommRingCat.of k')} {g : B ⟶ A}
    {I : A.IdealSheafData} {I' : B.IdealSheafData} {m : ℕ} {E : List A.IdealSheafData}
    {E' : List B.IdealSheafData} (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m E')
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (j : ℕ) (hj : j ≤ s'.length) (i : ℕ) (hi : i ≤ c.idx j) : s'.obj j ⟶ s.obj i :=
  c.mapToEarlierScheme j hj i hi

private def markedMap {k k' : Type u} [Field k] [Field k'] {A B : Scheme.{u}}
    {p : A ⟶ Spec (CommRingCat.of k)} {q : B ⟶ Spec (CommRingCat.of k')} {g : B ⟶ A}
    {I : A.IdealSheafData} {I' : B.IdealSheafData} {m : ℕ} {E : List A.IdealSheafData}
    {E' : List B.IdealSheafData} (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m E')
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (j : ℕ) (hj : j ≤ s'.length) : s'.obj j ⟶ s.obj (c.idx j) :=
  c.map j hj

/- English proof (authored)
The projections of the marked data are the underlying sequence projections. Apply the projection formula for the map to the earlier stage and identify those projections with the marked ones.
-/
private theorem markedMapToEarlierScheme_comp_projectionToBase {k k' : Type u} [Field k] [Field k'] {A B : Scheme.{u}}
    {p : A ⟶ Spec (CommRingCat.of k)} {q : B ⟶ Spec (CommRingCat.of k')} {g : B ⟶ A}
    {I : A.IdealSheafData} {I' : B.IdealSheafData} {m : ℕ} {E : List A.IdealSheafData}
    {E' : List B.IdealSheafData} (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m E')
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (j : ℕ) (hj : j ≤ s'.length) (i : ℕ) (hi : i ≤ c.idx j) :
    markedMapToEarlierScheme s s' c j hj i hi ≫ s.proj i = s'.proj j ≫ g := by
  have h := c.mapToEarlierScheme_comp_projectionToBase j hj i hi
  rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToBase, MarkedBlowupSequenceData.toMarkedSequence_projectionToBase] at h
  exact h

/- English proof (authored)
When the earlier index is the matched index itself, the underlying comparison is the ordinary stage comparison. The marked maps use these same morphisms.
-/
private theorem markedMapToEarlierScheme_index {k k' : Type u} [Field k] [Field k'] {A B : Scheme.{u}}
    {p : A ⟶ Spec (CommRingCat.of k)} {q : B ⟶ Spec (CommRingCat.of k')} {g : B ⟶ A}
    {I : A.IdealSheafData} {I' : B.IdealSheafData} {m : ℕ} {E : List A.IdealSheafData}
    {E' : List B.IdealSheafData} (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m E')
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (j : ℕ) (hj : j ≤ s'.length) :
    markedMapToEarlierScheme s s' c j hj (c.idx j) le_rfl = markedMap s s' c j hj :=
  c.mapToEarlierScheme_index j hj

/- English proof (authored)
First fix a stage of the pulled back sequence and compare pullbacks of the original ideal and boundary between two earlier stages separated only by unmatched steps. At each such step the center pulls back to the unit ideal, so the one-step formulas give equality of ideals and equivalence of boundaries. The maps to successive earlier stages compose through the original transition, so induction along the interval gives the comparison for the entire run of unmatched steps.

Next induct over the pulled back stages. At zero, the initial ideal and boundary comparison, together with the projection formula, identifies the pulled back data with the data from original stage zero. The unmatched-step comparison advances this to the first matched stage. For a successor, the two blowups at the current match form a pullback square and their exceptional ideals agree after pullback. Comparing the controlled-transform factorizations and cancelling the marked power of the exceptional ideal gives equality of successor ideals. Flat pullback commutes with strict transform, and the exceptional entries agree. Since the strict transform of a unit ideal is a unit ideal, the boundary equivalence also advances to the next original stage. Apply the unmatched-step comparison between that stage and the next matched index.

The last pulled back index matches the original last index. Transporting the stage comparison along that equality yields the stated ideal equality and boundary equivalence for the final map.
-/
theorem ideal_boundary_last_eq_comap_lastMap {k k' : Type u} [Field k] [Field k'] {X Y : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k')}
    {g : Y ⟶ X} [AlgebraicGeometry.Flat g]
    {I : X.IdealSheafData} {I' : Y.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} {E' : List Y.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m E')
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hI : I' = I.comap g)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (E.map (fun D => D.comap g)))
    (hN : ∀ i : ℕ, i ≤ s.length → AlgebraicGeometry.IsNoetherian (s.obj i))
    (hN' : ∀ j : ℕ, j ≤ s'.length → AlgebraicGeometry.IsNoetherian (s'.obj j)) :
    s'.ideal s'.length = (s.ideal s.length).comap c.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
        ((s.boundary s.length).map (fun D => D.comap c.lastMap)) := by
  subst hI
  have hrun : ∀ (j : ℕ) (hj : j ≤ s'.length) (b : ℕ) (hb : b ≤ c.idx j) (a : ℕ) (hab : a ≤ b),
      (∀ t : ℕ, a ≤ t → t < b → ∀ j' : ℕ, j' < s'.length → c.idx j' ≠ t) →
        (s.ideal a).comap (markedMapToEarlierScheme s s' c j hj a (le_trans hab hb)) =
            (s.ideal b).comap (markedMapToEarlierScheme s s' c j hj b hb) ∧
          MarkedIdealWithBoundary.SameNontrivialBoundary
            ((s.boundary a).map (fun D => D.comap (markedMapToEarlierScheme s s' c j hj a (le_trans hab hb))))
            ((s.boundary b).map (fun D => D.comap (markedMapToEarlierScheme s s' c j hj b hb))) := by
    intro j hj b
    induction b with
    | zero =>
        intro hb a hab _
        have ha0 : a = 0 := Nat.le_zero.1 hab
        subst ha0
        exact ⟨rfl, MarkedIdealWithBoundary.SameNontrivialBoundary.refl _⟩
    | succ nn ihb =>
        intro hb a hab hun
        rcases Nat.lt_or_ge a (nn + 1) with h | h
        · have han : a ≤ nn := Nat.lt_succ_iff.1 h
          have hnb : nn ≤ c.idx j := le_trans (Nat.le_succ nn) hb
          obtain ⟨i1, b1⟩ := ihb hnb a han (fun t ht ht2 => hun t ht (Nat.lt_succ_of_lt ht2))
          have hnlt : nn < c.idx j := lt_of_lt_of_le (Nat.lt_succ_self nn) hb
          have hlen : c.idx j ≤ s.length := c.index_le_length j hj
          have hnlen : nn < s.length := lt_of_lt_of_le hnlt hlen
          have hntop : (s.center nn).comap (markedMapToEarlierScheme s s' c j hj nn hnb) = ⊤ := by
            have h0 := c.comap_center_mapToEarlierScheme_eq_top_of_unmatched j hj nn hnlt (hun nn han (Nat.lt_succ_self nn))
            rw [MarkedBlowupSequenceData.toMarkedSequence_center] at h0
            exact h0
          have hmt : markedMapToEarlierScheme s s' c j hj nn hnb
              = markedMapToEarlierScheme s s' c j hj (nn + 1) hb ≫ s.map nn := by
            have h0 := c.mapToEarlierScheme_eq_comp_blowupMorphism j hj nn hnlt
            rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism] at h0
            exact h0
          have htop2 : (s.center nn).comap
              (markedMapToEarlierScheme s s' c j hj (nn + 1) hb ≫ s.map nn) = ⊤ := by
            rw [← hmt]
            exact hntop
          obtain ⟨i2, b2⟩ := comap_ideal_boundary_succ_of_comap_center_eq_top s nn hnlen (markedMapToEarlierScheme s s' c j hj (nn + 1) hb)
            (hN (nn + 1) hnlen) htop2
          constructor
          · refine i1.trans ?_
            rw [hmt]
            exact i2
          · refine b1.trans ?_
            rw [hmt]
            exact b2.symm
        · have hae : a = nn + 1 := le_antisymm hab h
          subst hae
          exact ⟨rfl, MarkedIdealWithBoundary.SameNontrivialBoundary.refl _⟩
  have main : ∀ (j : ℕ) (hj : j ≤ s'.length),
      s'.ideal j = (s.ideal (c.idx j)).comap (markedMap s s' c j hj) ∧
        MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary j)
          ((s.boundary (c.idx j)).map (fun D => D.comap (markedMap s s' c j hj))) := by
    intro j
    induction j with
    | zero =>
        intro hj0
        have hz : (0 : ℕ) ≤ c.idx 0 := Nat.zero_le _
        obtain ⟨r1, r2⟩ := hrun 0 hj0 (c.idx 0) le_rfl 0 hz
          (fun t _ ht => c.index_ne_of_lt_index_zero t ht)
        have hmi : markedMapToEarlierScheme s s' c 0 hj0 (c.idx 0) le_rfl = markedMap s s' c 0 hj0 :=
          markedMapToEarlierScheme_index s s' c 0 hj0
        have e1 : s'.ideal 0 = (s.ideal 0).comap (markedMapToEarlierScheme s s' c 0 hj0 0 hz) := by
          rw [s'.ideal_zero, s.ideal_zero, ← s.proj_zero, ← s'.proj_zero,
            ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
            markedMapToEarlierScheme_comp_projectionToBase]
        constructor
        · refine e1.trans ?_
          rw [← hmi]
          exact r1
        · have hmap : MarkedIdealWithBoundary.SameNontrivialBoundary
              (E'.map (fun D => D.comap (s'.proj 0)))
              ((E.map (fun D => D.comap g)).map (fun D => D.comap (s'.proj 0))) :=
            MarkedIdealWithBoundary.SameNontrivialBoundary.map _ (by simp) hE
          have hlist : (E.map (fun D => D.comap g)).map (fun D => D.comap (s'.proj 0))
              = (E.map (fun D => D.comap (s.proj 0))).map
                (fun D => D.comap (markedMapToEarlierScheme s s' c 0 hj0 0 hz)) := by
            simp only [List.map_map]
            apply List.map_congr_left
            intro D _
            simp only [Function.comp_apply]
            rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
              markedMapToEarlierScheme_comp_projectionToBase]
          have hb0 : s'.boundary 0 = E'.map (fun D => D.comap (s'.proj 0)) := by
            rw [s'.boundary_zero, ← s'.proj_zero]
          have hb0s : s.boundary 0 = E.map (fun D => D.comap (s.proj 0)) := by
            rw [s.boundary_zero, ← s.proj_zero]
          rw [hb0]
          refine hmap.trans ?_
          rw [hlist, ← hb0s, ← hmi]
          exact r2
    | succ n ih =>
        intro hj
        have hn : n < s'.length := hj
        have hnle : n ≤ s'.length := le_of_lt hn
        obtain ⟨ihI, ihB⟩ := ih hnle
        have hidxlt : c.idx n < s.length := c.idx_lt n hn
        have hstr : c.idx n < c.idx (n + 1) := c.idx_strictMono n hn
        have hcen : s'.center n = (s.center (c.idx n)).comap (markedMap s s' c n hnle) := by
          have h0 := c.center_comap n hn
          rw [MarkedBlowupSequenceData.toMarkedSequence_center, MarkedBlowupSequenceData.toMarkedSequence_center] at h0
          exact h0
        have hsq : IsPullback (markedMapToEarlierScheme s s' c (n + 1) hj (c.idx n + 1) hstr) (s'.map n)
            (s.map (c.idx n)) (markedMap s s' c n hnle) := by
          have h0 := c.isPullback_blowupMorphism n hn
          rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism] at h0
          exact h0
        have hw := hsq.w
        have hexc : (s'.center n).comap (s'.map n)
            = ((s.center (c.idx n)).comap (s.map (c.idx n))).comap
              (markedMapToEarlierScheme s s' c (n + 1) hj (c.idx n + 1) hstr) := by
          rw [hcen, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hw]
        have hblow : Blowup.IsBlowupAlongIdealSheaf (s.map (c.idx n)) (s.center (c.idx n)) := s.isBlowup _ hidxlt
        have hb' : Blowup.IsBlowupAlongIdealSheaf (s'.map n) (s'.center n) := s'.isBlowup n hn
        have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((s'.center n).comap (s'.map n)) := by
          unfold FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf at hb'
          exact hb'.1
        have hstepI : s'.ideal (n + 1)
            = (s.ideal (c.idx n + 1)).comap
              (markedMapToEarlierScheme s s' c (n + 1) hj (c.idx n + 1) hstr) := by
          refine (hcart.pow m).eq_of_mul_eq_mul ?_
          have h1 := s'.ideal_succ n hn
          have h2 := s.ideal_succ (c.idx n) hidxlt
          simp only [Blowup.exceptionalIdeal_eq_comap] at h1 h2
          rw [h1, ihI, ← Scheme.IdealSheafData.comap_comp, ← hw,
            Scheme.IdealSheafData.comap_comp, ← h2, Scheme.IdealSheafData.comap_mul,
            Scheme.IdealSheafData.comap_pow, ← hexc]
        have : AlgebraicGeometry.Flat (markedMap s s' c n hnle) := c.flat_map n hnle
        have := hN (c.idx n + 1) hidxlt
        have := hN' (n + 1) hj
        have hST : ∀ D : (s.obj (c.idx n)).IdealSheafData,
            (Blowup.strictTransform (s.map (c.idx n)) (s.center (c.idx n)) D).comap
                (markedMapToEarlierScheme s s' c (n + 1) hj (c.idx n + 1) hstr)
              = Blowup.strictTransform (s'.map n) (s'.center n) (D.comap (markedMap s s' c n hnle)) := by
          intro D
          rw [comap_strictTransform_of_flat_of_isLocallyNoetherian (s.map (c.idx n))
            (markedMap s s' c n hnle) (s'.map n)
            (markedMapToEarlierScheme s s' c (n + 1) hj (c.idx n + 1) hstr) hsq
            (s.center (c.idx n)) D hblow, ← hcen]
        have hB2 : ((s.boundary (c.idx n)).map (fun D => D.comap (markedMap s s' c n hnle))).map
              (Blowup.strictTransform (s'.map n) (s'.center n)) ++ [(s'.center n).comap (s'.map n)]
            = (s.boundary (c.idx n + 1)).map
              (fun D => D.comap (markedMapToEarlierScheme s s' c (n + 1) hj (c.idx n + 1) hstr)) := by
          rw [s.boundary_succ (c.idx n) hidxlt, List.map_append, List.map_map, List.map_map,
            List.map_cons, List.map_nil, Blowup.exceptionalIdeal_eq_comap, ← hexc]
          congr 1
          apply List.map_congr_left
          intro D _
          exact (hST D).symm
        have hB1 : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary (n + 1))
            (((s.boundary (c.idx n)).map (fun D => D.comap (markedMap s s' c n hnle))).map
              (Blowup.strictTransform (s'.map n) (s'.center n)) ++
                [(s'.center n).comap (s'.map n)]) := by
          rw [s'.boundary_succ n hn, Blowup.exceptionalIdeal_eq_comap]
          exact MonomialCenter.sameNontrivialBoundary_append
            (MarkedIdealWithBoundary.SameNontrivialBoundary.map _ (strictTransform_top _ _) ihB)
            (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _)
        obtain ⟨r1, r2⟩ := hrun (n + 1) hj (c.idx (n + 1)) le_rfl (c.idx n + 1) hstr
          (fun t ht ht2 => c.index_ne_of_index_lt_of_lt_index_succ n hj t (by omega) ht2)
        have hmi :
            markedMapToEarlierScheme s s' c (n + 1) hj (c.idx (n + 1)) le_rfl = markedMap s s' c (n + 1) hj :=
          markedMapToEarlierScheme_index s s' c (n + 1) hj
        constructor
        · refine hstepI.trans ?_
          rw [← hmi]
          exact r1
        · refine hB1.trans ?_
          rw [hB2, ← hmi]
          exact r2
  obtain ⟨hmI, hmB⟩ := main s'.length le_rfl
  have e1 : (s.ideal s.length).comap c.lastMap
      = (s.ideal (c.idx s'.length)).comap (markedMap s s' c s'.length le_rfl) :=
    comap_comp_eqToHom (F := s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.schemeAt) (fun n => s.ideal n) c.idx_length
      (c.map s'.length le_rfl)
  have e2 : (s.boundary s.length).map (fun D => D.comap c.lastMap)
      = (s.boundary (c.idx s'.length)).map
        (fun D => D.comap (markedMap s s' c s'.length le_rfl)) :=
    map_comap_comp_eqToHom (F := s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.schemeAt) (fun n => s.boundary n) c.idx_length
      (c.map s'.length le_rfl)
  exact ⟨hmI.trans e1.symm, sameNontrivialBoundary_of_eq hmB e2⟩

end SequenceOfBlowupsPullback

end FunctorialResolution.EmbeddedResolution

end
