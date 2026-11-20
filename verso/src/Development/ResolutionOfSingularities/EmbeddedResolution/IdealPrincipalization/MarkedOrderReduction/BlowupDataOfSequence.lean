import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedPullbackSquare
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderAlongBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.NonMonomialOrderReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.CompanionIdealReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MapToEarlierScheme
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The marked sequence and its underlying sequence use the projections of the original marked blowup data. Apply the projection comparison in the direction that identifies the sequence projection with the data projection.
-/
theorem toMarkedSequence_projectionToBase {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase i = s.proj i :=
  (s.projectionToBase_eq_toSequenceOfBlowups i).symm

/- English proof (authored)
The two upper marked objects have the same scheme and field. Substituting the equal structure maps, ideals, markings, and boundaries makes them the same object. The assumed pullback relation for its assigned sequence is then the required relation.
-/
theorem isPullbackBlowupSequence_congr (F : PrincipalizationAssignment.{u})
    {k₁ k₂ : Type u} [Field k₁] [Field k₂] {B Q : Scheme.{u}}
    (pB : B ⟶ Spec (CommRingCat.of k₁)) (IB : B.IdealSheafData) (mB : ℕ)
    (EB : List B.IdealSheafData) (q : Q ⟶ B)
    (pQ₁ pQ₂ : Q ⟶ Spec (CommRingCat.of k₂)) (IQ₁ IQ₂ : Q.IdealSheafData) (mQ₁ mQ₂ : ℕ)
    (EQ₁ EQ₂ : List Q.IdealSheafData)
    (hp : pQ₁ = pQ₂) (hI : IQ₁ = IQ₂) (hm : mQ₁ = mQ₂) (hE : EQ₁ = EQ₂)
    (h : IsPullbackBlowupSequence q (F (MarkedIdealWithBoundary.mk k₂ Q pQ₁ IQ₁ mQ₁ EQ₁)).toSequenceOfBlowups
        (F (MarkedIdealWithBoundary.mk k₁ B pB IB mB EB)).toSequenceOfBlowups) :
    IsPullbackBlowupSequence q (F (MarkedIdealWithBoundary.mk k₂ Q pQ₂ IQ₂ mQ₂ EQ₂)).toSequenceOfBlowups
      (F (MarkedIdealWithBoundary.mk k₁ B pB IB mB EB)).toSequenceOfBlowups := by
  subst hp
  subst hI
  subst hm
  subst hE
  exact h

/- English proof (authored)
Converting the sequence to data records its length, and constructing a sequence from the data uses that recorded length. The round trip therefore preserves length.
-/
theorem BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length {X : Scheme.{u}} (s : SequenceOfBlowups X) :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length = s.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_length]
  rfl

/- English proof (authored)
The data record the original scheme at every stage, and the reconstructed sequence takes its stage scheme from the data. Composing the two identifications gives the original stage scheme.
-/
private theorem ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt {X : Scheme.{u}} (s : SequenceOfBlowups X) (j : ℕ) :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt j = s.schemeAt j :=
  (BlowupSequenceData.toSequenceOfBlowups_schemeAt _ j).trans (BlowupSequenceData.ofSequenceOfBlowups_schemeAt s j)

/- English proof (authored)
The length after conversion to data and back equals the original sequence length. Substitute this equality into the given bound.
-/
private theorem le_length_of_le_ofSequenceOfBlowups_length {X : Scheme.{u}} (s : SequenceOfBlowups X) {j : ℕ}
    (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length) : j ≤ s.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
  exact hj

/- English proof (authored)
Conversion to data and back preserves length. The original upper bound for j therefore also bounds it in the reconstructed sequence.
-/
private theorem le_ofSequenceOfBlowups_length_of_le_length {X : Scheme.{u}} (s : SequenceOfBlowups X) {j : ℕ}
    (hj : j ≤ s.length) : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
  exact hj

/- English proof (authored)
The projection of the reconstructed sequence is the projection in its data. Those data were formed using the original sequence's projection, so the two agree.
-/
theorem BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups {X : Scheme.{u}} (t : SequenceOfBlowups X) (j : ℕ) :
    (BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups.projectionToBase j = t.projectionToBase j :=
  (BlowupSequenceData.toSequenceOfBlowups_projectionToBase (BlowupSequenceData.ofSequenceOfBlowups t) j).trans (BlowupSequenceData.ofSequenceOfBlowups_projectionToBase t j)

namespace SequenceOfBlowupsPullback

variable {X X' : Scheme.{u}} {φ : X' ⟶ X} {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}

private def ofSequenceOfBlowupsMap (c : SequenceOfBlowupsPullback φ s' s) (j : ℕ)
    (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length) :
    (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.schemeAt j ⟶ (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt (c.idx j) :=
  eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j) ≫ c.map j (le_length_of_le_ofSequenceOfBlowups_length s' hj) ≫
    eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s (c.idx j)).symm

/- English proof (authored)
Replace the two reconstructed lengths by the original lengths. The index at the original endpoint is the original target endpoint by the pullback data.
-/
private theorem index_ofSequenceOfBlowups_length (c : SequenceOfBlowupsPullback φ s' s) :
    c.idx (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length = (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s', BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s]
  exact c.idx_length

/- English proof (authored)
The strict bound in the reconstructed source sequence is the same strict bound in the original source. Its matched index lies before the original target length, which equals the reconstructed target length.
-/
private theorem index_lt_ofSequenceOfBlowups_length (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length →
      c.idx j < (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
  exact c.idx_lt j hj

/- English proof (authored)
The reconstructed length equals the original length, so j is an actual step in the original sequence. Strict increase of the matching indices there gives the inequality.
-/
private theorem index_lt_index_succ_of_lt_length_ofSequenceOfBlowups (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length → c.idx j < c.idx (j + 1) := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
  exact c.idx_strictMono j hj

/- English proof (authored)
The stage schemes are unchanged by conversion to data and back. The equality-induced maps inserted on both sides of the original comparison are consequently identities. Cancelling them gives the original comparison map.
-/
private theorem ofSequenceOfBlowups_map_eq (c : SequenceOfBlowupsPullback φ s' s) (j : ℕ)
    (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length) :
    ofSequenceOfBlowupsMap c j hj = c.map j (le_length_of_le_ofSequenceOfBlowups_length s' hj) := by
  show 𝟙 (s'.schemeAt j) ≫ c.map j (le_length_of_le_ofSequenceOfBlowups_length s' hj) ≫ 𝟙 (s.schemeAt (c.idx j))
      = c.map j (le_length_of_le_ofSequenceOfBlowups_length s' hj)
  exact (Category.id_comp _).trans (Category.comp_id _)

/- English proof (authored)
Substitute the four equalities of the arrows. The second square then has the same arrows as the square known to be a pullback.
-/
private theorem isPullback_congr {A B C D : Scheme.{u}} {f f' : A ⟶ B} {g g' : A ⟶ C}
    {h h' : B ⟶ D} {k k' : C ⟶ D} (hf : f = f') (hg : g = g') (hh : h = h') (hk : k = k')
    (H : IsPullback f g h k) : IsPullback f' g' h' k' := by
  subst hf
  subst hg
  subst hh
  subst hk
  exact H

/- English proof (authored)
The comparison map in the reconstructed square is the original comparison map under the stage identifications, and both projections are the original projections. Substitute these equalities into the original pullback square.
-/
private theorem isPullback_projectionToBase_ofSequenceOfBlowups (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ (j : ℕ) (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length),
      IsPullback (ofSequenceOfBlowupsMap c j hj) ((BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.projectionToBase j)
        ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.projectionToBase (c.idx j)) φ := by
  intro j hj
  exact isPullback_congr (ofSequenceOfBlowups_map_eq c j hj).symm
    (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s' j).symm
    (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s (c.idx j)).symm rfl
    (c.isPullback j (le_length_of_le_ofSequenceOfBlowups_length s' hj))

/- English proof (authored)
Induct on the number of steps in the transition. A transition to the same stage is the identity in both descriptions. Adding one step composes the new blowup map with the previous transition. Conversion records the original blowup map, and the previous transitions agree by induction, so the longer transitions agree.
-/
private theorem ofSequenceOfBlowups_transitionMap {W : Scheme.{u}} (t : SequenceOfBlowups W) {i i' : ℕ}
    (h : i ≤ i') : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap h = t.transitionMap h := by
  induction h with
  | refl =>
      have e1 : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (le_refl i) = 𝟙 ((BlowupSequenceData.ofSequenceOfBlowups t).obj i) := by
        rw [BlowupSequenceData.transitionMap_refl]
      have e2 : t.transitionMap (le_refl i) = 𝟙 (t.schemeAt i) := by
        rw [SequenceOfBlowups.transitionMap_self_eq_id]
      exact e1.trans e2.symm
  | @step m hm ih =>
      have hmap : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (Nat.le_succ m) = t.transitionMapSucc m :=
        (BlowupSequenceData.transitionMap_succ (BlowupSequenceData.ofSequenceOfBlowups t) m).trans (BlowupSequenceData.ofSequenceOfBlowups_blowupMorphism t m)
      have h1 : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (Nat.le_trans hm (Nat.le_succ m))
          = (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (Nat.le_succ m) ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm :=
        (BlowupSequenceData.transitionMap_comp_transitionMap (BlowupSequenceData.ofSequenceOfBlowups t) hm (Nat.le_succ m)).symm
      have h2a : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (Nat.le_succ m) ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm
          = t.transitionMapSucc m ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm :=
        congrArg (fun f : t.schemeAt (m + 1) ⟶ t.schemeAt m => f ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm) hmap
      have h2b : t.transitionMapSucc m ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm
          = t.transitionMapSucc m ≫ t.transitionMap hm :=
        congrArg (fun g : t.schemeAt m ⟶ t.schemeAt i => t.transitionMapSucc m ≫ g) ih
      have h3 : t.transitionMapSucc m ≫ t.transitionMap hm = t.transitionMap (Nat.le_trans hm (Nat.le_succ m)) := by
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
        exact SequenceOfBlowups.transitionMap_trans t hm (Nat.le_succ m)
      exact h1.trans (h2a.trans (h2b.trans h3))

/- English proof (authored)
The transition of the reconstructed sequence is the transition of the underlying data. The transition comparison identifies that data transition with the one in the original sequence.
-/
private theorem ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap {W : Scheme.{u}} (t : SequenceOfBlowups W) {i i' : ℕ}
    (h : i ≤ i') : (BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups.transitionMap h = t.transitionMap h :=
  (BlowupSequenceData.toSequenceOfBlowups_transitionMap (BlowupSequenceData.ofSequenceOfBlowups t) h).trans (ofSequenceOfBlowups_transitionMap t h)

/- English proof (authored)
In each sequence the blowup morphism is the transition between consecutive stages. Equality of those transitions gives equality of the blowup morphisms.
-/
private theorem ofSequenceOfBlowups_toSequenceOfBlowups_blowupMorphism {W : Scheme.{u}} (t : SequenceOfBlowups W) (i : ℕ) :
    (BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups.transitionMapSucc i = t.transitionMapSucc i :=
  (SequenceOfBlowups.blowupMorphism_eq_transitionMap ((BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups) i).trans
    ((ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap t (Nat.le_succ i)).trans
      (SequenceOfBlowups.blowupMorphism_eq_transitionMap t i).symm)

/- English proof (authored)
The reconstructed length gives the same bound on the step as the original length. The reconstructed step, comparison maps, and transition between matching indices are the corresponding original maps. Substitute these identifications and use the original compatibility of transitions.
-/
private theorem ofSequenceOfBlowups_blowupMorphism_comp_map (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ (j : ℕ) (hj : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length),
      (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.transitionMapSucc j ≫ ofSequenceOfBlowupsMap c j (le_of_lt hj) =
        ofSequenceOfBlowupsMap c (j + 1) hj ≫
          (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap (le_of_lt (index_lt_index_succ_of_lt_length_ofSequenceOfBlowups c j hj)) := by
  intro j hj
  have hlt : j < s'.length := by
    have h := hj
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at h
    exact h
  rw [ofSequenceOfBlowups_map_eq c j (le_of_lt hj), ofSequenceOfBlowups_map_eq c (j + 1) hj,
    ofSequenceOfBlowups_toSequenceOfBlowups_blowupMorphism, ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap]
  exact c.step j hlt

/- English proof (authored)
The maps induced by the two self-equalities are identities on their respective schemes. Composing f with these identities gives f.
-/
private theorem eqToHom_refl_comp_comp_eqToHom_refl {A B : Scheme.{u}} (hA : A = A) (hB : B = B)
    (f : A ⟶ B) : eqToHom hA ≫ f ≫ eqToHom hB = f := by
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/- English proof (authored)
The reconstructed center ideals are the original ones, and the comparison map is the original map because the inserted scheme identifications are identities. The bound on j is unchanged by reconstruction. Apply the original pullback equality for centers.
-/
private theorem center_ofSequenceOfBlowups_eq_comap (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ (j : ℕ) (hj : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length),
      (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.center j =
        ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.center (c.idx j)).comap (ofSequenceOfBlowupsMap c j (le_of_lt hj)) := by
  intro j hj
  have hj' : j < s'.length := lt_of_lt_of_le hj (le_of_eq (BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s'))
  have hmap : ofSequenceOfBlowupsMap c j (le_of_lt hj) = c.map j (le_of_lt hj') :=
    eqToHom_refl_comp_comp_eqToHom_refl (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j) (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s (c.idx j)).symm
      (c.map j (le_length_of_le_ofSequenceOfBlowups_length s' (le_of_lt hj)))
  rw [hmap]
  exact c.center_comap j hj'

/- English proof (authored)
The given reconstructed step is an original step because the lengths agree. Its center is the original center and hence differs from the unit ideal by the supplied pullback property.
-/
private theorem center_ofSequenceOfBlowups_ne_top (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length →
      (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.center j ≠ ⊤ := by
  intro j hj
  have hj' : j < s'.length := lt_of_lt_of_le hj (le_of_eq (BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s'))
  exact c.center_ne_top j hj'

/- English proof (authored)
The reconstructed lengths identify both the given target step and the set of source steps with the originals. Its center and projection to the base also agree with the originals. The omission condition then says that the projection of the given center point differs from the image of every point of the new base.
-/
private theorem ofSequenceOfBlowups_ne_of_mem_unmatched_center (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ i : ℕ, i < (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length →
      (∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length → c.idx j ≠ i) →
      ∀ z : ↥((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt i),
        z ∈ ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.center i).support →
        ∀ x' : ↥X', φ.base x' ≠ ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.projectionToBase i).base z := by
  intro i hi hmiss z hz x'
  have hi' : i < s.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hi
    exact hi
  have hmiss' : ∀ j : ℕ, j < s'.length → c.idx j ≠ i := by
    intro j hj
    refine hmiss j ?_
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have h := c.omitted i hi' hmiss' z hz x'
  rw [BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s i]
  exact h

def toBlowupDataOfSeq (c : SequenceOfBlowupsPullback φ s' s) :
    SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups where
  idx := c.idx
  map := ofSequenceOfBlowupsMap c
  idx_length := index_ofSequenceOfBlowups_length c
  idx_lt := index_lt_ofSequenceOfBlowups_length c
  idx_strictMono := index_lt_index_succ_of_lt_length_ofSequenceOfBlowups c
  isPullback := isPullback_projectionToBase_ofSequenceOfBlowups c
  step := ofSequenceOfBlowups_blowupMorphism_comp_map c
  center_comap := center_ofSequenceOfBlowups_eq_comap c
  center_ne_top := center_ofSequenceOfBlowups_ne_top c
  omitted := ofSequenceOfBlowups_ne_of_mem_unmatched_center c

private def transportedMap
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups)
    (j : ℕ) (hj : j ≤ s'.length) : s'.schemeAt j ⟶ s.schemeAt (c.idx j) :=
  eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j).symm ≫ c.map j (le_ofSequenceOfBlowups_length_of_le_length s' hj) ≫
    eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s (c.idx j))

/- English proof (authored)
The matching sends the endpoint of the reconstructed source to the endpoint of the reconstructed target. Both reconstructed lengths equal their original lengths, giving the endpoint formula.
-/
private theorem ofSequenceOfBlowups_index_length
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    c.idx s'.length = s.length := by
  have h := c.idx_length
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s', BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s] at h
  exact h

/- English proof (authored)
Translate the original source index bound to the reconstructed source. The matching index is then strictly below the reconstructed target length, which equals the original target length.
-/
private theorem ofSequenceOfBlowups_index_lt_length
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ j : ℕ, j < s'.length → c.idx j < s.length := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have h := c.idx_lt j hj'
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at h
  exact h

/- English proof (authored)
Translate the original index bound using preservation of length. Strict increase for the reconstructed matching gives the same strict increase at the original index.
-/
private theorem index_lt_index_succ_of_lt_length
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ j : ℕ, j < s'.length → c.idx j < c.idx (j + 1) := by
  intro j hj
  refine c.idx_strictMono j ?_
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
  exact hj

/- English proof (authored)
The maps used to transport between the original and reconstructed stage schemes are induced by equalities and here are identities. Composing the reconstructed comparison map on either side with these identities leaves it unchanged.
-/
private theorem transportedMap_eq_map
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups)
    (j : ℕ) (hj : j ≤ s'.length) :
    transportedMap c j hj = c.map j (le_ofSequenceOfBlowups_length_of_le_length s' hj) :=
  eqToHom_refl_comp_comp_eqToHom_refl (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j).symm (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s (c.idx j))
    (c.map j (le_ofSequenceOfBlowups_length_of_le_length s' hj))

/- English proof (authored)
Transport preserves the comparison map and both stage projections agree with those of the reconstructed sequences. The reconstructed pullback square therefore supplies the pullback square for the original stages.
-/
private theorem isPullback_transportedMap
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ (j : ℕ) (hj : j ≤ s'.length),
      IsPullback (transportedMap c j hj) (s'.projectionToBase j) (s.projectionToBase (c.idx j)) φ := by
  intro j hj
  exact isPullback_congr (transportedMap_eq_map c j hj).symm (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s' j)
    (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s (c.idx j)) rfl
    (c.isPullback j (le_ofSequenceOfBlowups_length_of_le_length s' hj))

/- English proof (authored)
Apply the commuting step relation in the reconstructed sequences, using equality of lengths for its bound. Their successor and longer transitions are the original transitions. The transported comparison maps are also the given comparison maps, so substituting these equalities gives the required relation.
-/
private theorem blowupMorphism_comp_map_of_ofSequenceOfBlowups
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ (j : ℕ) (hj : j < s'.length),
      s'.transitionMapSucc j ≫ transportedMap c j (le_of_lt hj) =
        transportedMap c (j + 1) hj ≫ s.transitionMap (le_of_lt (index_lt_index_succ_of_lt_length c j hj)) := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have key := c.step j hj'
  rw [ofSequenceOfBlowups_toSequenceOfBlowups_blowupMorphism, ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap] at key
  rw [transportedMap_eq_map c j (le_of_lt hj), transportedMap_eq_map c (j + 1) hj]
  exact key

/- English proof (authored)
Use equality of lengths to apply the reconstructed center formula at j. The original center ideals and comparison map agree with the reconstructed ones after transport. The formula therefore gives the original center as the asserted pullback.
-/
private theorem center_eq_comap_transportedMap
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ (j : ℕ) (hj : j < s'.length),
      s'.center j = (s.center (c.idx j)).comap (transportedMap c j (le_of_lt hj)) := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have hmap : transportedMap c j (le_of_lt hj) = c.map j (le_of_lt hj') :=
    eqToHom_refl_comp_comp_eqToHom_refl (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j).symm (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s (c.idx j))
      (c.map j (le_ofSequenceOfBlowups_length_of_le_length s' (le_of_lt hj)))
  rw [hmap]
  exact c.center_comap j hj'

/- English proof (authored)
The original step lies within the reconstructed length, which is the same length. Its center is the same ideal as the reconstructed center, which differs from the unit ideal.
-/
private theorem center_ne_top_of_pullback_ofSequenceOfBlowups
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ j : ℕ, j < s'.length → s'.center j ≠ ⊤ := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  exact c.center_ne_top j hj'

/- English proof (authored)
Use preservation of length to turn the original bounds and unmatched condition into the corresponding reconstructed ones. The center support at the chosen stage is unchanged. Apply the reconstructed omission property and replace the reconstructed projection by the original projection.
-/
private theorem ofSequenceOfBlowups_projectionToBase_ne
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ i : ℕ, i < s.length → (∀ j : ℕ, j < s'.length → c.idx j ≠ i) →
      ∀ z : ↥(s.schemeAt i), z ∈ (s.center i).support →
        ∀ x' : ↥X', φ.base x' ≠ (s.projectionToBase i).base z := by
  intro i hi hmiss z hz x'
  have hi' : i < (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hi
  have hmiss' : ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length → c.idx j ≠ i := by
    intro j hj
    refine hmiss j ?_
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
    exact hj
  have h := c.omitted i hi' hmiss' z hz x'
  rw [BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s i] at h
  exact h

def ofBlowupDataOfSeq (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    SequenceOfBlowupsPullback φ s' s where
  idx := c.idx
  map := transportedMap c
  idx_length := ofSequenceOfBlowups_index_length c
  idx_lt := ofSequenceOfBlowups_index_lt_length c
  idx_strictMono := index_lt_index_succ_of_lt_length c
  isPullback := isPullback_transportedMap c
  step := blowupMorphism_comp_map_of_ofSequenceOfBlowups c
  center_comap := center_eq_comap_transportedMap c
  center_ne_top := center_ne_top_of_pullback_ofSequenceOfBlowups c
  omitted := ofSequenceOfBlowups_projectionToBase_ne c

end SequenceOfBlowupsPullback

end FunctorialResolution.EmbeddedResolution

end
