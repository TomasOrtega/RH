import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Strict growth gives the lower bound that every value is at least its index, by induction from zero. For the other inequality use strong induction on the index. If a value exceeded its index, that index would be below the target endpoint, since all values are at most that endpoint. By surjectivity it would have a preimage before the source endpoint. The lower bound puts this preimage at or before the index. An earlier preimage is impossible because the induction hypothesis makes all earlier values at most their indices, and the current index is impossible because its value is assumed larger. Hence every value equals its index.
-/
private theorem apply_eq_self_of_strictMono_of_surjective (L L' : ℕ) (r : ℕ → ℕ)
    (h1 : ∀ i, i < L' → r i < L)
    (h2 : ∀ i j, j ≤ L' → i < j → r i < r j)
    (h3 : r L' = L)
    (hsurj : ∀ i, i < L → ∃ j, j < L' ∧ r j = i) :
    ∀ i, i ≤ L' → r i = i := by
  have hA : ∀ i, i ≤ L' → i ≤ r i := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have hstep := h2 n (n + 1) hn (Nat.lt_succ_self n)
      have hprev := ih (Nat.le_of_succ_le hn)
      omega
  have key : ∀ i, (∀ j, j < i → j ≤ L' → r j ≤ j) → i ≤ L' → r i ≤ i := by
    intro i ih hi
    by_contra hcon
    have hlt : i < r i := by omega
    have hle : r i ≤ L := by
      rcases Nat.lt_or_ge i L' with hc | hc
      · exact le_of_lt (h1 i hc)
      · have hEq : i = L' := le_antisymm hi hc
        subst hEq
        exact le_of_eq h3
    obtain ⟨j, hjL, hrj⟩ := hsurj i (by omega)
    have hjle : j ≤ r j := hA j (le_of_lt hjL)
    rcases Nat.lt_or_ge j i with hji | hji
    · have hij := ih j hji (le_of_lt hjL)
      omega
    · have hEq : j = i := by omega
      subst hEq
      omega
  have hB' : ∀ n i, i ≤ n → i ≤ L' → r i ≤ i := by
    intro n
    induction n with
    | zero =>
      intro i hi hiL
      exact key i (fun j hj _ => by omega) hiL
    | succ n ih =>
      intro i hi hiL
      exact key i (fun j _ hjL => ih j (by omega) hjL) hiL
  intro i hi
  exact le_antisymm (hB' i i le_rfl hi) (hA i hi)

/- English proof (authored)
Identify the two indices with the specified consecutive stages. The extra transitions in the comparison maps become identities, leaving the usual pullback square for the consecutive pulled-back transition.
-/
private theorem isPullback_pullbackTransitionMap_comp_transitionMap {X X' : Scheme.{u}} (s : SequenceOfBlowups X)
    (φ : X' ⟶ X) (i j j' : ℕ) (hj : j = i) (hj' : j' = i + 1) (hjj' : j ≤ j')
    (hij : i ≤ j) (hij' : i + 1 ≤ j') :
    IsPullback (pullback.snd φ (s.projectionToBase j') ≫ s.transitionMap hij')
      (s.pullbackTransitionMap φ hjj') (s.transitionMapSucc i)
      (pullback.snd φ (s.projectionToBase j) ≫ s.transitionMap hij) := by
  subst hj
  subst hj'
  simp only [SequenceOfBlowups.transitionMap_self_eq_id, Category.comp_id]
  exact s.isPullback_pullbackTransitionMap φ _

/- English proof (authored)
With the indices identified, the center ideals are the same and the intervening transition is the identity. Both expressions pull that center back along the same composite.
-/
private theorem center_comap_eq_comap_comp_transitionMap_of_eq {X W V : Scheme.{u}} (s : SequenceOfBlowups X) {i j : ℕ}
    (hij : i ≤ j) (hji : j = i) (f : W ⟶ V) (g : V ⟶ s.schemeAt j) :
    (s.center j).comap (f ≫ g) = (s.center i).comap (f ≫ g ≫ s.transitionMap hij) := by
  subst hji
  rw [SequenceOfBlowups.transitionMap_self_eq_id, Category.comp_id]

/- English proof (authored)
An ideal sheaf with empty support is the unit ideal. Since the given ideal is nonunit, its support is nonempty.
-/
private theorem support_nonempty_of_ne_top {Y : Scheme.{u}} (I : Y.IdealSheafData) (h : I ≠ ⊤) :
    ((I.support : Set ↥Y)).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro he
  apply h
  have hbot : I.support = ⊥ := SetLike.ext' (by rw [he]; rfl)
  exact (Scheme.IdealSheafData.support_eq_bot_iff I).mp hbot

/- English proof (authored)
At the given step take a point on the center support. Its image in the base has a preimage in the new base by hypothesis. Together these points give a point of the scheme pullback. Its second projection lies in the original center support, so it belongs to the pulled-back center support.
-/
theorem support_comap_center_nonempty_of_mem_range {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X)
    (hne : ∀ i : ℕ, i < s.length → (((s.center i).support : Set ↥(s.schemeAt i))).Nonempty)
    (hran : ∀ i : ℕ, i < s.length → ∀ x ∈ ((s.center i).support : Set ↥(s.schemeAt i)),
      (s.projectionToBase i).base x ∈ Set.range (⇑φ.base)) :
    ∀ i : ℕ, i < s.length →
      ((((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support :
        Set ↥(pullback φ (s.projectionToBase i)))).Nonempty := by
  intro i hi
  obtain ⟨x, hx⟩ := hne i hi
  obtain ⟨y, hy⟩ := hran i hi x hx
  obtain ⟨z, hz1, hz2⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := φ) (g := s.projectionToBase i) y x hy
  refine ⟨z, ?_⟩
  have hmem : (pullback.snd φ (s.projectionToBase i)) z ∈ ((s.center i).support : Set ↥(s.schemeAt i)) := by
    rw [hz2]; exact hx
  rw [Scheme.IdealSheafData.support_comap]
  exact hmem

/- English proof (authored)
Every original center has nonempty pulled-back support, so the retention condition makes every original step appear among the reindexed steps. The reindexing is strictly increasing and sends the final index to the original final index. The ordered-index argument now makes it the identity through the final stage, and the lengths agree. Use the stage isomorphisms followed by the second projections as the strict comparison maps. The initial comparison follows from the projection equations. For every successor, the transition square is obtained by composing the comparison isomorphisms with the ordinary consecutive base-change pullback square. The center equations become exactly the strict pullback equations because the indices agree.
-/
theorem IsPullbackBlowupSequence.isStrictPullback_of_support_comap_center_nonempty {X X' : Scheme.{u}} {φ : X' ⟶ X} {s' : SequenceOfBlowups X'}
    {s : SequenceOfBlowups X} (h : IsPullbackBlowupSequence φ s' s)
    (hhit : ∀ i : ℕ, i < s.length →
      ((((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support :
        Set ↥(pullback φ (s.projectionToBase i)))).Nonempty) :
    IsStrictPullbackBlowupSeq φ s' s := by
  obtain ⟨r, e, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hsurj : ∀ i, i < s.length → ∃ j, j < s'.length ∧ r j = i := by
    intro i hi
    obtain ⟨x, hx⟩ := hhit i hi
    exact (h4 i hi).mp ⟨x, hx⟩
  have hid : ∀ i, i ≤ s'.length → r i = i :=
    apply_eq_self_of_strictMono_of_surjective s.length s'.length r h1 h2 h3 hsurj
  have hlen : s'.length = s.length := by
    have hfin := hid s'.length le_rfl
    omega
  refine ⟨hlen, fun i hi => (e i hi).hom ≫ pullback.snd φ (s.projectionToBase (r i)) ≫
      s.transitionMap (le_of_eq (hid i hi).symm), ?_, ?_, ?_⟩
  · have h0 := h5 0 (Nat.zero_le s'.length)
    simp only [Category.assoc]
    rw [← s.projectionToBase_zero, s.transitionMap_comp_projectionToBase, ← pullback.condition,
      ← Category.assoc, h0, s'.projectionToBase_zero]
  · intro i hi
    have hile : i ≤ s'.length := le_of_lt hi
    have hi1 : i + 1 ≤ s'.length := hi
    have hrle : r i ≤ r (i + 1) := le_of_lt (h2 i (i + 1) hi1 (Nat.lt_succ_self i))
    have sq1 : IsPullback (e (i + 1) hi).hom (s'.transitionMapSucc i) (s.pullbackTransitionMap φ hrle)
        (e i hile).hom := by
      refine IsPullback.of_horiz_isIso ⟨?_⟩
      exact (h6 i hi hrle).symm
    have sq2 : IsPullback
        (pullback.snd φ (s.projectionToBase (r (i + 1))) ≫ s.transitionMap (le_of_eq (hid (i + 1) hi1).symm))
        (s.pullbackTransitionMap φ hrle) (s.transitionMapSucc i)
        (pullback.snd φ (s.projectionToBase (r i)) ≫ s.transitionMap (le_of_eq (hid i hile).symm)) :=
      isPullback_pullbackTransitionMap_comp_transitionMap s φ i (r i) (r (i + 1)) (hid i hile) (hid (i + 1) hi1) hrle
        (le_of_eq (hid i hile).symm) (le_of_eq (hid (i + 1) hi1).symm)
    exact sq1.paste_horiz sq2
  · intro i hi
    have hile : i ≤ s'.length := le_of_lt hi
    rw [h7 i hi]
    exact center_comap_eq_comap_comp_transitionMap_of_eq s (le_of_eq (hid i hile).symm) (hid i hile) (e i hile).hom
      (pullback.snd φ (s.projectionToBase (r i)))

/- English proof (authored)
Every original center is nonunit and therefore has nonempty support. Surjectivity of the base map ensures that the projection of any point of that support lies in its range. Thus every pulled-back center has nonempty support. Apply the criterion for a pullback with no missing centers.
-/
theorem IsPullbackBlowupSequence.isStrictPullback_of_surjective {X X' : Scheme.{u}} {φ : X' ⟶ X}
    [AlgebraicGeometry.Surjective φ] {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsPullbackBlowupSequence φ s' s) (hc : ∀ i : ℕ, i < s.length → s.center i ≠ ⊤) :
    IsStrictPullbackBlowupSeq φ s' s := by
  refine h.isStrictPullback_of_support_comap_center_nonempty ?_
  refine support_comap_center_nonempty_of_mem_range φ s
    (fun i hi => support_nonempty_of_ne_top (s.center i) (hc i hi)) ?_
  intro i _ x _
  exact φ.surjective _

end FunctorialResolution.EmbeddedResolution
