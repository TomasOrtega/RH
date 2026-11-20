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

/- English proof (translation)
Establish `hA : ∀ i, i ≤ L' → i ≤ r i`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro _`. Conclude with `Nat.zero_le _`.

Consider the case `succ n ih`. Introduce `hn`. Establish `hstep` using `h2 n (n + 1) hn (Nat.lt_succ_self n)`. Establish `hprev` using `ih (Nat.le_of_succ_le hn)`. Use linear arithmetic over natural numbers and integers.

Establish `key : ∀ i, (∀ j, j < i → j ≤ L' → r j ≤ j) → i ≤ L' → r i ≤ i`. Introduce `i ih hi`. Assume the negation of the conclusion as `hcon`. Establish `hlt : i < r i` using `by omega`. Establish `hle : r i ≤ L`.

Break down `Nat.lt_or_ge i L' with hc | hc` into its components or cases. Conclude with `le_of_lt (h1 i hc)`. Establish `hEq : i = L'` using `le_antisymm hi hc`. Substitute `hEq` using the available equality. Conclude with `le_of_eq h3`.

Take `⟨j, hjL, hrj⟩` from `hsurj i (by omega)`. Establish `hjle : j ≤ r j` using `hA j (le_of_lt hjL)`. Break down `Nat.lt_or_ge j i with hji | hji` into its components or cases. Establish `hij` using `ih j hji (le_of_lt hjL)`. Use linear arithmetic over natural numbers and integers.

Establish `hEq : j = i` using `by omega`. Substitute `hEq` using the available equality. Use linear arithmetic over natural numbers and integers. Establish `hB' : ∀ n i, i ≤ n → i ≤ L' → r i ≤ i`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `i hi hiL`. Conclude with `key i (fun j hj _ => by omega) hiL`. Consider the case `succ n ih`.

Introduce `i hi hiL`. Conclude with `key i (fun j _ hjL => ih j (by omega) hjL) hiL`. Introduce `i hi`. Conclude with `le_antisymm (hB' i i le_rfl hi) (hA i hi)`.
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

/- English proof (translation)
Substitute `hj` using the available equality. Substitute `hj'` using the available equality. Simplify using `only [SequenceOfBlowups.transitionMap_self_eq_id, Category.comp_id]`. Conclude with `s.isPullback_pullbackTransitionMap φ _`.
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

/- English proof (translation)
Substitute `hji` using the available equality. Rewrite using `[SequenceOfBlowups.transitionMap_self_eq_id, Category.comp_id]`.
-/
private theorem center_comap_eq_comap_comp_transitionMap_of_eq {X W V : Scheme.{u}} (s : SequenceOfBlowups X) {i j : ℕ}
    (hij : i ≤ j) (hji : j = i) (f : W ⟶ V) (g : V ⟶ s.schemeAt j) :
    (s.center j).comap (f ≫ g) = (s.center i).comap (f ≫ g ≫ s.transitionMap hij) := by
  subst hji
  rw [SequenceOfBlowups.transitionMap_self_eq_id, Category.comp_id]

/- English proof (translation)
Rewrite using `[Set.nonempty_iff_ne_empty]`. Introduce `he`. Apply `h` to reduce the goal to its premises. Establish `hbot : I.support = ⊥` using `SetLike.ext' (by rw [he]; rfl)`. Conclude with `(Scheme.IdealSheafData.support_eq_bot_iff I).mp hbot`.
-/
private theorem support_nonempty_of_ne_top {Y : Scheme.{u}} (I : Y.IdealSheafData) (h : I ≠ ⊤) :
    ((I.support : Set ↥Y)).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro he
  apply h
  have hbot : I.support = ⊥ := SetLike.ext' (by rw [he]; rfl)
  exact (Scheme.IdealSheafData.support_eq_bot_iff I).mp hbot

/- English proof (translation)
Introduce `i hi`. Take `⟨x, hx⟩` from `hne i hi`. Take `⟨y, hy⟩` from `hran i hi x hx`. Take `⟨z, hz1, hz2⟩` from `Scheme.Pullback.exists_preimage_pullback (f := φ) (g := s.projectionToBase i) y x hy`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Establish `hmem : (pullback.snd φ (s.projectionToBase i)) z ∈ ((s.center i).support : Set ↥(s.schemeAt i))`. Rewrite using `[hz2]`. Conclude with `hx`. Rewrite using `[Scheme.IdealSheafData.support_comap]`. Conclude with `hmem`.
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

/- English proof (translation)
Take `⟨r, e, h1, h2, h3, h4, h5, h6, h7⟩` from `h`. Establish `hsurj : ∀ i, i < s.length → ∃ j, j < s'.length ∧ r j = i`. Introduce `i hi`. Take `⟨x, hx⟩` from `hhit i hi`. Conclude with `(h4 i hi).mp ⟨x, hx⟩`.

Establish `hid : ∀ i, i ≤ s'.length → r i = i` using `apply_eq_self_of_strictMono_of_surjective s.length s'.length r h1 h2 h3 hsurj`. Establish `hlen : s'.length = s.length`. Establish `hfin` using `hid s'.length le_rfl`. Use linear arithmetic over natural numbers and integers. Use `⟨hlen, fun i hi => (e i hi).hom ≫ pullback.snd φ (s.projectionToBase (r i)) ≫ s.transitionMap (le_of_eq (hid i hi).symm), ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h0` using `h5 0 (Nat.zero_le s'.length)`. Simplify using `only [Category.assoc]`. Rewrite using `[← s.projectionToBase_zero, s.transitionMap_comp_projectionToBase, ← pullback.condition, ← Category.assoc, h0, s'.projectionToBase_zero]`. Introduce `i hi`. Establish `hile : i ≤ s'.length` using `le_of_lt hi`.

Establish `hi1 : i + 1 ≤ s'.length` using `hi`. Establish `hrle : r i ≤ r (i + 1)` using `le_of_lt (h2 i (i + 1) hi1 (Nat.lt_succ_self i))`. Establish `sq1 : IsPullback (e (i + 1) hi).hom (s'.transitionMapSucc i) (s.pullbackTransitionMap φ hrle) (e i hile).hom`. Use `IsPullback.of_horiz_isIso ⟨?_⟩` and prove the remaining obligations. Conclude with `(h6 i hi hrle).symm`.

Establish `sq2 : IsPullback (pullback.snd φ (s.projectionToBase (r (i + 1))) ≫ s.transitionMap (le_of_eq (hid (i + 1) hi1).symm)) (s.pullbackTransitionMap φ hrle) (s.transitionMapSucc i) (pullback.snd φ (s.projectionToBase (r i)) ≫ s.transitionMap (le_of_eq (hid i hile).symm))` using `isPullback_pullbackTransitionMap_comp_transitionMap s φ i (r i) (r (i + 1)) (hid i hile) (hid (i + 1) hi1) hrle (le_of_eq (hid i hile).symm) (le_of_eq (hid (i + 1) hi1).symm)`. Conclude with `sq1.paste_horiz sq2`. Introduce `i hi`. Establish `hile : i ≤ s'.length` using `le_of_lt hi`. Rewrite using `[h7 i hi]`.

Conclude with `center_comap_eq_comap_comp_transitionMap_of_eq s (le_of_eq (hid i hile).symm) (hid i hile) (e i hile).hom (pullback.snd φ (s.projectionToBase (r i)))`.
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

/- English proof (translation)
Use `h.isStrictPullback_of_support_comap_center_nonempty ?_` and prove the remaining obligations. Use `support_comap_center_nonempty_of_mem_range φ s (fun i hi => support_nonempty_of_ne_top (s.center i) (hc i hi)) ?_` and prove the remaining obligations. Introduce `i _ x _`. Conclude with `φ.surjective _`.
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
