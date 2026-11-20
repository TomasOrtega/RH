import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace FunctorialResolution.EmbeddedResolution

namespace SequenceOfBlowups

variable {X : Scheme.{u}}

/- English proof (authored)
The transition from a stage to itself is the tower functor’s image of an identity arrow and is therefore an identity morphism. Every identity morphism is an isomorphism.
-/
private theorem isIso_transitionMap_refl (s : SequenceOfBlowups X) {i : ℕ} (h : i ≤ i) :
    IsIso (s.transitionMap h) := by
  have he : (homOfLE h : i ⟶ i).op = 𝟙 (Opposite.op i) := rfl
  have hid : s.transitionMap h = 𝟙 (s.schemeAt i) := by
    rw [SequenceOfBlowups.transitionMap_def, he]
    exact s.tower.map_id (Opposite.op i)
  rw [hid]
  infer_instance

/- English proof (authored)
Induct on the upper endpoint starting at the lower endpoint. The initial transition is the identity. At a successor the transition factors as the last single blowup followed by the shorter transition. The last center is the unit ideal by hypothesis, so its blowup is an isomorphism. The shorter transition is an isomorphism by induction, and their composite is an isomorphism.
-/
theorem isIso_transitionMap_of_center_eq_top (s : SequenceOfBlowups X) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ s.length) (h : ∀ i, a ≤ i → i < b → s.center i = ⊤) :
    IsIso (s.transitionMap hab) := by
  revert hb h
  induction b, hab using Nat.le_induction with
  | base =>
    intro _ _
    exact isIso_transitionMap_refl s _
  | succ b hab ih =>
    intro hb h
    have hbl : b ≤ s.length := le_trans (Nat.le_succ b) hb
    have hlt : b < s.length := lt_of_lt_of_le (Nat.lt_succ_self b) hb
    have hcen : s.center b = ⊤ := h b hab (Nat.lt_succ_self b)
    have : IsIso (s.transitionMap hab) :=
      ih hbl fun i hi hib => h i hi (Nat.lt_succ_of_lt hib)
    have hB : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc b) (s.center b) := s.isBlowupAlongIdealSheaf_blowupMorphism b hlt
    rw [hcen] at hB
    have : IsIso (s.transitionMap (Nat.le_succ b)) := by
      have h4 := hB.isIso_of_top
      rw [s.blowupMorphism_eq_transitionMap b] at h4
      exact h4
    have h3 : IsIso (s.transitionMap (Nat.le_succ b) ≫ s.transitionMap hab) := inferInstance
    rw [s.transitionMap_trans hab (Nat.le_succ b)] at h3
    exact h3

/- English proof (authored)
Choose the larger of the starting index and the sequence length. It is at least the starting index and satisfies the stopping condition because it is at least the length.
-/
theorem exists_le_center_ne_top_or_length_le (s : SequenceOfBlowups X) (a : ℕ) :
    ∃ i, a ≤ i ∧ (s.center i ≠ ⊤ ∨ s.length ≤ i) :=
  ⟨max a s.length, le_max_left _ _, Or.inr (le_max_right _ _)⟩

noncomputable def nextNontrivialIndex (s : SequenceOfBlowups X) (a : ℕ) : ℕ :=
  @Nat.find _ (fun _ => Classical.propDecidable _) (s.exists_le_center_ne_top_or_length_le a)

/- English proof (authored)
The search returns the least index at or above the starting index with a nonunit center or at or beyond the end. By the defining property of a least witness, the returned index satisfies both conditions.
-/
theorem nextNontrivialIndex_spec (s : SequenceOfBlowups X) (a : ℕ) :
    a ≤ s.nextNontrivialIndex a ∧ (s.center (s.nextNontrivialIndex a) ≠ ⊤ ∨ s.length ≤ s.nextNontrivialIndex a) :=
  @Nat.find_spec _ (fun _ => Classical.propDecidable _) (s.exists_le_center_ne_top_or_length_le a)

/- English proof (authored)
The search specification includes the condition that the returned index is at least the starting index.
-/
theorem le_nextNontrivialIndex (s : SequenceOfBlowups X) (a : ℕ) : a ≤ s.nextNontrivialIndex a :=
  (s.nextNontrivialIndex_spec a).1

/- English proof (authored)
The index selected by the search meets its defining stopping condition. Its center is nonunit or the index is at least the length.
-/
theorem center_nextNontrivialIndex_ne_top_or_length_le (s : SequenceOfBlowups X) (a : ℕ) :
    s.center (s.nextNontrivialIndex a) ≠ ⊤ ∨ s.length ≤ s.nextNontrivialIndex a :=
  (s.nextNontrivialIndex_spec a).2

/- English proof (authored)
The candidate lies at or above the starting index and meets the stopping condition. The search chooses the least such candidate, giving the claimed bound.
-/
theorem nextNontrivialIndex_le (s : SequenceOfBlowups X) {a i : ℕ} (hi : a ≤ i)
    (h : s.center i ≠ ⊤ ∨ s.length ≤ i) : s.nextNontrivialIndex a ≤ i :=
  @Nat.find_min' _ (fun _ => Classical.propDecidable _) (s.exists_le_center_ne_top_or_length_le a) i ⟨hi, h⟩

/- English proof (authored)
The sequence length is at least the starting index by hypothesis and automatically satisfies the end-of-sequence condition. Minimality bounds the search result by the length.
-/
theorem nextNontrivialIndex_le_length (s : SequenceOfBlowups X) {a : ℕ} (h : a ≤ s.length) :
    s.nextNontrivialIndex a ≤ s.length :=
  s.nextNontrivialIndex_le h (Or.inr le_rfl)

/- English proof (authored)
If the earlier index had a nonunit center, it would be an admissible result for the search. Minimality would then bound the search result by that index, contradicting the strict inequality.
-/
theorem center_eq_top_of_lt_nextNontrivialIndex (s : SequenceOfBlowups X) {a i : ℕ} (hai : a ≤ i)
    (h : i < s.nextNontrivialIndex a) : s.center i = ⊤ := by
  by_contra hc
  exact absurd (s.nextNontrivialIndex_le hai (Or.inl hc)) (not_le.mpr h)

noncomputable def nontrivialIndex (s : SequenceOfBlowups X) (j : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (s.nextNontrivialIndex 0) (fun _ ih => s.nextNontrivialIndex (ih + 1)) j

/- English proof (authored)
The enumeration begins by searching for the next nontrivial index starting at zero.
-/
@[simp] theorem nontrivialIndex_zero (s : SequenceOfBlowups X) : s.nontrivialIndex 0 = s.nextNontrivialIndex 0 := rfl

/- English proof (authored)
The recursive step resumes the search at one more than the preceding retained index.
-/
@[simp] theorem nontrivialIndex_succ (s : SequenceOfBlowups X) (j : ℕ) :
    s.nontrivialIndex (j + 1) = s.nextNontrivialIndex (s.nontrivialIndex j + 1) := rfl

/- English proof (authored)
The next retained index is at least the starting index of its search, which is the preceding retained index plus one. Thus it is strictly greater than the preceding index.
-/
theorem nontrivialIndex_lt_succ (s : SequenceOfBlowups X) (j : ℕ) : s.nontrivialIndex j < s.nontrivialIndex (j + 1) := by
  have h := s.le_nextNontrivialIndex (s.nontrivialIndex j + 1)
  rw [nontrivialIndex_succ]
  exact h

/- English proof (authored)
For natural numbers, strict inequality between two consecutive retained indices means that one plus the earlier index is at most the later index.
-/
theorem succ_le_nontrivialIndex_succ (s : SequenceOfBlowups X) (j : ℕ) :
    s.nontrivialIndex j + 1 ≤ s.nontrivialIndex (j + 1) :=
  s.nontrivialIndex_lt_succ j

/- English proof (authored)
Successive values strictly increase. Chaining these one-step inequalities across any finite interval gives strict monotonicity.
-/
theorem nontrivialIndex_strictMono (s : SequenceOfBlowups X) : StrictMono s.nontrivialIndex :=
  strictMono_nat_of_lt_succ s.nontrivialIndex_lt_succ

/- English proof (authored)
Strict increase implies weak increase for unequal indices, and equal indices have equal values.
-/
theorem nontrivialIndex_monotone (s : SequenceOfBlowups X) : Monotone s.nontrivialIndex :=
  s.nontrivialIndex_strictMono.monotone

/- English proof (authored)
The first value is a natural number and hence at least zero. Each successive value is at least one larger than the preceding value. Induction therefore bounds the enumeration index by its value.
-/
theorem le_nontrivialIndex (s : SequenceOfBlowups X) (j : ℕ) : j ≤ s.nontrivialIndex j :=
  s.nontrivialIndex_strictMono.le_apply

/- English proof (authored)
Both the initial retained index and every successor retained index are results of the same search. In each case the result satisfies the stopping condition of having a nonunit center or reaching the sequence length.
-/
theorem center_nontrivialIndex_ne_top_or_length_le (s : SequenceOfBlowups X) (j : ℕ) :
    s.center (s.nontrivialIndex j) ≠ ⊤ ∨ s.length ≤ s.nontrivialIndex j := by
  cases j with
  | zero => exact s.center_nextNontrivialIndex_ne_top_or_length_le 0
  | succ j => exact s.center_nextNontrivialIndex_ne_top_or_length_le (s.nontrivialIndex j + 1)

/- English proof (authored)
The first search starts at zero, and the given index precedes its least admissible result. Therefore its center is the unit ideal.
-/
theorem center_eq_top_of_lt_nontrivialIndex_zero (s : SequenceOfBlowups X) {i : ℕ} (h : i < s.nontrivialIndex 0) :
    s.center i = ⊤ :=
  s.center_eq_top_of_lt_nextNontrivialIndex (Nat.zero_le i) h

/- English proof (authored)
The next search starts just after the preceding retained index. The index in question lies within that search range and before the result. If its center were nonunit the search would have stopped there or earlier, so its center is the unit ideal.
-/
theorem center_eq_top_of_nontrivialIndex_lt (s : SequenceOfBlowups X) {i j : ℕ} (h1 : s.nontrivialIndex j < i)
    (h2 : i < s.nontrivialIndex (j + 1)) : s.center i = ⊤ :=
  s.center_eq_top_of_lt_nextNontrivialIndex h1 h2

/- English proof (authored)
Use the sequence length as the enumeration index. The retained index function has value at least its argument, so the result is at least the length.
-/
theorem exists_length_le_nontrivialIndex (s : SequenceOfBlowups X) : ∃ j, s.length ≤ s.nontrivialIndex j :=
  ⟨s.length, s.le_nontrivialIndex s.length⟩

noncomputable def lengthWithoutIsoBlowups (s : SequenceOfBlowups X) : ℕ :=
  @Nat.find _ (fun _ => Classical.propDecidable _) s.exists_length_le_nontrivialIndex

/- English proof (authored)
The shortened length is the first enumeration index whose retained value reaches or exceeds the original length. Its retained value therefore satisfies that lower bound.
-/
theorem length_le_nontrivialIndex_lengthWithoutIsoBlowups (s : SequenceOfBlowups X) :
    s.length ≤ s.nontrivialIndex s.lengthWithoutIsoBlowups :=
  @Nat.find_spec _ (fun _ => Classical.propDecidable _) s.exists_length_le_nontrivialIndex

/- English proof (authored)
At index zero the search starts at zero and can always stop at the original length. At a successor, the preceding retained value is strictly below the length by hypothesis, so restarting at its successor is still at or below the length. In either case the length is an admissible endpoint, bounding the search result.
-/
private theorem nontrivialIndex_le_length_of_forall_lt (s : SequenceOfBlowups X) (j : ℕ)
    (h : ∀ i, i < j → s.nontrivialIndex i < s.length) : s.nontrivialIndex j ≤ s.length := by
  cases j with
  | zero =>
      show s.nextNontrivialIndex 0 ≤ s.length
      exact s.nextNontrivialIndex_le_length (Nat.zero_le _)
  | succ j =>
      have hj : s.nontrivialIndex j < s.length := h j (Nat.lt_succ_self j)
      show s.nextNontrivialIndex (s.nontrivialIndex j + 1) ≤ s.length
      exact s.nextNontrivialIndex_le_length hj

/- English proof (authored)
At the shortened length the retained value is at least the original length. Every earlier value is strictly below that length by minimality. The search that produces the value at the shortened length therefore starts at or below the original length and cannot pass it. The two bounds give equality.
-/
theorem nontrivialIndex_lengthWithoutIsoBlowups (s : SequenceOfBlowups X) : s.nontrivialIndex s.lengthWithoutIsoBlowups = s.length := by
  refine le_antisymm (nontrivialIndex_le_length_of_forall_lt s s.lengthWithoutIsoBlowups ?_)
    s.length_le_nontrivialIndex_lengthWithoutIsoBlowups
  intro i hi
  have hmin := @Nat.find_min _ (fun _ => Classical.propDecidable _)
    s.exists_length_le_nontrivialIndex i hi
  exact not_le.mp hmin

/- English proof (authored)
A value at an enumeration index strictly before the shortened length cannot already reach the original length, since that would contradict minimality of the shortened length.
-/
theorem nontrivialIndex_lt_length (s : SequenceOfBlowups X) {j : ℕ} (h : j < s.lengthWithoutIsoBlowups) :
    s.nontrivialIndex j < s.length := by
  have h' : ¬ (s.length ≤ s.nontrivialIndex j) :=
    @Nat.find_min _ (fun _ => Classical.propDecidable _) s.exists_length_le_nontrivialIndex j h
  exact not_le.mp h'

/- English proof (authored)
For the initial value, the original length is an admissible bound for the search. At a successor within the shortened length, the preceding value is strictly below the original length. The new search therefore starts at or below that length and cannot pass it.
-/
theorem nontrivialIndex_le_length (s : SequenceOfBlowups X) {j : ℕ} (h : j ≤ s.lengthWithoutIsoBlowups) :
    s.nontrivialIndex j ≤ s.length := by
  cases j with
  | zero => exact s.nextNontrivialIndex_le_length (Nat.zero_le _)
  | succ i =>
    have hi : i < s.lengthWithoutIsoBlowups := lt_of_lt_of_le (Nat.lt_succ_self i) h
    have hlt : s.nontrivialIndex i + 1 ≤ s.length := s.nontrivialIndex_lt_length hi
    exact s.nextNontrivialIndex_le_length hlt

/- English proof (authored)
The indexed search result has a nonunit center or reaches the original length. Since this is a position strictly within the shortened sequence, the retained value is below the original length. Thus the center is nonunit.
-/
theorem center_nontrivialIndex_ne_top (s : SequenceOfBlowups X) {j : ℕ} (h : j < s.lengthWithoutIsoBlowups) :
    s.center (s.nontrivialIndex j) ≠ ⊤ := by
  rcases s.center_nontrivialIndex_ne_top_or_length_le j with hc | hc
  · exact hc
  · exact absurd hc (not_le.mpr (s.nontrivialIndex_lt_length h))

/- English proof (authored)
The first retained index is at most the original length, and all centers before it are unit ideals. The transition across that initial interval is therefore an isomorphism.
-/
theorem isIso_transitionMap_nontrivialIndex_zero (s : SequenceOfBlowups X) :
    IsIso (s.transitionMap (Nat.zero_le (s.nontrivialIndex 0))) := by
  refine s.isIso_transitionMap_of_center_eq_top (Nat.zero_le (s.nontrivialIndex 0)) ?_ ?_
  · exact s.nextNontrivialIndex_le_length (Nat.zero_le _)
  · intro i _ hi
    exact s.center_eq_top_of_lt_nontrivialIndex_zero hi

/- English proof (authored)
Between the stage immediately after the retained blowup and the next retained stage, all omitted centers are unit ideals. The next retained stage is at most the original length. The transition across this interval is therefore an isomorphism.
-/
theorem isIso_transitionMap_nontrivialIndex_succ (s : SequenceOfBlowups X) {j : ℕ} (h : j < s.lengthWithoutIsoBlowups) :
    IsIso (s.transitionMap (s.succ_le_nontrivialIndex_succ j)) := by
  refine s.isIso_transitionMap_of_center_eq_top (s.succ_le_nontrivialIndex_succ j)
    (s.nontrivialIndex_le_length (Nat.succ_le_of_lt h)) ?_
  intro i hi hib
  exact s.center_eq_top_of_nontrivialIndex_lt (Nat.lt_of_succ_le hi) hib

noncomputable def objNontrivialIndexZeroIso (s : SequenceOfBlowups X) : s.schemeAt (s.nontrivialIndex 0) ≅ X :=
  haveI : IsIso (s.transitionMap (Nat.zero_le (s.nontrivialIndex 0))) := s.isIso_transitionMap_nontrivialIndex_zero
  (asIso (s.transitionMap (Nat.zero_le (s.nontrivialIndex 0)))).trans s.isoZero

/- English proof (authored)
The forward map first takes the initial run of omitted blowups back to stage zero and then applies the original initial isomorphism. That composite is the projection to the base at the first retained index.
-/
theorem objNontrivialIndexZeroIso_hom (s : SequenceOfBlowups X) :
    s.objNontrivialIndexZeroIso.hom = s.projectionToBase (s.nontrivialIndex 0) := by
  rw [projectionToBase_def]
  rfl

noncomputable def towerWithoutIsoBlowups (s : SequenceOfBlowups X) : ℕᵒᵖ ⥤ Scheme.{u} :=
  (Monotone.functor s.nontrivialIndex_monotone).op ⋙ s.tower

/- English proof (authored)
The shortened transition factors through the stage immediately after the original retained blowup. The map back from the next retained stage to that intermediate stage is an isomorphism, since all intervening centers are unit ideals. The other factor is the original blowup along the retained center. Precomposing a blowup with an isomorphism of its source leaves it a blowup along the same ideal.
-/
private theorem isBlowupAlongIdealSheaf_towerWithoutIsoBlowups_map (s : SequenceOfBlowups X) (i : ℕ) (hi : i < s.lengthWithoutIsoBlowups) :
    Blowup.IsBlowupAlongIdealSheaf (s.towerWithoutIsoBlowups.map (homOfLE (Nat.le_succ i)).op) (s.center (s.nontrivialIndex i)) := by
  have : IsIso (s.transitionMap (s.succ_le_nontrivialIndex_succ i)) := s.isIso_transitionMap_nontrivialIndex_succ hi
  have hB : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc (s.nontrivialIndex i)) (s.center (s.nontrivialIndex i)) :=
    s.isBlowupAlongIdealSheaf_blowupMorphism (s.nontrivialIndex i) (s.nontrivialIndex_lt_length hi)
  have hcomp := hB.iso_hom_comp (asIso (s.transitionMap (s.succ_le_nontrivialIndex_succ i)))
  have heq : (asIso (s.transitionMap (s.succ_le_nontrivialIndex_succ i))).hom ≫ s.transitionMapSucc (s.nontrivialIndex i)
      = s.transitionMap (s.nontrivialIndex_monotone (Nat.le_succ i)) := by
    rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
    exact s.transitionMap_trans (Nat.le_succ (s.nontrivialIndex i)) (s.succ_le_nontrivialIndex_succ i)
  rw [heq] at hcomp
  show Blowup.IsBlowupAlongIdealSheaf (s.transitionMap (s.nontrivialIndex_monotone (Nat.le_succ i))) (s.center (s.nontrivialIndex i))
  exact hcomp

noncomputable def withoutIsoBlowups (s : SequenceOfBlowups X) : SequenceOfBlowups X where
  length := s.lengthWithoutIsoBlowups
  tower := s.towerWithoutIsoBlowups
  isoZero := s.objNontrivialIndexZeroIso
  center := fun j => s.center (s.nontrivialIndex j)
  isBlowup := s.isBlowupAlongIdealSheaf_towerWithoutIsoBlowups_map

/- English proof (authored)
The shortened sequence is defined with length equal to the first enumeration index whose retained value reaches the original length.
-/
@[simp] theorem withoutIsoBlowups_length (s : SequenceOfBlowups X) : s.withoutIsoBlowups.length = s.lengthWithoutIsoBlowups := rfl

/- English proof (authored)
The shortened tower is the original tower evaluated at the retained indices. Its scheme at the given index is therefore the original scheme at the corresponding retained index.
-/
@[simp] theorem withoutIsoBlowups_schemeAt (s : SequenceOfBlowups X) (j : ℕ) :
    s.withoutIsoBlowups.schemeAt j = s.schemeAt (s.nontrivialIndex j) := rfl

/- English proof (authored)
The center of the shortened sequence is defined by evaluating the original center at the corresponding retained index.
-/
@[simp] theorem withoutIsoBlowups_center (s : SequenceOfBlowups X) (j : ℕ) :
    s.withoutIsoBlowups.center j = s.center (s.nontrivialIndex j) := rfl

/- English proof (authored)
The shortened sequence uses the previously constructed isomorphism from the first retained stage to the original base as its stage-zero isomorphism.
-/
theorem withoutIsoBlowups_isoObjZero (s : SequenceOfBlowups X) : s.withoutIsoBlowups.isoZero = s.objNontrivialIndexZeroIso := rfl

/- English proof (authored)
The shortened tower is obtained by precomposing the original tower with the map of ordered indexing categories given by the monotone retained-index function. The resulting transition is the original transition for the inequality between the retained indices.
-/
theorem withoutIsoBlowups_transitionMap (s : SequenceOfBlowups X) {j j' : ℕ} (h : j ≤ j') :
    s.withoutIsoBlowups.transitionMap h = s.transitionMap (s.nontrivialIndex_monotone h) := by
  rw [SequenceOfBlowups.transitionMap_def, SequenceOfBlowups.transitionMap_def]
  rfl

/- English proof (authored)
Apply the formula for shortened transitions to the order arrow from a stage to its successor, which defines the shortened blowup morphism.
-/
theorem withoutIsoBlowups_blowupMorphism (s : SequenceOfBlowups X) (j : ℕ) :
    s.withoutIsoBlowups.transitionMapSucc j = s.transitionMap (s.nontrivialIndex_monotone (Nat.le_succ j)) := by
  rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, withoutIsoBlowups_transitionMap]

/- English proof (authored)
Every center of the shortened sequence is the original center at its retained index. For a position within the shortened length, the search result lies before the original end and has a nonunit center.
-/
theorem withoutIsoBlowups_center_ne_top (s : SequenceOfBlowups X) {j : ℕ} (h : j < s.withoutIsoBlowups.length) :
    s.withoutIsoBlowups.center j ≠ ⊤ := by
  exact s.center_nontrivialIndex_ne_top h

/- English proof (authored)
The last retained index is exactly the original length. Evaluating the original tower at these equal indices identifies the two last objects.
-/
theorem withoutIsoBlowups_lastObj (s : SequenceOfBlowups X) : s.withoutIsoBlowups.lastObj = s.lastObj :=
  congrArg s.schemeAt s.nontrivialIndex_lengthWithoutIsoBlowups

/- English proof (authored)
Replace the equal indices by a single index. The indicated transport morphism then becomes the identity, whose composite with the projection is that projection.
-/
private theorem projectionToBase_eq_eqToHom_comp (s : SequenceOfBlowups X) {a b : ℕ} (h : a = b) :
    s.projectionToBase a = eqToHom (congrArg s.schemeAt h) ≫ s.projectionToBase b := by
  subst h
  simp

/- English proof (authored)
The shortened projection is the original transition to the first retained stage followed by the shortened initial isomorphism. This isomorphism’s forward map is the original projection from the first retained stage. The transition compatibility for projections identifies the composite with the original projection from the given retained stage.
-/
theorem withoutIsoBlowups_projectionToBase_eq_nontrivialIndex (s : SequenceOfBlowups X) (j : ℕ) :
    s.withoutIsoBlowups.projectionToBase j = s.projectionToBase (s.nontrivialIndex j) := by
  have h0 : s.withoutIsoBlowups.isoZero.hom = s.projectionToBase (s.nontrivialIndex 0) := s.objNontrivialIndexZeroIso_hom
  rw [projectionToBase_def, withoutIsoBlowups_transitionMap, h0]
  exact s.transitionMap_comp_projectionToBase _

/- English proof (authored)
The final shortened structural map is the original projection from the final retained stage. That retained index equals the original length, so transport along the induced equality of last objects identifies the projection with the original final structural map.
-/
theorem withoutIsoBlowups_lastStructMap (s : SequenceOfBlowups X) :
    s.withoutIsoBlowups.lastStructMap = eqToHom s.withoutIsoBlowups_lastObj ≫ s.lastStructMap := by
  have h0 : s.withoutIsoBlowups.isoZero.hom = s.projectionToBase (s.nontrivialIndex 0) := s.objNontrivialIndexZeroIso_hom
  have h1 : s.withoutIsoBlowups.lastStructMap = s.projectionToBase (s.nontrivialIndex s.withoutIsoBlowups.length) := by
    rw [lastStructMap_eq_projectionToBase, projectionToBase_def, withoutIsoBlowups_transitionMap, h0]
    exact s.transitionMap_comp_projectionToBase _
  rw [h1, lastStructMap_eq_projectionToBase]
  exact projectionToBase_eq_eqToHom_comp s s.nontrivialIndex_lengthWithoutIsoBlowups

/- English proof (authored)
A point on a shortened center is a point on the original center at the corresponding retained index. The shortened projection to the base equals the original projection from that stage. Its image lies in the prescribed set by the original center condition.
-/
theorem withoutIsoBlowups_centersLieOver (s : SequenceOfBlowups X) {S : Set X} (h : s.CentersLieOver S) :
    s.withoutIsoBlowups.CentersLieOver S := by
  intro j hj x hx
  have hx' : x ∈ (s.center (s.nontrivialIndex j)).support := hx
  have h2 := h (s.nontrivialIndex j) (s.nontrivialIndex_lt_length hj) x hx'
  rw [withoutIsoBlowups_projectionToBase_eq_nontrivialIndex]
  exact h2

end SequenceOfBlowups

end FunctorialResolution.EmbeddedResolution
