import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedLocusFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.BinaryCoproductBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrictTransformTower
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

namespace EmbeddedBlowupSequence

/- English proof (authored)
The inclusion of an old detached piece into the successor coproduct first includes it in the preceding coproduct and then includes that coproduct as the old summand. Passing from the successor to the later coproduct gives the inclusion of the same piece at the later stage.
-/
theorem detachedToCoprod_detachedCoprodInl_detachedCoprodMapOfLE (S : EmbeddedBlowupSequence k Y pY) (s a b : ℕ)
    (hsa : s < a) (hab : a + 1 ≤ b) :
    S.detachedToCoprod s a hsa ≫ S.detachedCoprodInl a ≫ S.detachedCoprodMapOfLE hab =
      S.detachedToCoprod s b (lt_of_lt_of_le hsa (le_trans (Nat.le_succ a) hab)) := by
  rw [← Category.assoc, ← S.detachedToCoprod_succ_of_lt s a hsa, S.detachedToCoprod_detachedCoprodMapOfLE]

/- English proof (authored)
The inclusion of the new summand is the inclusion of the piece detached at this step into the successor coproduct. Composing with the map to the later stage gives the corresponding inclusion there.
-/
theorem detachedCoprodInr_detachedCoprodMapOfLE (S : EmbeddedBlowupSequence k Y pY) (a b : ℕ) (hab : a + 1 ≤ b) :
    S.detachedCoprodInr a ≫ S.detachedCoprodMapOfLE hab =
      S.detachedToCoprod a b (lt_of_lt_of_le (Nat.lt_succ_self a) hab) := by
  rw [← S.detachedToCoprod_self a, S.detachedToCoprod_detachedCoprodMapOfLE]

def inactiveTotalToBase (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups) (i : ℕ) :
    S.detachedCoprod i ⟶ Y :=
  (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ (S.inducedBlowups h).projectionToBase i

/- English proof (authored)
The inactive map to the base is the detached-summand inclusion followed by the projection of the induced blowup sequence. On a piece detached at an earlier stage, that projection factors through the strict transform at the stage of detachment.
-/
theorem detachedToCoprod_inactiveTotalToBase (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups) (s i : ℕ)
    (hs : s < i) :
    S.detachedToCoprod s i hs ≫ S.inactiveTotalToBase h i = S.detachedι s ≫ S.strictTransformToBase s :=
  detachedToCoprod_inr_inducedBlowups_projectionToBase S h s i hs

/- English proof (authored)
Check the two summands of the total space. The projection of the induced blowup sequence restricts to the strict-transform map on the first summand and to the inactive map by definition on the second. The coproduct universal property then identifies the projection.
-/
theorem coprodDesc_strictTransformToBase_inactiveTotalToBase (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups) (i : ℕ) :
    coprod.desc (S.strictTransformToBase i) (S.inactiveTotalToBase h i) = (S.inducedBlowups h).projectionToBase i := by
  apply coprod.hom_ext
  · rw [coprod.inl_desc]
    exact (inl_inducedBlowups_projectionToBase S h i).symm
  · rw [coprod.inr_desc]
    rfl

end EmbeddedBlowupSequence

namespace ChartFlatBaseChange

variable {k' : Type u} [Field k'] [CharZero k'] {Y' : Scheme.{u}} [AlgebraicGeometry.IsAffine Y']
  {pY' : Y' ⟶ Spec (CommRingCat.of k')} [AlgebraicGeometry.LocallyOfFiniteType pY']
  {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

/- English proof (authored)
The comparison reindexing is strictly increasing on the stages under consideration. Both given indices are in that range, so it preserves their strict inequality.
-/
theorem reindex_lt_reindex (F : ChartFlatBaseChange S S') {s j : ℕ} (hsj : s < j)
    (hj : j ≤ S'.length) : F.reindex s < F.reindex j :=
  F.reindex_lt_reindex_of_lt hsj hj

/- English proof (authored)
The bound on the successor places the preceding stage strictly before the end of the sequence. Strict increase of the reindexing across this step gives the required weak inequality.
-/
private theorem reindex_le_reindex_succ (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j + 1 ≤ S'.length) :
    F.reindex j ≤ F.reindex (j + 1) :=
  (F.reindex_lt_succ j (by omega)).le

/- English proof (authored)
The bound on the successor places the preceding stage strictly before the end of the sequence. Apply strict increase of the reindexing across this step.
-/
private theorem reindex_lt_reindex_succ (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j + 1 ≤ S'.length) :
    F.reindex j < F.reindex (j + 1) :=
  F.reindex_lt_succ j (by omega)

/- English proof (authored)
Postcompose both maps to the original base with its closed immersion into the ambient base. On the first route, express the strict-transform projection through its ambient stage, then commute the strict-transform comparison with the stage inclusions. The ambient stage pullback square commutes with the ambient projections. On the second route, the projection through the new ambient stage agrees with the strict-transform projection followed by the new base embedding, and the comparison square of base embeddings commutes. The postcomposites agree, so cancel the original base embedding, which is a monomorphism.
-/
theorem strictTransformComparison_comp_strictTransformToBase (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length) :
    F.strictTransformComparison j hj ≫ S.strictTransformToBase (F.reindex j) = S'.strictTransformToBase j ≫ F.baseMap := by
  have : CategoryTheory.Mono S.emb := inferInstance
  have key : (F.strictTransformComparison j hj ≫ S.strictTransformToBase (F.reindex j)) ≫ S.emb
      = (S'.strictTransformToBase j ≫ F.baseMap) ≫ S.emb := by
    calc (F.strictTransformComparison j hj ≫ S.strictTransformToBase (F.reindex j)) ≫ S.emb
        = F.strictTransformComparison j hj ≫ (S.strictTransformToBase (F.reindex j) ≫ S.emb) := Category.assoc _ _ _
      _ = F.strictTransformComparison j hj ≫
            (S.strictTransformι (F.reindex j) ≫ S.ambientSeq.projectionToBase (F.reindex j)) := by
            rw [S.strictTransformToBase_emb (F.reindex j)]
      _ = (F.strictTransformComparison j hj ≫ S.strictTransformι (F.reindex j)) ≫
            S.ambientSeq.projectionToBase (F.reindex j) := (Category.assoc _ _ _).symm
      _ = (S'.strictTransformι j ≫ F.levelMap j hj) ≫ S.ambientSeq.projectionToBase (F.reindex j) := by
            rw [F.strictTransformComparison_comp_strictTransformι j hj]
      _ = S'.strictTransformι j ≫ (F.levelMap j hj ≫ S.ambientSeq.projectionToBase (F.reindex j)) :=
            Category.assoc _ _ _
      _ = S'.strictTransformι j ≫ (S'.ambientSeq.projectionToBase j ≫ F.ambientMap) := by
            rw [(F.isPullback_level j hj).w]
      _ = (S'.strictTransformι j ≫ S'.ambientSeq.projectionToBase j) ≫ F.ambientMap :=
            (Category.assoc _ _ _).symm
      _ = (S'.strictTransformToBase j ≫ S'.emb) ≫ F.ambientMap := by rw [S'.strictTransformToBase_emb j]
      _ = S'.strictTransformToBase j ≫ (S'.emb ≫ F.ambientMap) := Category.assoc _ _ _
      _ = S'.strictTransformToBase j ≫ (F.baseMap ≫ S.emb) := by rw [F.isPullback_emb.w]
      _ = (S'.strictTransformToBase j ≫ F.baseMap) ≫ S.emb := (Category.assoc _ _ _).symm
  exact (cancel_mono S.emb).mp key

/- English proof (authored)
Paste the pullback square for the strict-transform inclusions with the pullback square for the ambient stage projections. Identify the vertical composites as the strict-transform projections followed by the base embeddings. The square for those embeddings is a pullback, and the strict-transform projections commute with the comparison maps. Pullback cancellation therefore gives the desired square over the bases.
-/
theorem isPullback_strictTransformComparison_strictTransformToBase (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length) :
    IsPullback (F.strictTransformComparison j hj) (S'.strictTransformToBase j) (S.strictTransformToBase (F.reindex j))
      F.baseMap := by
  have h1 := (F.isPullback_strictTransformComparison_strictTransformι j hj).paste_vert (F.isPullback_level j hj)
  have h2 : IsPullback (F.strictTransformComparison j hj) (S'.strictTransformToBase j ≫ S'.emb)
      (S.strictTransformToBase (F.reindex j) ≫ S.emb) F.ambientMap := by
    rw [S'.strictTransformToBase_emb j, S.strictTransformToBase_emb (F.reindex j)]
    exact h1
  exact h2.of_bot (F.strictTransformComparison_comp_strictTransformToBase j hj) F.isPullback_emb

/- English proof (authored)
Compose the given compatibility over the original base with the original base embedding. The strict-transform projection through its ambient stage and the square of base embeddings turn this into compatibility over the ambient base, with the map to the new base followed by its embedding. The emptiness criterion for an omitted detached piece now applies.
-/
theorem isEmpty_of_comm_detachedScheme_of_not_mem_range (F : ChartFlatBaseChange S S') (s : ℕ) (hs : s < S.length)
    (hskip : ∀ j, j < S'.length → F.reindex j ≠ s) (Q : Scheme.{u}) (q : Q ⟶ S.detachedScheme s)
    (p : Q ⟶ Y') (hcomm : q ≫ S.detachedι s ≫ S.strictTransformToBase s = p ≫ F.baseMap) :
    IsEmpty ↥Q := by
  refine F.isEmpty_of_forall_reindex_ne s hs hskip Q q (p ≫ S'.emb) ?_
  calc q ≫ S.detachedι s ≫ S.strictTransformι s ≫ S.ambientSeq.projectionToBase s
      = q ≫ S.detachedι s ≫ S.strictTransformToBase s ≫ S.emb := by rw [S.strictTransformToBase_emb s]
    _ = (q ≫ S.detachedι s ≫ S.strictTransformToBase s) ≫ S.emb := by simp only [Category.assoc]
    _ = (p ≫ F.baseMap) ≫ S.emb := by rw [hcomm]
    _ = p ≫ (F.baseMap ≫ S.emb) := Category.assoc _ _ _
    _ = p ≫ (S'.emb ≫ F.ambientMap) := by rw [F.isPullback_emb.w]
    _ = (p ≫ S'.emb) ≫ F.ambientMap := (Category.assoc _ _ _).symm

/- English proof (authored)
A map to the initial scheme induces a function from the source's underlying space to the empty set. Thus the source has no points.
-/
private theorem isEmpty_of_hom_to_initial {P : Scheme.{u}}
    (f : P ⟶ ⊥_ Scheme.{u}) : IsEmpty ↥P :=
  Function.isEmpty f.base

/- English proof (authored)
For each earlier detached piece, both routes through the old summand map it to the base through its strict transform at detachment. The old summand therefore retains its preceding base map. On the new summand the base map is its detachment inclusion followed by that stage's strict-transform projection. These restrictions determine the map on the successor coproduct.
-/
private theorem inactiveTotalToBase_succ_eq_desc (T : EmbeddedBlowupSequence k Y pY)
    (hT : T.TransitionsAreBlowups) (i : ℕ) :
    T.inactiveTotalToBase hT (i + 1) =
      coprod.desc (T.inactiveTotalToBase hT i) (T.detachedι i ≫ T.strictTransformToBase i) := by
  have hl : T.detachedCoprodInl i ≫ T.inactiveTotalToBase hT (i + 1) = T.inactiveTotalToBase hT i := by
    refine T.detachedCoprod_hom_ext i ?_
    intro s hs
    calc T.detachedToCoprod s i hs ≫ T.detachedCoprodInl i ≫ T.inactiveTotalToBase hT (i + 1)
        = (T.detachedToCoprod s i hs ≫ T.detachedCoprodInl i) ≫ T.inactiveTotalToBase hT (i + 1) :=
          (Category.assoc _ _ _).symm
      _ = T.detachedToCoprod s (i + 1) (Nat.lt_succ_of_lt hs) ≫ T.inactiveTotalToBase hT (i + 1) := by
          rw [T.detachedToCoprod_succ_of_lt s i hs]
      _ = T.detachedι s ≫ T.strictTransformToBase s :=
          T.detachedToCoprod_inactiveTotalToBase hT s (i + 1) (Nat.lt_succ_of_lt hs)
      _ = T.detachedToCoprod s i hs ≫ T.inactiveTotalToBase hT i :=
          (T.detachedToCoprod_inactiveTotalToBase hT s i hs).symm
  have hr : T.detachedCoprodInr i ≫ T.inactiveTotalToBase hT (i + 1) = T.detachedι i ≫ T.strictTransformToBase i := by
    calc T.detachedCoprodInr i ≫ T.inactiveTotalToBase hT (i + 1)
        = T.detachedToCoprod i (i + 1) (Nat.lt_succ_self i) ≫ T.inactiveTotalToBase hT (i + 1) := by
          rw [T.detachedToCoprod_self i]
      _ = T.detachedι i ≫ T.strictTransformToBase i :=
          T.detachedToCoprod_inactiveTotalToBase hT i (i + 1) (Nat.lt_succ_self i)
  refine T.detachedCoprod_succ_hom_ext i ?_ ?_
  · exact hl.trans (coprod.inl_desc _ _).symm
  · exact hr.trans (coprod.inr_desc _ _).symm

/- English proof (authored)
Induct on the number of detached stages in the coproduct. At zero, any source mapping to the empty coproduct is empty. At a successor, the pullback of the older coproduct is empty by induction and the pullback of the new piece is empty by the criterion for omitted stages. Base change of their coproduct is the coproduct of these two empty pullbacks, using the summand description of the map to the base. A scheme with the stated compatible maps maps to this empty coproduct, so it is empty.
-/
private theorem forall_isEmpty_of_comm_inactiveTotalToBase (F : ChartFlatBaseChange S S')
    (h : S.TransitionsAreBlowups) :
    ∀ (i : ℕ), (∀ s, s < i → s < S.length) →
      (∀ s, s < i → ∀ j, j < S'.length → F.reindex j ≠ s) →
      ∀ (P : Scheme.{u}) (q : P ⟶ S.detachedCoprod i) (p : P ⟶ Y'),
        q ≫ S.inactiveTotalToBase h i = p ≫ F.baseMap → IsEmpty ↥P := by
  intro i
  induction i with
  | zero =>
      intro _ _ P q _ _
      exact isEmpty_of_hom_to_initial q
  | succ n ih =>
      intro hlt hskip P q p hcomm
      have h1 : IsPullback (initial.to (S.detachedCoprod n)) (initial.to Y')
          (S.inactiveTotalToBase h n) F.baseMap :=
        isPullback_initial_of_isEmpty (S.inactiveTotalToBase h n) F.baseMap
          (fun Q a b hab =>
            ih (fun s hs => hlt s (Nat.lt_succ_of_lt hs))
              (fun s hs => hskip s (Nat.lt_succ_of_lt hs)) Q a b hab)
      have h2 : IsPullback (initial.to (S.detachedScheme n)) (initial.to Y')
          (S.detachedι n ≫ S.strictTransformToBase n) F.baseMap :=
        isPullback_initial_of_isEmpty (S.detachedι n ≫ S.strictTransformToBase n) F.baseMap
          (fun Q c d hcd =>
            F.isEmpty_of_comm_detachedScheme_of_not_mem_range n (hlt n (Nat.lt_succ_self n))
              (hskip n (Nat.lt_succ_self n)) Q c d hcd)
      have h3 := isPullback_coprodMap_coprodDesc (initial.to (S.detachedCoprod n))
        (initial.to (S.detachedScheme n)) (initial.to Y') (initial.to Y')
        (S.inactiveTotalToBase h n) (S.detachedι n ≫ S.strictTransformToBase n) F.baseMap h1 h2
      have hcomm' : q ≫ coprod.desc (S.inactiveTotalToBase h n) (S.detachedι n ≫ S.strictTransformToBase n)
          = p ≫ F.baseMap :=
        (congrArg (fun t : S.detachedCoprod (n + 1) ⟶ Y => q ≫ t)
          (inactiveTotalToBase_succ_eq_desc S h n)).symm.trans hcomm
      exact isEmpty_of_hom_to_initial
        (h3.lift q p hcomm' ≫ coprod.desc (𝟙 (⊥_ Scheme.{u})) (𝟙 (⊥_ Scheme.{u})))

/- English proof (authored)
Every summand is indexed by an existing stage omitted by the reindexing, by the two assumptions on the indices. Apply the preceding induction criterion to the compatible pair of maps.
-/
theorem isEmpty_of_comm_inactiveTotalToBase_of_not_mem_range (F : ChartFlatBaseChange S S') (h : S.TransitionsAreBlowups)
    (i : ℕ) (hlt : ∀ s, s < i → s < S.length)
    (hskip : ∀ s, s < i → ∀ j, j < S'.length → F.reindex j ≠ s) (P : Scheme.{u})
    (q : P ⟶ S.detachedCoprod i) (p : P ⟶ Y')
    (hcomm : q ≫ S.inactiveTotalToBase h i = p ≫ F.baseMap) : IsEmpty ↥P :=
  forall_isEmpty_of_comm_inactiveTotalToBase F h i hlt hskip P q p hcomm

/- English proof (authored)
Induct from the initial stage of the interval to its endpoint. At the initial stage the coproduct map is the identity, so the starting square is the given pullback. At a successor the new detached piece is omitted by the reindexing, so it has empty pullback. The successor map to the base is the coproduct of the previous base map and that piece's map. Its pullback is therefore still represented by the preceding pullback, with the first projection followed by the inclusion of the old summand. This inclusion extends the coproduct map through the successor and proves the induction step.
-/
theorem isPullback_detachedCoprodMapOfLE_inactiveTotalToBase (F : ChartFlatBaseChange S S') (h : S.TransitionsAreBlowups)
    {a b : ℕ} (hab : a ≤ b) (hlt : ∀ s, a ≤ s → s < b → s < S.length)
    (hskip : ∀ s, a ≤ s → s < b → ∀ j, j < S'.length → F.reindex j ≠ s) {P : Scheme.{u}}
    (q : P ⟶ S.detachedCoprod a) (p : P ⟶ Y')
    (hsq : IsPullback q p (S.inactiveTotalToBase h a) F.baseMap) :
    IsPullback (q ≫ S.detachedCoprodMapOfLE hab) p (S.inactiveTotalToBase h b) F.baseMap := by
  have main : ∀ (c : ℕ) (hac : a ≤ c),
      (∀ s, a ≤ s → s < c → s < S.length) →
      (∀ s, a ≤ s → s < c → ∀ j, j < S'.length → F.reindex j ≠ s) →
      IsPullback (q ≫ S.detachedCoprodMapOfLE hac) p (S.inactiveTotalToBase h c) F.baseMap := by
    intro c hac
    induction c, hac using Nat.le_induction with
    | base =>
        intro _ _
        have hself : S.detachedCoprodMapOfLE (Nat.le_refl a) = 𝟙 (S.detachedCoprod a) := S.detachedCoprodMapOfLE_self a
        have hpbRefl : IsPullback (q ≫ S.detachedCoprodMapOfLE (Nat.le_refl a)) p
            (S.inactiveTotalToBase h a) F.baseMap := by
          rw [hself, Category.comp_id]
          exact hsq
        exact hpbRefl
    | succ c hac ih =>
        intro hlt1 hskip1
        have ih' := ih (fun s h1 h2 => hlt1 s h1 (Nat.lt_succ_of_lt h2))
          (fun s h1 h2 => hskip1 s h1 (Nat.lt_succ_of_lt h2))
        have hc : c < S.length := hlt1 c hac (Nat.lt_succ_self c)
        have hsk : ∀ j, j < S'.length → F.reindex j ≠ c := hskip1 c hac (Nat.lt_succ_self c)
        have hF : ∀ (Q : Scheme.{u}) (cc : Q ⟶ S.detachedScheme c) (d : Q ⟶ Y'),
            cc ≫ S.detachedι c ≫ S.strictTransformToBase c = d ≫ F.baseMap → IsEmpty Q :=
          fun Q cc d hcomm => F.isEmpty_of_comm_detachedScheme_of_not_mem_range c hc hsk Q cc d hcomm
        have hinl : S.detachedCoprodInl c ≫ S.inactiveTotalToBase h (c + 1) = S.inactiveTotalToBase h c := by
          show S.detachedCoprodInl c ≫ (coprod.inr : S.detachedCoprod (c + 1) ⟶ S.totalSpace (c + 1)) ≫
              (S.inducedBlowups h).projectionToBase (c + 1) = S.inactiveTotalToBase h c
          rw [SequenceOfBlowups.projectionToBase_succ, inducedBlowups_blowupMorphism]
          exact S.detachedCoprodInl_inr_totalTransition_assoc c ((S.inducedBlowups h).projectionToBase c)
        have hinr : S.detachedCoprodInr c ≫ S.inactiveTotalToBase h (c + 1) =
            S.detachedι c ≫ S.strictTransformToBase c := by
          have hkey := S.detachedToCoprod_inactiveTotalToBase h c (c + 1) (Nat.lt_succ_self c)
          rw [S.detachedToCoprod_self c] at hkey
          exact hkey
        have hdesc : (coprod.desc (S.inactiveTotalToBase h c) (S.detachedι c ≫ S.strictTransformToBase c) :
            S.detachedCoprod c ⨿ S.detachedScheme c ⟶ Y) = S.inactiveTotalToBase h (c + 1) := by
          apply coprod.hom_ext
          · rw [coprod.inl_desc]
            exact hinl.symm
          · rw [coprod.inr_desc]
            exact hinr.symm
        have key1 : IsPullback ((q ≫ S.detachedCoprodMapOfLE hac) ≫ S.detachedCoprodInl c) p
            (S.inactiveTotalToBase h (c + 1)) F.baseMap := by
          have key0 := isPullback_comp_inl_coprodDesc (q ≫ S.detachedCoprodMapOfLE hac) p
            (S.inactiveTotalToBase h c) F.baseMap (S.detachedι c ≫ S.strictTransformToBase c) ih' hF
          rw [hdesc] at key0
          exact key0
        have hup : S.detachedCoprodMapOfLE (Nat.le_succ_of_le hac) = S.detachedCoprodMapOfLE hac ≫ S.detachedCoprodInl c :=
          S.detachedCoprodMapOfLE_succ hac
        have hpbSucc : IsPullback (q ≫ S.detachedCoprodMapOfLE (Nat.le_succ_of_le hac)) p
            (S.inactiveTotalToBase h (c + 1)) F.baseMap := by
          rw [hup, ← Category.assoc]
          exact key1
        exact hpbSucc
  exact main b hab hlt hskip

/- English proof (authored)
Paste the pullback square comparing the detached schemes inside their strict transforms with the pullback square comparing the strict transforms over the bases. The resulting projections are the detachment inclusions followed by the strict-transform projections.
-/
theorem isPullback_inactiveSchemeMap_baseMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    IsPullback (F.detachedSchemeComparison j hj) (S'.detachedι j ≫ S'.strictTransformToBase j)
      (S.detachedι (F.reindex j) ≫ S.strictTransformToBase (F.reindex j)) F.baseMap :=
  (F.isPullback_detachedSchemeComparison j hj).paste_vert (F.isPullback_strictTransformComparison_strictTransformToBase j hj.le)

def inactiveTotalMap (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] :
    ∀ (j : ℕ), j ≤ S'.length → (S'.detachedCoprod j ⟶ S.detachedCoprod (F.reindex j))
  | 0, _ => eqToHom S'.detachedCoprod_zero ≫ initial.to (S.detachedCoprod (F.reindex 0))
  | (j + 1), hj =>
      eqToHom (S'.detachedCoprod_succ j) ≫
        coprod.desc
          (inactiveTotalMap F j (Nat.le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ j hj))
          (F.detachedSchemeComparison j (by omega) ≫
            S.detachedToCoprod (F.reindex j) (F.reindex (j + 1)) (F.reindex_lt_reindex_succ j hj))

/- English proof (authored)
At a successor, the recursive map is defined on the old summand by the preceding comparison followed by the map to the later coproduct. On the new summand it compares the detached piece and includes it at the reindexed stage. Identifying the source with this coproduct gives the stated map.
-/
private theorem inactiveTotalMap_succ_eq_desc (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (n : ℕ)
    (hj : n + 1 ≤ S'.length) :
    F.inactiveTotalMap (n + 1) hj =
      coprod.desc
        (F.inactiveTotalMap n (Nat.le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ n hj))
        (F.detachedSchemeComparison n (lt_of_lt_of_le (Nat.lt_succ_self n) hj) ≫
          S.detachedToCoprod (F.reindex n) (F.reindex (n + 1)) (F.reindex_lt_reindex_succ n hj)) := by
  have h0 : F.inactiveTotalMap (n + 1) hj =
      eqToHom (S'.detachedCoprod_succ n) ≫
        coprod.desc
          (F.inactiveTotalMap n (Nat.le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ n hj))
          (F.detachedSchemeComparison n (lt_of_lt_of_le (Nat.lt_succ_self n) hj) ≫
            S.detachedToCoprod (F.reindex n) (F.reindex (n + 1)) (F.reindex_lt_reindex_succ n hj)) := rfl
  have hid : eqToHom (S'.detachedCoprod_succ n) = 𝟙 (S'.detachedCoprod (n + 1)) := eqToHom_refl _ _
  rw [h0, hid]
  exact Category.id_comp _

/- English proof (authored)
Restrict the successor comparison to the old summand. By its coproduct description, this is the preceding comparison followed by the inclusion of the earlier target coproduct into the later target coproduct.
-/
private theorem detachedCoprodInl_inactiveTotalMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (n : ℕ)
    (hj : n + 1 ≤ S'.length) :
    S'.detachedCoprodInl n ≫ F.inactiveTotalMap (n + 1) hj =
      F.inactiveTotalMap n (Nat.le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ n hj) := by
  rw [inactiveTotalMap_succ_eq_desc F n hj]
  exact coprod.inl_desc _ _

/- English proof (authored)
Restrict the successor comparison to the new summand. Its coproduct description gives the comparison of the newly detached scheme followed by that piece's inclusion in the reindexed coproduct.
-/
private theorem detachedCoprodInr_inactiveTotalMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (n : ℕ)
    (hj : n + 1 ≤ S'.length) :
    S'.detachedCoprodInr n ≫ F.inactiveTotalMap (n + 1) hj =
      F.detachedSchemeComparison n (lt_of_lt_of_le (Nat.lt_succ_self n) hj) ≫
        S.detachedToCoprod (F.reindex n) (F.reindex (n + 1)) (F.reindex_lt_reindex_succ n hj) := by
  rw [inactiveTotalMap_succ_eq_desc F n hj]
  exact coprod.inr_desc _ _

/- English proof (authored)
Induct on the stage of the coproduct. The initial coproduct has no earlier index. At a successor, a piece from a strictly earlier stage factors through the old summand. Apply the induction hypothesis there and compose the inclusion of the corresponding piece with the map to the larger target coproduct. For the piece detached at the current step, the restriction to the new summand gives the asserted formula directly.
-/
private theorem forall_detachedToCoprod_inactiveTotalMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] :
    ∀ (j : ℕ) (hj : j ≤ S'.length) (s : ℕ) (hs : s < j),
      S'.detachedToCoprod s j hs ≫ F.inactiveTotalMap j hj =
        F.detachedSchemeComparison s (lt_of_lt_of_le hs hj) ≫
          S.detachedToCoprod (F.reindex s) (F.reindex j) (F.reindex_lt_reindex hs hj) := by
  intro j
  induction j with
  | zero =>
      intro hj s hs
      exact absurd hs (Nat.not_lt_zero s)
  | succ n ih =>
      intro hj s hs
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hs) with hlt | heq
      · rw [S'.detachedToCoprod_succ_of_lt s n hlt, Category.assoc,
          detachedCoprodInl_inactiveTotalMap F n hj, ← Category.assoc,
          ih (Nat.le_of_succ_le hj) s hlt, Category.assoc, S.detachedToCoprod_detachedCoprodMapOfLE]
      · subst heq
        rw [S'.detachedToCoprod_self s, detachedCoprodInr_inactiveTotalMap F s hj]

/- English proof (authored)
Apply the inductive description of the inactive comparison on each detached summand to the specified stage and summand index.
-/
theorem detachedToCoprod_inactiveTotalMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length)
    (s : ℕ) (hs : s < j) :
    S'.detachedToCoprod s j hs ≫ F.inactiveTotalMap j hj =
      F.detachedSchemeComparison s (lt_of_lt_of_le hs hj) ≫
        S.detachedToCoprod (F.reindex s) (F.reindex j) (F.reindex_lt_reindex hs hj) :=
  forall_detachedToCoprod_inactiveTotalMap F j hj s hs

/- English proof (authored)
Check the two maps on each piece of the older coproduct. Including that piece first in the successor and then in the later stage gives its inclusion at the later stage. The direct map from the older coproduct has the same restriction. Thus the maps agree.
-/
private theorem inl_detachedCoprodMapOfLE (T : EmbeddedBlowupSequence k Y pY) {c b : ℕ}
    (hcb : c + 1 ≤ b) :
    (coprod.inl : T.detachedCoprod c ⟶ T.detachedCoprod c ⨿ T.detachedScheme c) ≫ T.detachedCoprodMapOfLE hcb =
      T.detachedCoprodMapOfLE (Nat.le_of_succ_le hcb) := by
  refine T.detachedCoprod_hom_ext c (fun s hs => ?_)
  have h1 := T.detachedToCoprod_detachedCoprodInl_detachedCoprodMapOfLE s c b hs hcb
  have h2 := T.detachedToCoprod_detachedCoprodMapOfLE hs (Nat.le_of_succ_le hcb)
  exact h1.trans h2.symm

/- English proof (authored)
The second inclusion inserts the newly detached piece into the successor coproduct. The map to the later coproduct carries this inclusion to the inclusion of the same piece there.
-/
private theorem inr_detachedCoprodMapOfLE (T : EmbeddedBlowupSequence k Y pY) {c b : ℕ}
    (hcb : c + 1 ≤ b) :
    (coprod.inr : T.detachedScheme c ⟶ T.detachedCoprod c ⨿ T.detachedScheme c) ≫ T.detachedCoprodMapOfLE hcb =
      T.detachedToCoprod c b hcb :=
  T.detachedCoprodInr_detachedCoprodMapOfLE c b hcb

/- English proof (authored)
Replace the first projection by its equal map in the given pullback square. The universal property stays the same.
-/
private theorem isPullback_of_fst_eq {P X Z W : Scheme.{u}} {f f' : P ⟶ X} {g : P ⟶ Z}
    {q : X ⟶ W} {u : Z ⟶ W} (hf : f = f') (hp : IsPullback f' g q u) : IsPullback f g q u := by
  subst hf
  exact hp

/- English proof (authored)
Use the two equalities to replace both projections of the given pullback. The same universal property proves the assertion.
-/
private theorem isPullback_of_fst_eq_of_snd_eq {P X Z W : Scheme.{u}} {f f' : P ⟶ X}
    {g g' : P ⟶ Z} {q : X ⟶ W} {u : Z ⟶ W} (hf : f = f') (hg : g = g')
    (hp : IsPullback f' g' q u) : IsPullback f g q u := by
  subst hf
  subst hg
  exact hp

/- English proof (authored)
Substitute the equal second projection and the equal map from the first target to the base. This gives exactly the given pullback square.
-/
private theorem isPullback_of_snd_eq_of_map_eq {P X Z W : Scheme.{u}} {f : P ⟶ X} {g g' : P ⟶ Z}
    {q q' : X ⟶ W} {u : Z ⟶ W} (hg : g = g') (hq : q = q')
    (hp : IsPullback f g' q' u) : IsPullback f g q u := by
  subst hg
  subst hq
  exact hp

/- English proof (authored)
Induct on the source stage. At zero the source coproduct is empty, and every target summand before the initial reindexed stage is omitted. Their pullback is empty, so the two unique projections from the initial scheme give the desired square. At a successor take the coproduct of the previous comparison square and the square for the newly detached piece. This gives a pullback up to the stage just after that piece in the original sequence. Any remaining intervening stages are omitted, so including their pieces preserves the pullback. On the old and new summands the resulting first projection gives the two defining restrictions of the successor comparison, which identifies the resulting square.
-/
theorem isPullback_inactiveTotalMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y']
    (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups) (j : ℕ) (hj : j ≤ S'.length) :
    IsPullback (F.inactiveTotalMap j hj) (S'.inactiveTotalToBase h' j)
      (S.inactiveTotalToBase h (F.reindex j)) F.baseMap := by
  have main : ∀ (m : ℕ) (hm : m ≤ S'.length),
      IsPullback (F.inactiveTotalMap m hm) (S'.inactiveTotalToBase h' m)
        (S.inactiveTotalToBase h (F.reindex m)) F.baseMap := by
    intro m
    induction m with
    | zero =>
        intro hm
        have hI : IsInitial (S'.detachedCoprod 0) := initialIsInitial
        have hlen : F.reindex 0 ≤ S.length := F.reindex_le_length (Nat.zero_le S'.length)
        have hempty : ∀ (P : Scheme.{u}) (a : P ⟶ S.detachedCoprod (F.reindex 0)) (b : P ⟶ Y'),
            a ≫ S.inactiveTotalToBase h (F.reindex 0) = b ≫ F.baseMap → IsEmpty ↥P := by
          intro P a b hcomm
          exact F.isEmpty_of_comm_inactiveTotalToBase_of_not_mem_range h (F.reindex 0)
            (fun s hs => lt_of_lt_of_le hs hlen)
            (fun s hs j' hj' => F.reindex_ne_of_lt_reindex_zero s hs j' hj') P a b hcomm
        have hpb :=
          isPullback_initial_of_isEmpty (S.inactiveTotalToBase h (F.reindex 0)) F.baseMap hempty
        have e1 : F.inactiveTotalMap 0 hm = initial.to (S.detachedCoprod (F.reindex 0)) :=
          hI.hom_ext _ _
        have e2 : S'.inactiveTotalToBase h' 0 = initial.to Y' := hI.hom_ext _ _
        exact isPullback_of_fst_eq_of_snd_eq e1 e2 hpb
    | succ n ih =>
        intro hm
        have hn : n ≤ S'.length := Nat.le_of_succ_le hm
        have hnlt : n < S'.length := hm
        have hab : F.reindex n + 1 ≤ F.reindex (n + 1) := F.reindex_lt_succ n hnlt
        have hlen : F.reindex (n + 1) ≤ S.length := F.reindex_le_length hm
        have hcop := isPullback_coprodMap_coprodDesc (F.inactiveTotalMap n hn)
          (F.detachedSchemeComparison n hnlt) (S'.inactiveTotalToBase h' n) (S'.detachedι n ≫ S'.strictTransformToBase n)
          (S.inactiveTotalToBase h (F.reindex n))
          (S.detachedι (F.reindex n) ≫ S.strictTransformToBase (F.reindex n)) F.baseMap (ih hn)
          (F.isPullback_inactiveSchemeMap_baseMap n hnlt)
        have hcop2 : IsPullback
            (coprod.map (F.inactiveTotalMap n hn) (F.detachedSchemeComparison n hnlt))
            (S'.inactiveTotalToBase h' (n + 1)) (S.inactiveTotalToBase h (F.reindex n + 1)) F.baseMap :=
          isPullback_of_snd_eq_of_map_eq (inactiveTotalToBase_succ_eq_desc S' h' n)
            (inactiveTotalToBase_succ_eq_desc S h (F.reindex n)) hcop
        have hstep := F.isPullback_detachedCoprodMapOfLE_inactiveTotalToBase h hab
          (fun s _ hs2 => lt_of_lt_of_le hs2 hlen)
          (fun s hs1 hs2 j' hj' => F.reindex_ne_of_reindex_lt_of_lt_reindex_succ n hnlt s (by omega) hs2 j' hj')
          (coprod.map (F.inactiveTotalMap n hn) (F.detachedSchemeComparison n hnlt))
          (S'.inactiveTotalToBase h' (n + 1)) hcop2
        have hE : F.inactiveTotalMap (n + 1) hm =
            coprod.map (F.inactiveTotalMap n hn) (F.detachedSchemeComparison n hnlt) ≫
              S.detachedCoprodMapOfLE hab := by
          refine S'.detachedCoprod_succ_hom_ext n ?_ ?_
          · exact (detachedCoprodInl_inactiveTotalMap F n hm).trans
              ((coprod.inl_map_assoc (F.inactiveTotalMap n hn)
                  (F.detachedSchemeComparison n hnlt) (S.detachedCoprodMapOfLE hab)).trans
                (congrArg
                  (fun t : (S.detachedCoprod (F.reindex n) ⟶ S.detachedCoprod (F.reindex (n + 1))) =>
                    F.inactiveTotalMap n hn ≫ t)
                  (inl_detachedCoprodMapOfLE S hab))).symm
          · exact (detachedCoprodInr_inactiveTotalMap F n hm).trans
              ((coprod.inr_map_assoc (F.inactiveTotalMap n hn)
                  (F.detachedSchemeComparison n hnlt) (S.detachedCoprodMapOfLE hab)).trans
                (congrArg
                  (fun t : (S.detachedScheme (F.reindex n) ⟶ S.detachedCoprod (F.reindex (n + 1))) =>
                    F.detachedSchemeComparison n hnlt ≫ t)
                  (inr_detachedCoprodMapOfLE S hab))).symm
        exact isPullback_of_fst_eq hE hstep
  exact main j hj

def totalSpaceMap (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length) :
    S'.totalSpace j ⟶ S.totalSpace (F.reindex j) :=
  coprod.map (F.strictTransformComparison j hj) (F.inactiveTotalMap j hj)

/- English proof (authored)
The total space is the coproduct of the strict transform and accumulated detached pieces. Its comparison is defined as the coproduct map of the strict-transform comparison and the inactive comparison.
-/
theorem totalSpaceMap_eq_coprodMap (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length) :
    F.totalSpaceMap j hj = coprod.map (F.strictTransformComparison j hj) (F.inactiveTotalMap j hj) := rfl

/- English proof (authored)
Restrict the coproduct comparison to the strict-transform summand. This gives the strict-transform comparison followed by the corresponding target inclusion.
-/
theorem inl_totalSpaceMap (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length) :
    (coprod.inl : S'.strictTransform j ⟶ S'.totalSpace j) ≫ F.totalSpaceMap j hj =
      F.strictTransformComparison j hj ≫
        (coprod.inl : S.strictTransform (F.reindex j) ⟶ S.totalSpace (F.reindex j)) := by
  simp [ChartFlatBaseChange.totalSpaceMap]

/- English proof (authored)
On the inactive summand the total space comparison is the inactive comparison followed by the target inclusion. Restrict that comparison to the specified detached scheme using its summand formula, then compose with the inclusion into the target total space.
-/
theorem detachedToCoprod_inr_totalSpaceMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length)
    (s : ℕ) (hs : s < j) :
    S'.detachedToCoprod s j hs ≫ (coprod.inr : S'.detachedCoprod j ⟶ S'.totalSpace j) ≫
        F.totalSpaceMap j hj =
      F.detachedSchemeComparison s (lt_of_lt_of_le hs hj) ≫
        S.detachedToCoprod (F.reindex s) (F.reindex j) (F.reindex_lt_reindex hs hj) ≫
          (coprod.inr : S.detachedCoprod (F.reindex j) ⟶ S.totalSpace (F.reindex j)) := by
  rw [F.totalSpaceMap_eq_coprodMap j hj, coprod.inr_map, ← Category.assoc,
    F.detachedToCoprod_inactiveTotalMap j hj s hs, Category.assoc]

/- English proof (authored)
The strict-transform comparison and the inactive comparison each give pullback squares over the same map of bases. Take their coproduct on each side. The resulting projections are the projections of the induced blowup sequences, since those restrict to the two component maps. Its comparison is the total space map by definition.
-/
theorem isPullback_totalSpaceMap (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
    (j : ℕ) (hj : j ≤ S'.length) :
    IsPullback (F.totalSpaceMap j hj) ((S'.inducedBlowups h').projectionToBase j)
      ((S.inducedBlowups h).projectionToBase (F.reindex j)) F.baseMap := by
  have key := isPullback_coprodMap_coprodDesc (F.strictTransformComparison j hj)
    (F.inactiveTotalMap j hj) (S'.strictTransformToBase j) (S'.inactiveTotalToBase h' j)
    (S.strictTransformToBase (F.reindex j)) (S.inactiveTotalToBase h (F.reindex j)) F.baseMap
    (F.isPullback_strictTransformComparison_strictTransformToBase j hj) (F.isPullback_inactiveTotalMap h h' j hj)
  rw [S'.coprodDesc_strictTransformToBase_inactiveTotalToBase h' j, S.coprodDesc_strictTransformToBase_inactiveTotalToBase h (F.reindex j)] at key
  rw [F.totalSpaceMap_eq_coprodMap j hj]
  exact key

end ChartFlatBaseChange

end FunctorialResolution.EmbeddedResolution

end
