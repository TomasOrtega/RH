import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransformOffCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceTransitions
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  {k' : Type u} [Field k'] [CharZero k'] {Y' : Scheme.{u}} [AlgebraicGeometry.IsAffine Y']
  {pY' : Y' ⟶ Spec (CommRingCat.of k')} [AlgebraicGeometry.LocallyOfFiniteType pY']

structure ChartFlatBaseChange (S : EmbeddedBlowupSequence k Y pY) (S' : EmbeddedBlowupSequence k' Y' pY') where
  ambientMap : S'.ambient ⟶ S.ambient
  flat_ambientMap : AlgebraicGeometry.Flat ambientMap
  baseMap : Y' ⟶ Y
  isPullback_emb : IsPullback baseMap S'.emb S.emb ambientMap
  reindex : ℕ → ℕ
  levelMap : ∀ j : ℕ, j ≤ S'.length → (S'.schemeAt j ⟶ S.schemeAt (reindex j))
  reindex_lt : ∀ j : ℕ, j < S'.length → reindex j < S.length
  reindex_lt_succ : ∀ j : ℕ, j < S'.length → reindex j < reindex (j + 1)
  reindex_len : reindex S'.length = S.length
  isPullback_level : ∀ (j : ℕ) (hj : j ≤ S'.length),
    IsPullback (levelMap j hj) (S'.ambientSeq.projectionToBase j)
      (S.ambientSeq.projectionToBase (reindex j)) ambientMap
  isPullback_down : ∀ (j : ℕ) (hj : j ≤ S'.length) (i : ℕ) (hi : i ≤ reindex j),
    (∀ m, i ≤ m → m < reindex j → ∀ j', j' < S'.length → reindex j' ≠ m) →
    IsPullback (levelMap j hj ≫ S.ambientSeq.transitionMap hi) (S'.ambientSeq.projectionToBase j)
      (S.ambientSeq.projectionToBase i) ambientMap
  isPullback_step : ∀ (j : ℕ) (hj : j < S'.length) (hσ : reindex j + 1 ≤ reindex (j + 1)),
    IsPullback (levelMap (j + 1) (Nat.succ_le_of_lt hj) ≫ S.ambientSeq.transitionMap hσ)
      (S'.blowdown j) (S.blowdown (reindex j)) (levelMap j (Nat.le_of_lt hj))
  center_eq : ∀ (j : ℕ) (hj : j < S'.length),
    S'.ambientCenter j = (S.ambientCenter (reindex j)).comap (levelMap j (Nat.le_of_lt hj))
  comap_center_skipped : ∀ i, i < S.length → (∀ j, j < S'.length → reindex j ≠ i) →
    ∀ (P : Scheme.{u}) (q : P ⟶ S.schemeAt i) (p : P ⟶ S'.ambient),
      IsPullback q p (S.ambientSeq.projectionToBase i) ambientMap → (S.ambientCenter i).comap q = ⊤

namespace ChartFlatBaseChange

variable {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

instance instFlatAmbientMap (F : ChartFlatBaseChange S S') :
    AlgebraicGeometry.Flat F.ambientMap := F.flat_ambientMap

/- English proof (authored)
Each consecutive pair of values through the bound is strictly increasing. Chaining these inequalities from the lower index to the higher one gives the stated strict inequality.
-/
private theorem apply_lt_apply_of_forall_lt_succ
    {σ : ℕ → ℕ} {N : ℕ} (h : ∀ j, j < N → σ j < σ (j + 1)) :
    ∀ j, j ≤ N → ∀ i, i < j → σ i < σ j := by
  intro j hj i hij
  exact strictMonoOn_Iic_of_lt_succ h (Set.mem_Iic.mpr (le_trans (le_of_lt hij) hj))
    (Set.mem_Iic.mpr hj) hij

/- English proof (authored)
The chart comparison requires strict increase at each consecutive source index. The chain of one-step inequalities gives strict increase between the two specified indices.
-/
theorem reindex_lt_reindex_of_lt (F : ChartFlatBaseChange S S') {i j : ℕ} (hij : i < j) (hj : j ≤ S'.length) :
    F.reindex i < F.reindex j :=
  apply_lt_apply_of_forall_lt_succ (σ := F.reindex) (N := S'.length)
    F.reindex_lt_succ j hj i hij

/- English proof (authored)
At the final source index the reindexing is the target length by hypothesis. At any earlier index it is strictly below the target length. Either case gives the weak bound.
-/
theorem reindex_le_length (F : ChartFlatBaseChange S S') {j : ℕ} (hj : j ≤ S'.length) :
    F.reindex j ≤ S.length := by
  rcases eq_or_lt_of_le hj with h | h
  · subst h
    exact le_of_eq F.reindex_len
  · exact le_of_lt (F.reindex_lt j h)

/- English proof (authored)
The stage comparison is a pullback of the flat ambient comparison along the target projection to its ambient base. Flatness is preserved by pullback.
-/
theorem flat_levelMap (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length) :
    AlgebraicGeometry.Flat (F.levelMap j hj) := by
  have hst : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.Flat : MorphismProperty Scheme.{u}) := inferInstance
  exact hst.of_isPullback (F.isPullback_level j hj).flip F.flat_ambientMap

/- English proof (authored)
The reindexed zero is at most every retained index by monotonicity. An index strictly below it therefore cannot be retained.
-/
theorem reindex_ne_of_lt_reindex_zero (F : ChartFlatBaseChange S S') (m : ℕ)
    (hm : m < F.reindex 0) (j : ℕ) (hj : j < S'.length) : F.reindex j ≠ m := by
  have h : F.reindex 0 ≤ F.reindex j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      exact le_rfl
    · exact le_of_lt (F.reindex_lt_reindex_of_lt h0 (le_of_lt hj))
  omega

/- English proof (authored)
An index at or before the given source stage has reindexed value at most the earlier endpoint. An index at or after its successor has value at least the later endpoint. Thus no retained value lies strictly between these consecutive endpoints.
-/
theorem reindex_ne_of_reindex_lt_of_lt_reindex_succ (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length) (m : ℕ)
    (h1 : F.reindex j < m) (h2 : m < F.reindex (j + 1)) (j' : ℕ) (hj' : j' < S'.length) :
    F.reindex j' ≠ m := by
  intro hEq
  rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
  · have hle : F.reindex j' ≤ F.reindex j := by
      rcases Nat.lt_or_ge j' j with h | h
      · exact le_of_lt (F.reindex_lt_reindex_of_lt h (le_of_lt hj))
      · have hjj : j' = j := le_antisymm (Nat.lt_succ_iff.mp hlt) h
        subst hjj
        exact le_rfl
    omega
  · have hle : F.reindex (j + 1) ≤ F.reindex j' := by
      rcases Nat.eq_or_lt_of_le hge with h | h
      · exact le_of_eq (congrArg F.reindex h)
      · exact le_of_lt (F.reindex_lt_reindex_of_lt h (le_of_lt hj'))
    omega

/- English proof (authored)
Induct on the number of omitted steps between the earlier stage and the reindexed stage. With zero steps the transition is the identity. Otherwise the first omitted center pulls back to the unit ideal on the comparison scheme, since the relevant stage square is a pullback and the step is omitted. The strict transform agrees with the total transform after this pullback because the pulled-back center is unit. Thus pulling the earlier ideal back equals pulling back the next strict-transform ideal along the comparison to that stage. Apply induction across the remaining omitted steps, using composition of the ambient transitions.
-/
private theorem strictTransformIdeal_comap_transitionMap_eq (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length) :
    ∀ (n i : ℕ) (hi : i ≤ F.reindex j), i + n = F.reindex j →
      (∀ m, i ≤ m → m < F.reindex j → ∀ j', j' < S'.length → F.reindex j' ≠ m) →
      (S.strictTransformIdeal i).comap (F.levelMap j hj ≫ S.ambientSeq.transitionMap hi)
        = (S.strictTransformIdeal (F.reindex j)).comap (F.levelMap j hj) := by
  intro n
  induction n with
  | zero =>
      intro i hi hsum _
      have hie : i = F.reindex j := by omega
      subst hie
      rw [S.ambientSeq.transitionMap_self hi, Category.comp_id]
  | succ n ih =>
      intro i hi hsum hskip
      have hi1 : i + 1 ≤ F.reindex j := by omega
      have hlen : F.reindex j ≤ S.length := F.reindex_le_length hj
      have hiS : i + 1 ≤ S.length := le_trans hi1 hlen
      have := S.isNoetherian_schemeAt (i + 1) hiS
      have hIH := ih (i + 1) hi1 (by omega)
        (fun m hm hm2 j' hj' => hskip m (by omega) hm2 j' hj')
      have hdown : S.ambientSeq.transitionMap hi1 ≫ S.blowdown i = S.ambientSeq.transitionMap hi := by
        have h := S.ambientSeq.transitionMap_trans (Nat.le_succ i) hi1
        rw [← S.ambientSeq.blowupMorphism_eq_transitionMap] at h
        exact h
      have htop : (S.ambientCenter i).comap (F.levelMap j hj ≫ S.ambientSeq.transitionMap hi) = ⊤ :=
        F.comap_center_skipped i (by omega) (fun j' hj' => hskip i le_rfl (by omega) j' hj')
          (S'.schemeAt j) (F.levelMap j hj ≫ S.ambientSeq.transitionMap hi)
          (S'.ambientSeq.projectionToBase j) (F.isPullback_down j hj i hi hskip)
      have hg : ((S.ambientCenter i).comap (S.blowdown i)).comap
          (F.levelMap j hj ≫ S.ambientSeq.transitionMap hi1) = ⊤ := by
        rw [← Scheme.IdealSheafData.comap_comp, Category.assoc, hdown]
        exact htop
      have hst := strictTransform_comap_of_comap_center_eq_top (S.blowdown i)
        (S.ambientCenter i) (S.strictTransformIdeal i) (F.levelMap j hj ≫ S.ambientSeq.transitionMap hi1) hg
      rw [← hIH, S.strictTransformIdeal_succ i, hst, ← Scheme.IdealSheafData.comap_comp, Category.assoc,
        hdown]

/- English proof (authored)
At zero the ideals are the kernels of the original closed embeddings transported to their initial ambient stages. The embedding pullback square remains a pullback after transport by the initial isomorphisms, and the comparison to the original stage zero is flat. Thus the kernel formula for flat base change gives equality there. The omitted initial centers have unit pullbacks, so the equality also holds at the first retained stage. At a successor the ambient comparison square identifies the new blowup with the flat base change of the original retained blowup. The preceding strict-transform ideal and center are corresponding pullbacks, so flat base change of strict transforms identifies the successor ideals at this blowup. All intervening stages before the next retained index are omitted, and pullback across their unit centers preserves the strict-transform ideal. This gives the equality at the next retained index and completes the induction.
-/
theorem strictTransformIdeal_eq_comap (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length) :
    S'.strictTransformIdeal j = (S.strictTransformIdeal (F.reindex j)).comap (F.levelMap j hj) := by
  revert hj
  induction j with
  | zero =>
      intro hj
      have h0 : (0 : ℕ) ≤ F.reindex 0 := Nat.zero_le _
      have hskip : ∀ m, 0 ≤ m → m < F.reindex 0 → ∀ j', j' < S'.length → F.reindex j' ≠ m :=
        fun m _ hm j' hj' => F.reindex_ne_of_lt_reindex_zero m hm j' hj'
      have hkey := strictTransformIdeal_comap_transitionMap_eq F 0 hj (F.reindex 0) 0 h0 (by omega) hskip
      have hlev : IsPullback (F.levelMap 0 hj ≫ S.ambientSeq.transitionMap h0)
          (S'.ambientSeq.projectionToBase 0) (S.ambientSeq.projectionToBase 0) F.ambientMap :=
        F.isPullback_down 0 hj 0 h0 hskip
      have hcomm : S'.ambientSeq.isoZero.inv ≫ (F.levelMap 0 hj ≫ S.ambientSeq.transitionMap h0)
          = F.ambientMap ≫ S.ambientSeq.isoZero.inv := by
        have h1 := hlev.w
        rw [S.ambientSeq.projectionToBase_zero, S'.ambientSeq.projectionToBase_zero] at h1
        have h2 : (S'.ambientSeq.isoZero.inv ≫ (F.levelMap 0 hj ≫ S.ambientSeq.transitionMap h0)) ≫
            S.ambientSeq.isoZero.hom
            = (F.ambientMap ≫ S.ambientSeq.isoZero.inv) ≫ S.ambientSeq.isoZero.hom := by
          simp only [Category.assoc] at h1 ⊢
          rw [h1]
          simp
        exact (cancel_mono S.ambientSeq.isoZero.hom).mp h2
      have hD : IsPullback F.ambientMap S'.ambientSeq.isoZero.inv S.ambientSeq.isoZero.inv
          (F.levelMap 0 hj ≫ S.ambientSeq.transitionMap h0) :=
        (IsPullback.of_horiz_isIso ⟨hcomm⟩).flip
      have hC : IsPullback F.baseMap (S'.emb ≫ S'.ambientSeq.isoZero.inv)
          (S.emb ≫ S.ambientSeq.isoZero.inv) (F.levelMap 0 hj ≫ S.ambientSeq.transitionMap h0) :=
        F.isPullback_emb.paste_vert hD
      have : AlgebraicGeometry.QuasiCompact (S.emb ≫ S.ambientSeq.isoZero.inv) := inferInstance
      have : AlgebraicGeometry.QuasiCompact (S'.emb ≫ S'.ambientSeq.isoZero.inv) :=
        quasiCompact_of_isPullback hC
      have : AlgebraicGeometry.Flat (F.levelMap 0 hj ≫ S.ambientSeq.transitionMap h0) :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (P := @AlgebraicGeometry.Flat) hlev.flip inferInstance
      rw [← hkey, S'.strictTransformIdeal_zero, S.strictTransformIdeal_zero]
      exact ker_eq_comap_ker_of_isPullback_of_flat hC
  | succ n ih =>
      intro hj
      have hn : n < S'.length := Nat.lt_of_succ_le hj
      have hnle : n ≤ S'.length := Nat.le_of_lt hn
      have hσ : F.reindex n + 1 ≤ F.reindex (n + 1) := F.reindex_lt_succ n hn
      have hlen : F.reindex (n + 1) ≤ S.length := F.reindex_le_length hj
      have hIH := ih hnle
      have hcenter : S'.ambientCenter n
          = (S.ambientCenter (F.reindex n)).comap (F.levelMap n hnle) := F.center_eq n hn
      have : AlgebraicGeometry.Flat (F.levelMap n hnle) := F.flat_levelMap n hnle
      have := S.isNoetherian_schemeAt (F.reindex n + 1) (le_trans hσ hlen)
      have := S'.isNoetherian_schemeAt (n + 1) hj
      have hst := comap_strictTransform_of_flat_of_isLocallyNoetherian
        (S.blowdown (F.reindex n)) (F.levelMap n hnle) (S'.blowdown n)
        (F.levelMap (n + 1) hj ≫ S.ambientSeq.transitionMap hσ)
        (F.isPullback_step n hn hσ) (S.ambientCenter (F.reindex n))
        (S.strictTransformIdeal (F.reindex n))
        (S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism (F.reindex n) (F.reindex_lt n hn))
      have hbet : ∀ m, F.reindex n + 1 ≤ m → m < F.reindex (n + 1) →
          ∀ j', j' < S'.length → F.reindex j' ≠ m :=
        fun m h1 h2 j' hj' => F.reindex_ne_of_reindex_lt_of_lt_reindex_succ n hn m (by omega) h2 j' hj'
      have hkey := strictTransformIdeal_comap_transitionMap_eq F (n + 1) hj
        (F.reindex (n + 1) - (F.reindex n + 1)) (F.reindex n + 1) hσ (by omega) hbet
      rw [← hkey, S.strictTransformIdeal_succ (F.reindex n), hst, ← hIH, ← hcenter]
      exact S'.strictTransformIdeal_succ n

/- English proof (authored)
Each composite of the two proposed maps becomes the identity after composition with the corresponding ambient monomorphism, by the two factorization equations. Cancellation makes the two composites identities. The maps therefore form an isomorphism with the stated factorization.
-/
private theorem exists_iso_of_mono_of_comp_eq
    {A Z W : Scheme.{u}} (g : Z ⟶ A) (i : W ⟶ A)
    [CategoryTheory.Mono g] [CategoryTheory.Mono i] (a : W ⟶ Z) (b : Z ⟶ W)
    (ha : a ≫ g = i) (hb : b ≫ i = g) :
    ∃ u : W ≅ Z, u.hom ≫ g = i := by
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · refine (cancel_mono i).mp ?_
    rw [Category.assoc, hb, ha, Category.id_comp]
  · refine (cancel_mono g).mp ?_
    rw [Category.assoc, ha, hb, Category.id_comp]

/- English proof (authored)
The closed immersion and the immersion defined by its kernel have the same kernel ideal. Each therefore factors through the other by the closed-immersion lifting property. They are monomorphisms, so the two factorizations form an isomorphism over the ambient scheme.
-/
private theorem exists_iso_subscheme_ker
    {A Z : Scheme.{u}} (g : Z ⟶ A) [AlgebraicGeometry.IsClosedImmersion g] :
    ∃ u : (Scheme.Hom.ker g).subscheme ≅ Z, u.hom ≫ g = (Scheme.Hom.ker g).subschemeι := by
  have hker : Scheme.Hom.ker (Scheme.Hom.ker g).subschemeι = Scheme.Hom.ker g :=
    AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι _
  have h1 : Scheme.Hom.ker g ≤ Scheme.Hom.ker (Scheme.Hom.ker g).subschemeι :=
    le_of_eq hker.symm
  have h2 : Scheme.Hom.ker (Scheme.Hom.ker g).subschemeι ≤ Scheme.Hom.ker g := le_of_eq hker
  exact exists_iso_of_mono_of_comp_eq g (Scheme.Hom.ker g).subschemeι
    (AlgebraicGeometry.IsClosedImmersion.lift g (Scheme.Hom.ker g).subschemeι h1)
    (AlgebraicGeometry.IsClosedImmersion.lift (Scheme.Hom.ker g).subschemeι g h2)
    (AlgebraicGeometry.IsClosedImmersion.lift_fac ..)
    (AlgebraicGeometry.IsClosedImmersion.lift_fac ..)

/- English proof (authored)
The base change of the original closed immersion is itself a closed immersion. Its kernel is the specified new ideal, so the new closed subscheme is isomorphic over the new ambient scheme to this pullback. Under that isomorphism use the other projection as the comparison to the original closed subscheme. The projections commute and the square is a pullback.
-/
private theorem exists_isPullback_subscheme_of_ker_eq
    {A B : Scheme.{u}} (f : A ⟶ B) (I : B.IdealSheafData) (J : A.IdealSheafData)
    (hJ : J = Scheme.Hom.ker (pullback.fst f I.subschemeι)) :
    ∃ g : J.subscheme ⟶ I.subscheme,
      g ≫ I.subschemeι = J.subschemeι ≫ f ∧
        IsPullback g J.subschemeι I.subschemeι f := by
  subst hJ
  have : AlgebraicGeometry.IsClosedImmersion (pullback.fst f I.subschemeι) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.IsClosedImmersion)
      (IsPullback.of_hasPullback f I.subschemeι).flip inferInstance
  obtain ⟨u, hu⟩ := exists_iso_subscheme_ker (pullback.fst f I.subschemeι)
  have hfst : (u ≪≫ pullbackSymmetry f I.subschemeι).hom ≫ pullback.fst I.subschemeι f
      = u.hom ≫ pullback.snd f I.subschemeι := by
    rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
  have hsnd : (u ≪≫ pullbackSymmetry f I.subschemeι).hom ≫ pullback.snd I.subschemeι f
      = (Scheme.Hom.ker (pullback.fst f I.subschemeι)).subschemeι := by
    rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd, hu]
  have hcomm : ((u ≪≫ pullbackSymmetry f I.subschemeι).hom ≫ pullback.fst I.subschemeι f)
        ≫ I.subschemeι
      = (Scheme.Hom.ker (pullback.fst f I.subschemeι)).subschemeι ≫ f := by
    rw [hfst, Category.assoc, ← pullback.condition, ← Category.assoc, hu]
  exact ⟨(u ≪≫ pullbackSymmetry f I.subschemeι).hom ≫ pullback.fst I.subschemeι f, hcomm,
    IsPullback.of_iso_pullback ⟨hcomm⟩ (u ≪≫ pullbackSymmetry f I.subschemeι) rfl hsnd⟩

/- English proof (authored)
The new strict-transform ideal is the pullback of the original one, which is the kernel of the base-changed strict-transform immersion. Apply the closed-subscheme pullback result for equal kernels to construct the comparison and its pullback square.
-/
theorem exists_isPullback_strictTransformι (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length) :
    ∃ g : S'.strictTransform j ⟶ S.strictTransform (F.reindex j),
      g ≫ S.strictTransformι (F.reindex j) = S'.strictTransformι j ≫ F.levelMap j hj ∧
        IsPullback g (S'.strictTransformι j) (S.strictTransformι (F.reindex j)) (F.levelMap j hj) := by
  have hJ : S'.strictTransformIdeal j
      = Scheme.Hom.ker (pullback.fst (F.levelMap j hj)
          (S.strictTransformIdeal (F.reindex j)).subschemeι) := F.strictTransformIdeal_eq_comap j hj
  exact exists_isPullback_subscheme_of_ker_eq (F.levelMap j hj)
    (S.strictTransformIdeal (F.reindex j)) (S'.strictTransformIdeal j) hJ

def strictTransformComparison (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length) :
    S'.strictTransform j ⟶ S.strictTransform (F.reindex j) :=
  (F.exists_isPullback_strictTransformι j hj).choose

/- English proof (authored)
The strict-transform comparison was chosen with a commuting square of strict-transform inclusions and ambient comparison. The displayed equality is its commuting equation.
-/
theorem strictTransformComparison_comp_strictTransformι (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length) :
    F.strictTransformComparison j hj ≫ S.strictTransformι (F.reindex j) = S'.strictTransformι j ≫ F.levelMap j hj :=
  (F.exists_isPullback_strictTransformι j hj).choose_spec.1

/- English proof (authored)
The chosen strict-transform comparison exhibits the new strict transform as the pullback of the original strict-transform inclusion. Its defining property is exactly this pullback square.
-/
theorem isPullback_strictTransformComparison_strictTransformι (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length) :
    IsPullback (F.strictTransformComparison j hj) (S'.strictTransformι j) (S.strictTransformι (F.reindex j))
      (F.levelMap j hj) :=
  (F.exists_isPullback_strictTransformι j hj).choose_spec.2

/- English proof (authored)
The ambient stage comparison is flat, and the square of strict transforms identifies their comparison as its base change along the original strict-transform inclusion. This comparison is therefore flat.
-/
theorem flat_strictTransformComparison (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length) :
    AlgebraicGeometry.Flat (F.strictTransformComparison j hj) := by
  have hst : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.Flat : MorphismProperty Scheme.{u}) := inferInstance
  exact hst.of_isPullback (F.isPullback_strictTransformComparison_strictTransformι j hj).flip (F.flat_levelMap j hj)

end ChartFlatBaseChange

def chartFlatBaseChangeOfIsPullbackSeq (S : EmbeddedBlowupSequence k Y pY) (S' : EmbeddedBlowupSequence k' Y' pY')
    (f : S'.ambient ⟶ S.ambient) [AlgebraicGeometry.Flat f] (b : Y' ⟶ Y)
    (hb : IsPullback b S'.emb S.emb f)
    (hpb : IsPullbackBlowupSequence f S'.ambientSeq S.ambientSeq) :
    ChartFlatBaseChange S S' where
  ambientMap := f
  flat_ambientMap := inferInstance
  baseMap := b
  isPullback_emb := hb
  reindex := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose
  levelMap := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose
  reindex_lt := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.1
  reindex_lt_succ := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.1
  reindex_len := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.1
  isPullback_level := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.1
  isPullback_down := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.2.1
  isPullback_step :=
    (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.2.2.1
  center_eq :=
    (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.2.2.2.1
  comap_center_skipped :=
    (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.2.2.2.2

end FunctorialResolution.EmbeddedResolution

end
