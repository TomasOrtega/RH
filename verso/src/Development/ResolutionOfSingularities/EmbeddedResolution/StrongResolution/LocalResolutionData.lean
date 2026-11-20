import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

section

variable {X : Scheme.{u}}

def SequenceOfBlowups.schemeAtIsoOfEq (s : SequenceOfBlowups X) {i j : ℕ} (h : i = j) : s.schemeAt i ≅ s.schemeAt j :=
  eqToIso (congrArg s.schemeAt h)

/- English proof (authored)
Identify the two equal stage indices. The induced isomorphism is the identity at that stage, so composing its forward map with the projection to the base leaves the projection unchanged.
-/
theorem SequenceOfBlowups.schemeAtIsoOfEq_hom_projectionToBase (s : SequenceOfBlowups X) {i j : ℕ} (h : i = j) :
    (s.schemeAtIsoOfEq h).hom ≫ s.projectionToBase j = s.projectionToBase i := by
  subst h
  simp [SequenceOfBlowups.schemeAtIsoOfEq]

end

structure BlowupSequencePullbackComparison {S T : Scheme.{u}} (φ : T ⟶ S) (s' : SequenceOfBlowups T)
    (s : SequenceOfBlowups S) where
  reindex : ℕ → ℕ
  iso : ∀ i : ℕ, i ≤ s'.length →
    (s'.schemeAt i ≅ (pullback φ (s.projectionToBase (reindex i)) : Scheme.{u}))
  reindex_length : reindex s'.length = s.length
  retention : ∀ i : ℕ, i < s.length →
    ((∃ j : ℕ, ∃ _ : j < s'.length, reindex j = i) ↔
      ∃ x, x ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support)
  iso_hom_fst : ∀ (i : ℕ) (h : i ≤ s'.length),
    (iso i h).hom ≫ pullback.fst φ (s.projectionToBase (reindex i)) = s'.projectionToBase i
  center_eq : ∀ (i : ℕ) (h : i < s'.length),
    s'.center i =
      (s.center (reindex i)).comap
        ((iso i h.le).hom ≫ pullback.snd φ (s.projectionToBase (reindex i)))

/- English proof (authored)
The pullback-sequence condition supplies the reindexing, the isomorphisms from local stages to global pullbacks, and the final-index, projection, and center compatibilities. Its criterion for retaining a step says exactly that the restricted center has a point, after writing membership in its support as an existential statement. Use these data to form a pullback comparison.
-/
theorem nonempty_pullbackComparison_of_isPullback {S T : Scheme.{u}} (φ : T ⟶ S) (s' : SequenceOfBlowups T)
    (s : SequenceOfBlowups S) (h : IsPullbackBlowupSequence φ s' s) : Nonempty (BlowupSequencePullbackComparison φ s' s) := by
  unfold IsPullbackBlowupSequence at h
  obtain ⟨r, e, hlt, hmono, hlen, hret, hfst, hblow, hcen⟩ := h
  have hret' : ∀ i : ℕ, i < s.length →
      ((∃ j : ℕ, ∃ _ : j < s'.length, r j = i) ↔
        ∃ x, x ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support) := by
    intro i hi
    refine ⟨fun hj => (hret i hi).2 ?_, fun hx => ?_⟩
    · obtain ⟨j, hj1, hj2⟩ := hj
      exact ⟨j, hj1, hj2⟩
    · obtain ⟨j, hj1, hj2⟩ := (hret i hi).1 hx
      exact ⟨j, hj1, hj2⟩
  exact ⟨⟨r, e, hlen, hret', hfst, hcen⟩⟩

structure LocalResolutionData (k : Type u) [instFieldk : Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (s : SequenceOfBlowups X) where
  cover : Scheme.OpenCover.{u, u} X
  seq : ∀ i : cover.I₀, SequenceOfBlowups (cover.X i)
  isPullback : ∀ i : cover.I₀, IsPullbackBlowupSequence (cover.f i) (seq i) s
  finiteType : ∀ i : cover.I₀, LocallyOfFiniteType (cover.f i ≫ f)
  isResolution : ∀ i : cover.I₀,
    @IsStrongResolution k instFieldk (cover.X i) (cover.f i ≫ f) (finiteType i) (seq i)

attribute [instance] LocalResolutionData.finiteType

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

def comparison (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    BlowupSequencePullbackComparison (d.cover.f i) (d.seq i) s :=
  (nonempty_pullbackComparison_of_isPullback (d.cover.f i) (d.seq i) s (d.isPullback i)).some

def reindex (d : LocalResolutionData k f s) (i : d.cover.I₀) : ℕ → ℕ := (d.comparison i).reindex

def schemeAtIsoPullback (d : LocalResolutionData k f s) (i : d.cover.I₀) (j : ℕ) (hj : j ≤ (d.seq i).length) :
    ((d.seq i).schemeAt j ≅ (pullback (d.cover.f i) (s.projectionToBase (d.reindex i j)) : Scheme.{u})) :=
  (d.comparison i).iso j hj

/- English proof (authored)
The chosen pullback comparison requires the final stage of the local sequence to reindex to the final stage of the global sequence.
-/
theorem reindex_length (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    d.reindex i (d.seq i).length = s.length :=
  (d.comparison i).reindex_length

/- English proof (authored)
The stage comparison identifies the map from the local stage to its own base with the first projection from the corresponding global pullback. Applying this condition at the specified stage gives the formula.
-/
theorem schemeAtIsoPullback_hom_fst (d : LocalResolutionData k f s) (i : d.cover.I₀) (j : ℕ)
    (hj : j ≤ (d.seq i).length) :
    (d.schemeAtIsoPullback i j hj).hom ≫ pullback.fst (d.cover.f i) (s.projectionToBase (d.reindex i j))
      = (d.seq i).projectionToBase j :=
  (d.comparison i).iso_hom_fst j hj

/- English proof (authored)
At a local blowup step, the comparison defines its center as the pullback of the corresponding global center along the map from the local stage to the global stage. This map is the stage isomorphism followed by the second pullback projection.
-/
theorem localSequence_center_eq_comap (d : LocalResolutionData k f s) (i : d.cover.I₀) (j : ℕ)
    (hj : j < (d.seq i).length) :
    (d.seq i).center j =
      (s.center (d.reindex i j)).comap
        ((d.schemeAtIsoPullback i j hj.le).hom ≫
          pullback.snd (d.cover.f i) (s.projectionToBase (d.reindex i j))) :=
  (d.comparison i).center_eq j hj

/- English proof (authored)
The global step is retained on the chosen chart exactly when its pulled-back center there has nonempty support. This is the retention condition in the comparison data.
-/
theorem exists_reindex_eq_iff_exists_mem_support (d : LocalResolutionData k f s) (i : d.cover.I₀) (j : ℕ) (hj : j < s.length) :
    ((∃ l : ℕ, ∃ _ : l < (d.seq i).length, d.reindex i l = j) ↔
      ∃ x, x ∈ ((s.center j).comap (pullback.snd (d.cover.f i) (s.projectionToBase j))).support) :=
  (d.comparison i).retention j hj

/- English proof (authored)
The final local stage reindexes to the final global stage. The projection of that stage to the base is the global final structural map. Substituting these two equalities identifies the pullback objects.
-/
theorem pullback_projectionToBase_eq_pullback_lastStructMap (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    (pullback (d.cover.f i) (s.projectionToBase (d.reindex i (d.seq i).length)) : Scheme.{u})
      = (pullback (d.cover.f i) s.lastStructMap : Scheme.{u}) := by
  have h1 : (pullback (d.cover.f i) (s.projectionToBase (d.reindex i (d.seq i).length)) : Scheme.{u})
      = (pullback (d.cover.f i) (s.projectionToBase s.length) : Scheme.{u}) :=
    congrArg (fun n : ℕ => (pullback (d.cover.f i) (s.projectionToBase n) : Scheme.{u}))
      (d.reindex_length i)
  have h2 : (pullback (d.cover.f i) (s.projectionToBase s.length) : Scheme.{u})
      = (pullback (d.cover.f i) s.lastStructMap : Scheme.{u}) :=
    congrArg (fun g : s.lastObj ⟶ X => (pullback (d.cover.f i) g : Scheme.{u}))
      s.lastStructMap_eq_projectionToBase.symm
  exact h1.trans h2

def lastObjIsoPullback (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    ((d.seq i).lastObj ≅ (pullback (d.cover.f i) s.lastStructMap : Scheme.{u})) :=
  (d.schemeAtIsoPullback i (d.seq i).length le_rfl).trans (eqToIso (d.pullback_projectionToBase_eq_pullback_lastStructMap i))

/- English proof (authored)
Identify the equal second objects. The compatibility of the second morphisms then identifies those morphisms as well. The pullbacks and their first projections are now identical, and transport along the pullback equality is the identity.
-/
private theorem eqToHom_comp_pullback_fst {X₀ X₁ Y₀ Y₁ : Scheme.{u}} (φ : X₁ ⟶ X₀)
    {g : Y₀ ⟶ X₀} {g' : Y₁ ⟶ X₀} (hY : Y₀ = Y₁) (hg : eqToHom hY ≫ g' = g)
    (e : (pullback φ g : Scheme.{u}) = (pullback φ g' : Scheme.{u})) :
    eqToHom e ≫ pullback.fst φ g' = pullback.fst φ g := by
  subst hY
  simp only [eqToHom_refl, Category.id_comp] at hg
  subst hg
  simp

/- English proof (authored)
The point map of the composite applies the first point map followed by the second.
-/
private theorem base_comp_apply {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (t : ↥A) :
    (a ≫ b).base t = b.base (a.base t) := by
  simp

/- English proof (authored)
The final comparison isomorphism is the stage comparison at the last local stage followed by transport to the pullback of the final global morphism. This transport carries the first projection to the corresponding stage pullback projection. By stage compatibility, the composite with that projection is the local projection to the base at its final stage, namely the local final structural map.
-/
theorem lastObjIsoPullback_hom_fst (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    (d.lastObjIsoPullback i).hom ≫ pullback.fst (d.cover.f i) s.lastStructMap = (d.seq i).lastStructMap := by
  have hg : eqToHom (congrArg s.schemeAt (d.reindex_length i)) ≫ s.lastStructMap
      = s.projectionToBase (d.reindex i (d.seq i).length) := by
    rw [s.lastStructMap_eq_projectionToBase]
    exact s.schemeAtIsoOfEq_hom_projectionToBase (d.reindex_length i)
  have key := eqToHom_comp_pullback_fst (d.cover.f i)
    (congrArg s.schemeAt (d.reindex_length i)) hg (d.pullback_projectionToBase_eq_pullback_lastStructMap i)
  have e1 : (d.lastObjIsoPullback i).hom
      = (d.schemeAtIsoPullback i (d.seq i).length le_rfl).hom ≫ eqToHom (d.pullback_projectionToBase_eq_pullback_lastStructMap i) := rfl
  rw [e1, Category.assoc, key, d.schemeAtIsoPullback_hom_fst i (d.seq i).length le_rfl,
    (d.seq i).lastStructMap_eq_projectionToBase]

def chartToLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) : (d.seq i).lastObj ⟶ s.lastObj :=
  (d.lastObjIsoPullback i).hom ≫ pullback.snd (d.cover.f i) s.lastStructMap

/- English proof (authored)
The final chart map is defined by the isomorphism from the local final object to the pullback, followed by projection to the global final object.
-/
theorem chartToLastObj_eq (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    d.chartToLastObj i = (d.lastObjIsoPullback i).hom ≫ pullback.snd (d.cover.f i) s.lastStructMap :=
  rfl

/- English proof (authored)
The projection from the pullback to the final global scheme is the base change of an open immersion from the given base chart. It is an open immersion. Precomposing it with the final comparison isomorphism preserves this property.
-/
theorem isOpenImmersion_chartToLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsOpenImmersion (d.chartToLastObj i) := by
  have : IsOpenImmersion (d.cover.f i) := d.cover.map_prop i
  rw [d.chartToLastObj_eq i]
  infer_instance

instance instIsOpenImmersionChartEmbedding (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsOpenImmersion (d.chartToLastObj i) :=
  d.isOpenImmersion_chartToLastObj i

/- English proof (authored)
The two composites from the pullback to the global base agree by the pullback square. The first projection after the local comparison isomorphism is the local structural map, and the second projection after it is the chart map. Substitute these descriptions.
-/
theorem chartToLastObj_comp_lastStructMap (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    d.chartToLastObj i ≫ s.lastStructMap = (d.seq i).lastStructMap ≫ d.cover.f i := by
  rw [d.chartToLastObj_eq i, Category.assoc, ← pullback.condition, ← Category.assoc,
    d.lastObjIsoPullback_hom_fst i]

/- English proof (authored)
Choose a base chart point above the image of the given point of the final global scheme. Together the two points give a point of the pullback over the base. Transport it back to the final local object through the comparison isomorphism. Its chart image is the second projection of that pullback point, which is the given global point.
-/
theorem exists_chartToLastObj_eq (d : LocalResolutionData k f s) (x : ↥(s.lastObj)) :
    ∃ (i : d.cover.I₀) (y : ↥((d.seq i).lastObj)), (d.chartToLastObj i).base y = x := by
  obtain ⟨w, hw⟩ := d.cover.covers (s.lastStructMap.base x)
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback w x hw
  refine ⟨d.cover.idx (s.lastStructMap.base x), (d.lastObjIsoPullback _).inv.base p, ?_⟩
  have h2 : (d.lastObjIsoPullback (d.cover.idx (s.lastStructMap.base x))).inv ≫
      d.chartToLastObj (d.cover.idx (s.lastStructMap.base x))
      = pullback.snd (d.cover.f (d.cover.idx (s.lastStructMap.base x))) s.lastStructMap := by
    rw [d.chartToLastObj_eq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h3 := congrArg
    (fun m : (pullback (d.cover.f (d.cover.idx (s.lastStructMap.base x))) s.lastStructMap : Scheme.{u}) ⟶ s.lastObj
      => m.base p) h2
  simp only [base_comp_apply] at h3
  exact h3.trans hp2

/- English proof (authored)
For each point, use the existence of a preimage in one of the final local objects. The action of the chart morphism on that point is its underlying point map, so the resulting equality is the one required.
-/
private theorem exists_chartToLastObj_apply_eq (d : LocalResolutionData k f s) :
    ∀ x : ↥(s.lastObj), ∃ (i : d.cover.I₀) (y : ↥((d.seq i).lastObj)), (d.chartToLastObj i) y = x :=
  fun x => d.exists_chartToLastObj_eq x

def lastObjCover (d : LocalResolutionData k f s) : Scheme.OpenCover.{u, u} s.lastObj :=
  Scheme.Cover.mkOfCovers d.cover.I₀ (fun i => (d.seq i).lastObj)
    (fun i => d.chartToLastObj i) d.exists_chartToLastObj_apply_eq
    (fun i => d.isOpenImmersion_chartToLastObj i)

/- English proof (authored)
The base chart map is an open immersion. At each chart point, its open neighborhood identifies with an open neighborhood in the original scheme, so smoothness of the composite to the field is equivalent to smoothness of the original map at the image. Thus the local smooth locus is the inverse image of the global one.
-/
theorem preimage_smoothLocus_cover_map (d : LocalResolutionData k f s) (i : d.cover.I₀)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)] :
    (d.cover.f i) ⁻¹ᵁ f.smoothLocus = (d.cover.f i ≫ f).smoothLocus := by
  have : IsOpenImmersion (d.cover.f i) := d.cover.map_prop i
  exact Scheme.Hom.preimage_smoothLocus_eq _ _

/- English proof (authored)
The smooth-locus formula identifies the inverse image of the global smooth locus with the local smooth locus. Inverse image commutes with complement, which gives the formula for their complements.
-/
theorem preimage_smoothLocusComplement_cover_map (d : LocalResolutionData k f s) (i : d.cover.I₀)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)] :
    (d.cover.f i).base ⁻¹' ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X)
      = ((smoothLocusComplement (d.cover.f i ≫ f) :
          TopologicalSpace.Closeds ↥(d.cover.X i)) : Set ↥(d.cover.X i)) := by
  have h : ((d.cover.f i).base ⁻¹' (f.smoothLocus : Set ↥X))
      = ((d.cover.f i ≫ f).smoothLocus : Set ↥(d.cover.X i)) :=
    congrArg (fun U : TopologicalSpace.Opens ↥(d.cover.X i) => (U : Set ↥(d.cover.X i)))
      (d.preimage_smoothLocus_cover_map i)
  show (d.cover.f i).base ⁻¹' ((f.smoothLocus : Set ↥X))ᶜ
      = ((d.cover.f i ≫ f).smoothLocus : Set ↥(d.cover.X i))ᶜ
  rw [Set.preimage_compl, h]

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
