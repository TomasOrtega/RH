import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ProperOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HaarUniqInfHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbMSectMul

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

/- English proof (translation)
Establish `: FiniteDimensional X.B.I.F X.B.I.E` using `fd_of X`. Establish `hdet : ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (F` using `X.B.I.F) (Ainf X.B.I.F))).det = inclR (F := X.B.I.F) (Ainf X.B.I.F) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det := by`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Establish `hsub : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {((TI X u' hT : HmI X) : Matrix _ _ _)} ⊆ IndI X`.

Introduce `y hy`. Establish `hy' : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y = ((TI X u' hT : HmI X) : Matrix _ _ _)` using `hy`. Apply `linIndep_of_isUnit_det (R := Ainf X.B.I.F) (σ := X.B.I.cm.sig) (J := X.B.I.J) y` to reduce the goal to its premises. Rewrite using `[hy']`. Use `show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (F := X.B.I.F) (Ainf X.B.I.F))).det`.

Rewrite using `[hdet]`. Conclude with `(isUnit_iff_ne_zero.2 hd).map _`. Establish `he : FbI X u' hT = gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {((TI X u' hT : HmI X) : Matrix _ _ _)}` using `Set.inter_eq_left.2 hsub`. Rewrite using `[he]`. Conclude with `isClosed_singleton.preimage (continuous_gramI X)`.
-/
theorem fbI_closed {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) : IsClosed (FbI X u' hT) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hdet : ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (F := X.B.I.F) (Ainf X.B.I.F))).det =
      inclR (F := X.B.I.F) (Ainf X.B.I.F) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det := by
    rw [RingHom.map_det]; rfl
  have hsub : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {((TI X u' hT : HmI X) : Matrix _ _ _)} ⊆ IndI X := by
    intro y hy
    have hy' : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y = ((TI X u' hT : HmI X) : Matrix _ _ _) := hy
    apply linIndep_of_isUnit_det (R := Ainf X.B.I.F) (σ := X.B.I.cm.sig) (J := X.B.I.J) y
    rw [hy']
    show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (F := X.B.I.F) (Ainf X.B.I.F))).det
    rw [hdet]
    exact (isUnit_iff_ne_zero.2 hd).map _
  have he : FbI X u' hT = gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {((TI X u' hT : HmI X) : Matrix _ _ _)} :=
    Set.inter_eq_left.2 hsub
  rw [he]
  exact isClosed_singleton.preimage (continuous_gramI X)

/- English proof (translation)
Introduce `D X u' ψ hT μinf νinf fibInf hP K hK`. Establish `: FiniteDimensional X.B.I.F X.B.I.E` using `fd_of X`. Establish `: SecondCountableTopology (GI X)` using `PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J`. Establish `: LocallyCompactSpace (GI X)` using `inferInstanceAs (LocallyCompactSpace (HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J))`. Establish `hd` using `detNZ_holds X u' ψ hT μinf νinf fibInf hP`.

Establish `horb : MulAction.orbit (GI X) (Y0 X u') = FbI X u' hT`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `orbM_mem X u' hT hd g`. Introduce `y hy`.

Take `⟨g, hg⟩` from `hW X u' ψ hT μinf νinf fibInf hP hy`. Conclude with `⟨g, hg⟩`. Establish `hcl : IsClosed (MulAction.orbit (GI X) (Y0 X u'))` using `horb ▸ fbI_closed X u' hT hd`. Establish `: LocallyCompactSpace (MulAction.orbit (GI X) (Y0 X u'))` using `hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `hjoint : Continuous (fun p : GI X × TupI X => p.1 • p.2)`.

Use `continuous_pi fun a => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun p : GI X × TupI X => ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J p.1 : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).mulVec (p.2 a)`. Conclude with `((MassDataMassesW.SplitW.continuous_matHA X.B.I.cm.sig X.B.I.J (Ainf X.B.I.F)).comp continuous_fst).matrix_mulVec ((continuous_apply a).comp continuous_snd)`. Establish `: ContinuousSMul (GI X) (MulAction.orbit (GI X) (Y0 X u'))` using `⟨continuous_induced_rng.2 (hjoint.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩`. Establish `y0O : Y0 X u' ∈ MulAction.orbit (GI X) (Y0 X u')` using `MulAction.mem_orbit_self _`.

Establish `hopen : IsOpenMap (fun g : GI X => g • (⟨Y0 X u', y0O⟩ : MulAction.orbit (GI X) (Y0 X u')))` using `isOpenMap_smul_of_sigmaCompact _`. Establish `hHc : IsCompact (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') : Set (GI X))`. Establish `: CompactSpace (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u'))` using `hH X u'`. Establish `h` using `isCompact_range (continuous_subtype_val : Continuous (Subtype.val : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') → GI X))`. Rewrite `h` using `[Subtype.range_coe]`. Then use the resulting hypothesis.

Take `⟨V, hVc, hV1⟩` from `exists_compact_mem_nhds (1 : GI X)`. Set `U : GI X → Set (MulAction.orbit (GI X) (Y0 X u'))` to `fun g => (fun h : GI X => h • (⟨Y0 X u', y0O⟩ : MulAction.orbit (GI X) (Y0 X u'))) '' ((fun h => h * g) '' interior V)`. Establish `hUo : ∀ g, IsOpen (U g)` using `fun g => hopen _ ((isOpenMap_mul_right g) _ isOpen_interior)`. Establish `hKO : IsCompact (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u')))` using `hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK`. Establish `hcov : (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u'))) ⊆ ⋃ g, U g`.

Introduce `y _`. Take `⟨g, hg⟩` from `y.2`. Use `Set.mem_iUnion.2 ⟨g, 1 * g, ⟨1, mem_interior_iff_mem_nhds.2 hV1, rfl⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (1 * g) • Y0 X u' = y.1`.

Rewrite using `[one_mul]`. Conclude with `hg`. Take `⟨t, ht⟩` from `hKO.elim_finite_subcover U hUo hcov`. Use `⟨⋃ g ∈ t, (fun p : GI X × GI X => p.1 * g * p.2) '' (V ×ˢ (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') : Set (GI X))), t.isCompact_biUnion fun g _ => (hVc.prod hHc).image ((continuous_fst.mul continuous_const).mul continuous_snd), fun g hg => ?_⟩` and prove the remaining obligations. Establish `hy : (⟨g • Y0 X u', ⟨g, rfl⟩⟩ : MulAction.orbit (GI X) (Y0 X u')) ∈ (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u')))` using `hg`.

Take `⟨g', hg't, hyU⟩` from `Set.mem_iUnion₂.1 (ht hy)`. Take `⟨_, ⟨v, hv, rfl⟩, hvg⟩` from `hyU`. Establish `hvg' : (v * g') • Y0 X u' = g • Y0 X u'` using `congrArg Subtype.val hvg`. Use `Set.mem_iUnion₂.2 ⟨g', hg't, (v, (v * g')⁻¹ * g), ⟨interior_subset hv, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show ((v * g')⁻¹ * g) ∈ Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')`.

Rewrite using `[mem_H_iff]`. Express the relevant statement in the definitionally equal form `((v * g')⁻¹ * g) • Y0 X u' = Y0 X u'`. Rewrite using `[mul_smul, ← hvg', ← mul_smul, inv_mul_cancel, one_smul]`. Conclude with `mul_inv_cancel_left (v * g') g`.
-/
theorem properOne_of (hW : WittInf) (hH : MassDataMassesW.HinfCompact) : ProperOne := by
  intro D X u' ψ hT μinf νinf fibInf hP K hK
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : SecondCountableTopology (GI X) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  have : LocallyCompactSpace (GI X) :=
    inferInstanceAs (LocallyCompactSpace (HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J))
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have horb : MulAction.orbit (GI X) (Y0 X u') = FbI X u' hT := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g, rfl⟩; exact orbM_mem X u' hT hd g
    · intro y hy
      obtain ⟨g, hg⟩ := hW X u' ψ hT μinf νinf fibInf hP hy
      exact ⟨g, hg⟩
  have hcl : IsClosed (MulAction.orbit (GI X) (Y0 X u')) := horb ▸ fbI_closed X u' hT hd
  have : LocallyCompactSpace (MulAction.orbit (GI X) (Y0 X u')) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hjoint : Continuous (fun p : GI X × TupI X => p.1 • p.2) := by
    refine continuous_pi fun a => ?_
    change Continuous fun p : GI X × TupI X =>
      ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J p.1 : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).mulVec (p.2 a)
    exact ((MassDataMassesW.SplitW.continuous_matHA X.B.I.cm.sig X.B.I.J (Ainf X.B.I.F)).comp
      continuous_fst).matrix_mulVec ((continuous_apply a).comp continuous_snd)
  have : ContinuousSMul (GI X) (MulAction.orbit (GI X) (Y0 X u')) :=
    ⟨continuous_induced_rng.2 (hjoint.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  have y0O : Y0 X u' ∈ MulAction.orbit (GI X) (Y0 X u') := MulAction.mem_orbit_self _
  have hopen : IsOpenMap (fun g : GI X => g • (⟨Y0 X u', y0O⟩ : MulAction.orbit (GI X) (Y0 X u'))) :=
    isOpenMap_smul_of_sigmaCompact _
  have hHc : IsCompact (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') : Set (GI X)) := by
    have : CompactSpace (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) := hH X u'
    have h := isCompact_range (continuous_subtype_val :
      Continuous (Subtype.val : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') → GI X))
    rwa [Subtype.range_coe] at h
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : GI X)
  let U : GI X → Set (MulAction.orbit (GI X) (Y0 X u')) := fun g =>
    (fun h : GI X => h • (⟨Y0 X u', y0O⟩ : MulAction.orbit (GI X) (Y0 X u'))) '' ((fun h => h * g) '' interior V)
  have hUo : ∀ g, IsOpen (U g) := fun g => hopen _ ((isOpenMap_mul_right g) _ isOpen_interior)
  have hKO : IsCompact (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u'))) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hcov : (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u'))) ⊆ ⋃ g, U g := by
    intro y _
    obtain ⟨g, hg⟩ := y.2
    refine Set.mem_iUnion.2 ⟨g, 1 * g, ⟨1, mem_interior_iff_mem_nhds.2 hV1, rfl⟩, ?_⟩
    apply Subtype.ext
    show (1 * g) • Y0 X u' = y.1
    rw [one_mul]; exact hg
  obtain ⟨t, ht⟩ := hKO.elim_finite_subcover U hUo hcov
  refine ⟨⋃ g ∈ t, (fun p : GI X × GI X => p.1 * g * p.2) ''
      (V ×ˢ (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') : Set (GI X))),
    t.isCompact_biUnion fun g _ => (hVc.prod hHc).image ((continuous_fst.mul continuous_const).mul continuous_snd),
    fun g hg => ?_⟩
  have hy : (⟨g • Y0 X u', ⟨g, rfl⟩⟩ : MulAction.orbit (GI X) (Y0 X u')) ∈
      (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u'))) := hg
  obtain ⟨g', hg't, hyU⟩ := Set.mem_iUnion₂.1 (ht hy)
  obtain ⟨_, ⟨v, hv, rfl⟩, hvg⟩ := hyU
  have hvg' : (v * g') • Y0 X u' = g • Y0 X u' := congrArg Subtype.val hvg
  refine Set.mem_iUnion₂.2 ⟨g', hg't, (v, (v * g')⁻¹ * g), ⟨interior_subset hv, ?_⟩, ?_⟩
  · show ((v * g')⁻¹ * g) ∈ Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')
    rw [mem_H_iff]
    change ((v * g')⁻¹ * g) • Y0 X u' = Y0 X u'
    rw [mul_smul, ← hvg', ← mul_smul, inv_mul_cancel, one_smul]
  · exact mul_inv_cancel_left (v * g') g

/- English proof (translation)
The claim follows from `constTest_of_polar_one hP (properOne_of hW hH) hI`.
-/
theorem constTest_of_polar_witt (hP : PolarLoc) (hW : WittInf) (hH : MassDataMassesW.HinfCompact) (hI : InvNbhd) :
    ConstTest :=
  constTest_of_polar_one hP (properOne_of hW hH) hI

end PI.AprimeInfW
