import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBPullIsoOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubsingletonOfPoints
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankMumfordBundleCechHomologyOriginStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.MumfordCohom

/- English proof (translation)
Take `⟨_, ⟨V₀, hV₀, rfl⟩, hoV, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ o) isOpen_univ`. Establish `hc : IsCompact (V₀ : Set X)ᶜ` using `V₀.isOpen.isClosed_compl.isCompact`. Take `⟨s, hs⟩` from `hc.elim_finite_subcover (fun W : {W : X.Opens // IsAffineOpen W ∧ o ∉ W} => (W.1 : Set X)) (fun W => W.1.isOpen) (by`. Introduce `x hx`. Establish `hx' : x ∈ ({o} : Set X)ᶜ`.

Introduce and unpack `rfl`. Conclude with `hx hoV`. Take `⟨_, ⟨W, hW, rfl⟩, hxW, hWo⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open hx' ho.isOpen_compl`. Conclude with `Set.mem_iUnion.2 ⟨⟨W, hW, fun h => hWo h rfl⟩, hxW⟩)`. Use `⟨s.card, Fin.cons V₀ fun j => (s.equivFin.symm j).1.1, fun j => ?_, ?_, hoV, fun j hj => ?_⟩` and prove the remaining obligations.

Use `Fin.cases hV₀ (fun j => ?_) j` and prove the remaining obligations. Conclude with `(s.equivFin.symm j).1.2.1`. Use `top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ V₀`. Conclude with `⟨0, hx⟩`.

Take `⟨W, hW, hxW⟩` from `Set.mem_iUnion₂.1 (hs hx)`. Use `⟨(s.equivFin ⟨W, hW⟩).succ, ?_⟩` and prove the remaining obligations. Simplify using `using hxW`. Take `⟨j, rfl⟩` from `Fin.exists_succ_eq.2 hj`. Conclude with `(s.equivFin.symm j).1.2.2`.
-/
theorem exists_cover_point (X : Scheme.{0}) [CompactSpace X] (o : X) (ho : IsClosed {o}) :
    ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens), (∀ j, IsAffineOpen (V j)) ∧ ⨆ j, V j = ⊤ ∧
      o ∈ V 0 ∧ ∀ j, j ≠ 0 → o ∉ V j := by
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hoV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ o) isOpen_univ
  have hc : IsCompact (V₀ : Set X)ᶜ := V₀.isOpen.isClosed_compl.isCompact
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover
    (fun W : {W : X.Opens // IsAffineOpen W ∧ o ∉ W} => (W.1 : Set X)) (fun W => W.1.isOpen) (by
      intro x hx
      have hx' : x ∈ ({o} : Set X)ᶜ := by
        rintro rfl
        exact hx hoV
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWo⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx' ho.isOpen_compl
      exact Set.mem_iUnion.2 ⟨⟨W, hW, fun h => hWo h rfl⟩, hxW⟩)
  refine ⟨s.card, Fin.cons V₀ fun j => (s.equivFin.symm j).1.1, fun j => ?_, ?_, hoV, fun j hj => ?_⟩
  · refine Fin.cases hV₀ (fun j => ?_) j
    exact (s.equivFin.symm j).1.2.1
  · refine top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    by_cases hx : x ∈ V₀
    · exact ⟨0, hx⟩
    · obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.1 (hs hx)
      refine ⟨(s.equivFin ⟨W, hW⟩).succ, ?_⟩
      simpa using hxW
  · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hj
    exact (s.equivFin.symm j).1.2.2

/- English proof (translation)
Establish `: IsAffine V` using `hV`. Establish `: IsAffineHom (V.ι ≫ g)` using `haveI : IsAffineHom ((V.ι ≫ g) ≫ terminal.from X) := inferInstance IsAffineHom.of_comp _ (terminal.from X)`. Establish `h` using `(hD.preimage (V.ι ≫ g)).image_of_isOpenImmersion V.ι`. Rewrite `h` using `[Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]`. Then use the resulting hypothesis.
-/
theorem isAffineOpen_preimage_inf {X Y : Scheme.{0}} [X.IsSeparated] (g : Y ⟶ X) {D : X.Opens}
    (hD : IsAffineOpen D) {V : Y.Opens} (hV : IsAffineOpen V) : IsAffineOpen (g ⁻¹ᵁ D ⊓ V) := by
  have : IsAffine V := hV
  have : IsAffineHom (V.ι ≫ g) :=
    haveI : IsAffineHom ((V.ι ≫ g) ≫ terminal.from X) := inferInstance
    IsAffineHom.of_comp _ (terminal.from X)
  have h := (hD.preimage (V.ι ≫ g)).image_of_isOpenImmersion V.ι
  rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_comm] at h

/- English proof (translation)
Establish `e (p : ℕ) : (Cube.d (secCube f' M D) p : Cube.Term (secCube f' M D) p → _) = (Cube.d (secCube f M D) p : Cube.Term (secCube f M D) p → _)`. Use function extensionality and compare the values at `fun x => funext fun t => (Cube.d_apply (secCube f' M D) p x t).trans (Cube.d_apply (secCube f M D) p x t).symm`. Introduce `n`. Consider the cases of `n with`. Consider the case `zero`.

Establish `h₀` using `h 0`. Rewrite `h₀`, the goal using `[cochainComplex_exactAt_zero_iff, cechLB_d _ _ _ 0]`. Conclude with `(e 1).symm ▸ h₀`. Consider the case `succ n`. Establish `h₀` using `(cechComplex_exactAt_succ_iff (secCube f M D) n).1 (h (n + 1))`.

Use `(cechComplex_exactAt_succ_iff (secCube f' M D) n).2 ?_` and prove the remaining obligations. Rewrite using `[e, e]`. Conclude with `h₀`.
-/
theorem acyclic_cechLB_of_acyclic {R R' : Type} [CommRing R] [CommRing R'] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of R)) (f' : Y ⟶ Spec (CommRingCat.of R')) (M : LB Y) {κ : Type}
    [LinearOrder κ] (D : κ → Y.Opens) (h : (cechLB f M D).Acyclic) : (cechLB f' M D).Acyclic := by
  have e (p : ℕ) : (Cube.d (secCube f' M D) p : Cube.Term (secCube f' M D) p → _) =
      (Cube.d (secCube f M D) p : Cube.Term (secCube f M D) p → _) :=
    funext fun x => funext fun t => (Cube.d_apply (secCube f' M D) p x t).trans
      (Cube.d_apply (secCube f M D) p x t).symm
  intro n
  cases n with
  | zero =>
    have h₀ := h 0
    rw [cochainComplex_exactAt_zero_iff, cechLB_d _ _ _ 0] at h₀ ⊢
    exact (e 1).symm ▸ h₀
  | succ n =>
    have h₀ := (cechComplex_exactAt_succ_iff (secCube f M D) n).1 (h (n + 1))
    refine (cechComplex_exactAt_succ_iff (secCube f' M D) n).2 ?_
    rw [e, e]
    exact h₀

/- English proof (translation)
Substitute `hO` using the available equality. Establish `h₁ (s : Finset κ₁) : ⨅ u ∈ Cube.sumVertex s T, Sum.elim U W (ofLex u) ≤ ⨅ i ∈ s, (U i ⊓ ⨅ j ∈ T, W j)` using `le_iInf₂ fun i hi => le_inf (biInf_le (fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)) (Cube.inl_mem_sumVertex.2 hi)) (le_iInf₂ fun j hj => biInf_le (fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)) (Cube.inr_mem_sumVertex.2 hj))`. Establish `h₂ (s : Finset κ₁) (hs : s.Nonempty) : ⨅ i ∈ s, (U i ⊓ ⨅ j ∈ T, W j) ≤ ⨅ u ∈ Cube.sumVertex s T, Sum.elim U W (ofLex u)`. Use `le_iInf₂ fun u hu => ?_` and prove the remaining obligations. Break down `u with i | j` into its components or cases.

Conclude with `(biInf_le (fun i => U i ⊓ ⨅ j ∈ T, W j) (Cube.inl_mem_sumVertex.1 hu)).trans inf_le_left`. Take `⟨i, hi⟩` from `hs`. Conclude with `(biInf_le (fun i => U i ⊓ ⨅ j ∈ T, W j) hi).trans (inf_le_right.trans (biInf_le W (Cube.inr_mem_sumVertex.1 hu)))`. Set `φ : secCube f M (fun i => U i ⊓ ⨅ j ∈ T, W j) ⟶ Cube.sliceFst (secCube f M fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)) T` to `Cube.homMk (fun s => SecOnR.restrict f M (h₁ s)) fun {s t} _ x => (SecOnR.restrict_restrict f _ (h₁ t) x).trans (SecOnR.restrict_restrict f (h₁ s) _ x).symm`. Conclude with `⟨@asIso _ _ _ _ (cechComplexMap φ) (isIso_cechComplexMap φ fun s hs => SecOnR.restrict_bijective f (h₁ s) (h₂ s hs))⟩`.
-/
theorem nonempty_cech_sliceFst_iso {R : Type} [CommRing R] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) {κ₁ κ₂ : Type} [LinearOrder κ₁] [LinearOrder κ₂]
    (U : κ₁ → Y.Opens) (W : κ₂ → Y.Opens) (T : Finset κ₂) (O : Y.Opens) (hO : O = ⨅ j ∈ T, W j) :
    Nonempty (cechLB f M (fun i => U i ⊓ O) ≅ cechComplex (Cube.sliceFst
      (secCube f M fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)) T)) := by
  subst hO
  have h₁ (s : Finset κ₁) : ⨅ u ∈ Cube.sumVertex s T, Sum.elim U W (ofLex u) ≤
      ⨅ i ∈ s, (U i ⊓ ⨅ j ∈ T, W j) :=
    le_iInf₂ fun i hi => le_inf
      (biInf_le (fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)) (Cube.inl_mem_sumVertex.2 hi))
      (le_iInf₂ fun j hj =>
        biInf_le (fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)) (Cube.inr_mem_sumVertex.2 hj))
  have h₂ (s : Finset κ₁) (hs : s.Nonempty) : ⨅ i ∈ s, (U i ⊓ ⨅ j ∈ T, W j) ≤
      ⨅ u ∈ Cube.sumVertex s T, Sum.elim U W (ofLex u) := by
    refine le_iInf₂ fun u hu => ?_
    rcases u with i | j
    · exact (biInf_le (fun i => U i ⊓ ⨅ j ∈ T, W j) (Cube.inl_mem_sumVertex.1 hu)).trans inf_le_left
    · obtain ⟨i, hi⟩ := hs
      exact (biInf_le (fun i => U i ⊓ ⨅ j ∈ T, W j) hi).trans
        (inf_le_right.trans (biInf_le W (Cube.inr_mem_sumVertex.1 hu)))
  let φ : secCube f M (fun i => U i ⊓ ⨅ j ∈ T, W j) ⟶ Cube.sliceFst
      (secCube f M fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)) T :=
    Cube.homMk (fun s => SecOnR.restrict f M (h₁ s)) fun {s t} _ x =>
      (SecOnR.restrict_restrict f _ (h₁ t) x).trans (SecOnR.restrict_restrict f (h₁ s) _ x).symm
  exact ⟨@asIso _ _ _ _ (cechComplexMap φ) (isIso_cechComplexMap φ fun s hs =>
    SecOnR.restrict_bijective f (h₁ s) (h₂ s hs))⟩

variable {K : Type} [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K)))

/- English proof (translation)
Set `π` to `pullback.fst (fst P.A P.A).left hV.fromSpec`. Set `f` to `pullback.snd (fst P.A P.A).left hV.fromSpec`. Establish `H : IsPullback π f (fst P.A P.A).left hV.fromSpec` using `IsPullback.of_hasPullback _ _`. Establish `H'` using `((AbProj.abelian_projective_baseChange K P).2 Γ(P.A.left, V) hV.fromSpec _ π f H).2.2.2.2.2`. Establish `hq : IsAffineHom (π ≫ (snd P.A P.A).left)` using `MorphismProperty.of_isPullback (P := @IsAffineHom) H'.flip inferInstance`.

Establish `hr : π.opensRange = (fst P.A P.A).left ⁻¹ᵁ V` using `by ext1`. Rewrite using `[Scheme.Hom.coe_opensRange]`. Use `erw [Scheme.Pullback.range_fst]`. Rewrite using `[hV.range_fromSpec]`. Both sides reduce to the same expression.

Establish `hE (i : κ) : π ⁻¹ᵁ ((snd P.A P.A).left ⁻¹ᵁ D i ⊓ (fst P.A P.A).left ⁻¹ᵁ V) = (π ≫ (snd P.A P.A).left) ⁻¹ᵁ D i`. Rewrite using `[← hr, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq, Scheme.Hom.comp_preimage]`. Establish `hA (i : κ) : IsAffineOpen ((π ≫ (snd P.A P.A).left) ⁻¹ᵁ D i)` using `(hD i).preimage _`. Use `⟨fun i => ?_, _, π, f, fun i => π ⁻¹ᵁ ((snd P.A P.A).left ⁻¹ᵁ D i ⊓ (fst P.A P.A).left ⁻¹ᵁ V), H, fun i => (congrArg IsAffineOpen (hE i)).mpr (hA i), ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `(hA i).image_of_isOpenImmersion π`.

Rewrite `h` using `[Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hr, inf_comm]`. Then use the resulting hypothesis. Simplify using `only [hE]`. Rewrite using `[← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]`. Establish `e : f ≫ hV.fromSpec ≫ P.A.hom = π ≫ (P.A ⊗ P.A).hom`. Rewrite using `[← H.w_assoc, Over.w (fst P.A P.A)]`.

Rewrite using `[e]`. Conclude with `cechLB_pull_iso_of_isOpenImmersion K _ _ M _ π κ _ hM fun i => hr ▸ inf_le_right`.
-/
theorem over_affineOpen {V : P.A.left.Opens} (hV : IsAffineOpen V) {κ : Type} [LinearOrder κ]
    [Fintype κ] (D : κ → P.A.left.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (M : LB (P.A ⊗ P.A).left) (hM : M.IsLB) :
    (∀ i, IsAffineOpen ((snd P.A P.A).left ⁻¹ᵁ D i ⊓ (fst P.A P.A).left ⁻¹ᵁ V)) ∧
    ∃ (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec Γ(P.A.left, V)) (E : κ → Y.Opens),
      IsPullback π f (fst P.A P.A).left hV.fromSpec ∧ (∀ i, IsAffineOpen (E i)) ∧ ⨆ i, E i = ⊤ ∧
      Nonempty (cechLB (f ≫ hV.fromSpec ≫ P.A.hom) (M.pull π) E ≅ cechLB (P.A ⊗ P.A).hom M
        fun i => (snd P.A P.A).left ⁻¹ᵁ D i ⊓ (fst P.A P.A).left ⁻¹ᵁ V) := by
  let π := pullback.fst (fst P.A P.A).left hV.fromSpec
  let f := pullback.snd (fst P.A P.A).left hV.fromSpec
  have H : IsPullback π f (fst P.A P.A).left hV.fromSpec := IsPullback.of_hasPullback _ _
  have H' := ((AbProj.abelian_projective_baseChange K P).2 Γ(P.A.left, V) hV.fromSpec _ π f H).2.2.2.2.2
  have hq : IsAffineHom (π ≫ (snd P.A P.A).left) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) H'.flip inferInstance
  have hr : π.opensRange = (fst P.A P.A).left ⁻¹ᵁ V := by
    ext1
    rw [Scheme.Hom.coe_opensRange]
    erw [Scheme.Pullback.range_fst]
    rw [hV.range_fromSpec]
    rfl
  have hE (i : κ) : π ⁻¹ᵁ ((snd P.A P.A).left ⁻¹ᵁ D i ⊓ (fst P.A P.A).left ⁻¹ᵁ V) =
      (π ≫ (snd P.A P.A).left) ⁻¹ᵁ D i := by
    rw [← hr, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq,
      Scheme.Hom.comp_preimage]
  have hA (i : κ) : IsAffineOpen ((π ≫ (snd P.A P.A).left) ⁻¹ᵁ D i) := (hD i).preimage _
  refine ⟨fun i => ?_, _, π, f,
    fun i => π ⁻¹ᵁ ((snd P.A P.A).left ⁻¹ᵁ D i ⊓ (fst P.A P.A).left ⁻¹ᵁ V), H,
    fun i => (congrArg IsAffineOpen (hE i)).mpr (hA i), ?_, ?_⟩
  · have h := (hA i).image_of_isOpenImmersion π
    rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hr, inf_comm] at h
  · simp only [hE]
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  · have e : f ≫ hV.fromSpec ≫ P.A.hom = π ≫ (P.A ⊗ P.A).hom := by
      rw [← H.w_assoc, Over.w (fst P.A P.A)]
    rw [e]
    exact cechLB_pull_iso_of_isOpenImmersion K _ _ M _ π κ _ hM fun i => hr ▸ inf_le_right

/- English proof (translation)
Introduce `K _ _ P κ _ _ D hD hc n`. Take `⟨B, hB, hBc⟩` from `AffineCover.exists_cover forall_geometricallyIntegral_of_smooth_of_geometricallyConnected trdeg_eq_of_smoothOfRelativeDimension K P`. Establish `hsep : IsSeparated P.A.hom` using `(AbProj.abelian_projective_baseChange K P).1.2`. Establish `hpr : IsProper P.A.hom` using `P.isAb.proper`. Establish `: P.A.left.IsSeparated` using `⟨by`.

Rewrite using `[← terminal.comp_from P.A.hom]`. Use the proof step `infer_instance⟩`. Establish `: CompactSpace P.A.left` using `QuasiCompact.compactSpace_of_compactSpace P.A.hom`. Set `q₀ : (𝟙_ (Over (Spec (CommRingCat.of K)))).left` to `IsLocalRing.closedPoint K`. Establish `hq (q : (𝟙_ (Over (Spec (CommRingCat.of K)))).left) : q = q₀` using `Subsingleton.elim (α := PrimeSpectrum K) _ _`.

Establish `ho : IsClosed {η[P.A].left q₀}`. Rewrite using `[← Set.image_singleton]`. Use `η[P.A].left.isClosedEmbedding.isClosedMap _ ?_` and prove the remaining obligations. Rewrite using `[show ({q₀} : Set _) = Set.univ from Set.eq_univ_of_forall hq]`. Conclude with `isClosed_univ`.

Take `⟨r, V, hV, hVc, hV₀, hV₁⟩` from `exists_cover_point P.A.left _ ho`. Establish `hM : (translDiff P.A P.L (𝟙 P.A)).IsLB` using `LB.isLB_linComb P.isLB _ _`. Establish `hsep' : IsSeparated (P.A ⊗ P.A).hom`. Rewrite using `[← Over.w (fst P.A P.A)]`. Establish `: IsSeparated (fst P.A P.A).left` using `inferInstanceAs (IsSeparated (pullback.fst P.A.hom P.A.hom))`.

Use `infer_instance`. Take `⟨e₁⟩` from `cechLB_homology_equiv_trunc₂ K _ (P.A ⊗ P.A).hom _ κ D _ (fun i => (snd P.A P.A).left ⁻¹ᵁ B i) _ (fun j => (fst P.A P.A).left ⁻¹ᵁ V j) hM hsep' hD hc (by rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top]) (by rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_to …`. Establish `e₂` using `trunc₂HomologyIsoFstSingleton (0 : Fin (r + 1)) (secCube (P.A ⊗ P.A).hom (translDiff P.A P.L (𝟙 P.A)) fun u : Fin (P.g + 1) ⊕ₗ Fin (r + 1) => Sum.elim (fun i => (snd P.A P.A).left ⁻¹ᵁ B i) (fun j => (fst P.A P.A).left ⁻¹ᵁ V j) (ofLex u)) (fun t ht ht' => by`. Establish `hVt : IsAffineOpen (⨅ j ∈ t, V j)` using `IsAffineOpen.biInf _ t.finite_toSet ht fun j _ => hV j`. Take `⟨j, hj, hj₀⟩ : ∃ j ∈ t, j ≠ 0` from `by by_contra! h`.

Conclude with `ht' (Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨ht, h⟩)`. Take `⟨-, Y, π, f, E, H, hE, hEc, ⟨i₁⟩⟩` from `over_affineOpen P hVt B hB hBc _ hM`. Take `⟨i₂⟩` from `nonempty_cech_sliceFst_iso (P.A ⊗ P.A).hom (translDiff P.A P.L (𝟙 P.A)) (fun i => (snd P.A P.A).left ⁻¹ᵁ B i) (fun j => (fst P.A P.A).left ⁻¹ᵁ V j) t _ (preimage_biInf V (fst P.A P.A).left t)`. Establish `h` using `MumfordAway.acyclic_away K P Γ(P.A.left, ⨅ j ∈ t, V j) hVt.fromSpec Y π f H inferInstance (fun p q hpq => by`. Establish `hp : hVt.fromSpec p ∈ (⨅ j ∈ t, V j : P.A.left.Opens)` using `hVt.range_fromSpec.le ⟨p, rfl⟩`.

Rewrite `hp` using `[hpq, hq q]`. Conclude with `hV₁ j hj₀ (biInf_le V hj hp)) _ E hE hEc`. Conclude with `fun m => (acyclic_cechLB_of_acyclic f _ _ E h m).of_iso (i₁ ≪≫ i₂)) n`. Take `⟨-, Y, π, f, E, H, hE, hEc, ⟨i₁⟩⟩` from `over_affineOpen P (hV 0) B hB hBc _ hM`. Take `⟨i₂⟩` from `nonempty_cech_sliceFst_iso (P.A ⊗ P.A).hom (translDiff P.A P.L (𝟙 P.A)) (fun i => (snd P.A P.A).left ⁻¹ᵁ B i) (fun j => (fst P.A P.A).left ⁻¹ᵁ V j) {0} ((fst P.A P.A).left ⁻¹ᵁ V 0) (by simp)`.

Take `⟨p, hp⟩` from `(hV 0).range_fromSpec.ge hV₀`. Establish `h` using `(T.finrank_mumfordBundle_cech_homology_origin K P Γ(P.A.left, V 0) (hV 0).fromSpec Y π f H inferInstance ⟨p, q₀, hp⟩ E hE hEc n).2`. Rewrite using `[← h]`. Conclude with `(e₁ ≪≫ₗ (e₂ ≪≫ (HomologicalComplex.homologyMapIso (i₁ ≪≫ i₂) n).symm).toLinearEquiv).finrank_eq`.
-/
theorem finrank_cechLB_translDiff : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (P.A ⊗ P.A).left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ n, Module.finrank K ((cechLB (P.A ⊗ P.A).hom (translDiff P.A P.L (𝟙 P.A)) D).homology n) = if n = P.g then 1 else 0 := by
  intro K _ _ P κ _ _ D hD hc n
  obtain ⟨B, hB, hBc⟩ := AffineCover.exists_cover
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    trdeg_eq_of_smoothOfRelativeDimension K P
  have hsep : IsSeparated P.A.hom := (AbProj.abelian_projective_baseChange K P).1.2
  have hpr : IsProper P.A.hom := P.isAb.proper
  have : P.A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from P.A.hom]
    infer_instance⟩
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  let q₀ : (𝟙_ (Over (Spec (CommRingCat.of K)))).left := IsLocalRing.closedPoint K
  have hq (q : (𝟙_ (Over (Spec (CommRingCat.of K)))).left) : q = q₀ :=
    Subsingleton.elim (α := PrimeSpectrum K) _ _
  have ho : IsClosed {η[P.A].left q₀} := by
    rw [← Set.image_singleton]
    refine η[P.A].left.isClosedEmbedding.isClosedMap _ ?_
    rw [show ({q₀} : Set _) = Set.univ from Set.eq_univ_of_forall hq]
    exact isClosed_univ
  obtain ⟨r, V, hV, hVc, hV₀, hV₁⟩ := exists_cover_point P.A.left _ ho
  have hM : (translDiff P.A P.L (𝟙 P.A)).IsLB := LB.isLB_linComb P.isLB _ _
  have hsep' : IsSeparated (P.A ⊗ P.A).hom := by
    rw [← Over.w (fst P.A P.A)]
    have : IsSeparated (fst P.A P.A).left :=
      inferInstanceAs (IsSeparated (pullback.fst P.A.hom P.A.hom))
    infer_instance
  obtain ⟨e₁⟩ := cechLB_homology_equiv_trunc₂ K _ (P.A ⊗ P.A).hom _ κ D _ (fun i => (snd P.A P.A).left ⁻¹ᵁ B i) _
    (fun j => (fst P.A P.A).left ⁻¹ᵁ V j) hM hsep' hD hc
    (by rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
    (by rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
    (fun i _ h => isAffineOpen_preimage_inf _ (hB i) h)
    (fun j _ h => isAffineOpen_preimage_inf _ (hV j) h)
    (fun i j => (over_affineOpen P (hV j) B hB hBc _ hM).1 i) n
  have e₂ := trunc₂HomologyIsoFstSingleton (0 : Fin (r + 1)) (secCube (P.A ⊗ P.A).hom
    (translDiff P.A P.L (𝟙 P.A)) fun u : Fin (P.g + 1) ⊕ₗ Fin (r + 1) =>
      Sum.elim (fun i => (snd P.A P.A).left ⁻¹ᵁ B i) (fun j => (fst P.A P.A).left ⁻¹ᵁ V j) (ofLex u))
    (fun t ht ht' => by
      have hVt : IsAffineOpen (⨅ j ∈ t, V j) :=
        IsAffineOpen.biInf _ t.finite_toSet ht fun j _ => hV j
      obtain ⟨j, hj, hj₀⟩ : ∃ j ∈ t, j ≠ 0 := by
        by_contra! h
        exact ht' (Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨ht, h⟩)
      obtain ⟨-, Y, π, f, E, H, hE, hEc, ⟨i₁⟩⟩ := over_affineOpen P hVt B hB hBc _ hM
      obtain ⟨i₂⟩ := nonempty_cech_sliceFst_iso (P.A ⊗ P.A).hom (translDiff P.A P.L (𝟙 P.A))
        (fun i => (snd P.A P.A).left ⁻¹ᵁ B i) (fun j => (fst P.A P.A).left ⁻¹ᵁ V j) t _
        (preimage_biInf V (fst P.A P.A).left t)
      have h := MumfordAway.acyclic_away K P Γ(P.A.left, ⨅ j ∈ t, V j) hVt.fromSpec Y π f H inferInstance
        (fun p q hpq => by
          have hp : hVt.fromSpec p ∈ (⨅ j ∈ t, V j : P.A.left.Opens) :=
            hVt.range_fromSpec.le ⟨p, rfl⟩
          rw [hpq, hq q] at hp
          exact hV₁ j hj₀ (biInf_le V hj hp)) _ E hE hEc
      exact fun m => (acyclic_cechLB_of_acyclic f _ _ E h m).of_iso (i₁ ≪≫ i₂)) n
  obtain ⟨-, Y, π, f, E, H, hE, hEc, ⟨i₁⟩⟩ := over_affineOpen P (hV 0) B hB hBc _ hM
  obtain ⟨i₂⟩ := nonempty_cech_sliceFst_iso (P.A ⊗ P.A).hom (translDiff P.A P.L (𝟙 P.A))
    (fun i => (snd P.A P.A).left ⁻¹ᵁ B i) (fun j => (fst P.A P.A).left ⁻¹ᵁ V j) {0}
    ((fst P.A P.A).left ⁻¹ᵁ V 0) (by simp)
  obtain ⟨p, hp⟩ := (hV 0).range_fromSpec.ge hV₀
  have h := (T.finrank_mumfordBundle_cech_homology_origin K P Γ(P.A.left, V 0) (hV 0).fromSpec Y π f H inferInstance ⟨p, q₀, hp⟩
    E hE hEc n).2
  rw [← h]
  exact (e₁ ≪≫ₗ (e₂ ≪≫ (HomologicalComplex.homologyMapIso (i₁ ≪≫ i₂) n).symm).toLinearEquiv).finrank_eq

end GlobalTheory.MumfordCohom
