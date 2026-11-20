import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCovers
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBPullIsoOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProductAcyclic

/- English proof (translation)
Introduce `n`. Take `⟨e⟩` from `e n`. Establish `h₁` using `h n`. Rewrite `h₁`, the goal using `[HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]`. Conclude with `e.symm.injective.subsingleton`.
-/
theorem acyclic_of_homology_equiv {R : Type} [CommRing R] {C C' : CochainComplex (ModuleCat.{0} R) ℕ}
    (e : ∀ n, Nonempty (C.homology n ≃ₗ[R] C'.homology n)) (h : C.Acyclic) : C'.Acyclic := by
  intro n
  obtain ⟨e⟩ := e n
  have h₁ := h n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton] at h₁ ⊢
  exact e.symm.injective.subsingleton

/- English proof (translation)
Establish `hc : IsCompact (V₀ : Set X)ᶜ` using `V₀.isOpen.isClosed_compl.isCompact`. Take `⟨s, hs⟩` from `hc.elim_finite_subcover (fun W : {W : X.Opens // IsAffineOpen W ∧ W ≤ O} => (W.1 : Set X)) (fun W => W.1.isOpen) (by`. Introduce `x hx`. Take `⟨_, ⟨W, hW, rfl⟩, hxW, hWo⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (h x hx) O.isOpen`. Conclude with `Set.mem_iUnion.2 ⟨⟨W, hW, hWo⟩, hxW⟩)`.

Use `⟨s.card, Fin.cons V₀ fun j => (s.equivFin.symm j).1.1, fun j => ?_, ?_, rfl, fun j hj => ?_⟩` and prove the remaining obligations. Use `Fin.cases hV₀ (fun j => ?_) j` and prove the remaining obligations. Conclude with `(s.equivFin.symm j).1.2.1`. Use `top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ V₀`.

Conclude with `⟨0, hx⟩`. Take `⟨W, hW, hxW⟩` from `Set.mem_iUnion₂.1 (hs hx)`. Use `⟨(s.equivFin ⟨W, hW⟩).succ, ?_⟩` and prove the remaining obligations. Simplify using `using hxW`. Take `⟨j, rfl⟩` from `Fin.exists_succ_eq.2 hj`.

Conclude with `(s.equivFin.symm j).1.2.2`.
-/
theorem exists_cover (X : Scheme.{0}) [CompactSpace X] {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀)
    (O : X.Opens) (h : ∀ x, x ∉ V₀ → x ∈ O) :
    ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens), (∀ j, IsAffineOpen (V j)) ∧ ⨆ j, V j = ⊤ ∧
      V 0 = V₀ ∧ ∀ j, j ≠ 0 → V j ≤ O := by
  have hc : IsCompact (V₀ : Set X)ᶜ := V₀.isOpen.isClosed_compl.isCompact
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover
    (fun W : {W : X.Opens // IsAffineOpen W ∧ W ≤ O} => (W.1 : Set X)) (fun W => W.1.isOpen) (by
      intro x hx
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWo⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (h x hx) O.isOpen
      exact Set.mem_iUnion.2 ⟨⟨W, hW, hWo⟩, hxW⟩)
  refine ⟨s.card, Fin.cons V₀ fun j => (s.equivFin.symm j).1.1, fun j => ?_, ?_, rfl, fun j hj => ?_⟩
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

variable {K : Type} [Field K] {Z T X : Scheme.{0}} {p : Z ⟶ T} {g : T ⟶ Spec (CommRingCat.of K)}
  {q : Z ⟶ X} {h : X ⟶ Spec (CommRingCat.of K)} {F : LB Z}

/- English proof (translation)
Establish `H' : IsPullback (π ≫ q) f h (t ≫ g)` using `H.paste_horiz sq.flip`. Establish `: IsOpenImmersion π` using `MorphismProperty.of_isPullback (P := @IsOpenImmersion) H.flip ‹_›`. Establish `hq : IsAffineHom (π ≫ q)` using `MorphismProperty.of_isPullback (P := @IsAffineHom) H'.flip inferInstance`. Establish `hsep : IsSeparated f` using `MorphismProperty.of_isPullback (P := @IsSeparated) H' ‹_›`. Establish `hr : π.opensRange = p ⁻¹ᵁ V`.

Substitute `hV` using the available equality. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `⟨f y, by rw [← Scheme.Hom.comp_apply, ← H.w, Scheme.Hom.comp_apply]⟩`. Introduce and unpack `x ⟨y, hy⟩`.

Take `⟨w, hw, -⟩` from `Scheme.exists_preimage_of_isPullback H x y hy.symm`. Conclude with `⟨w, hw⟩`. Establish `hE (i : ν) : π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) = (π ≫ q) ⁻¹ᵁ B i`. Rewrite using `[← hr, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq, Scheme.Hom.comp_preimage]`. Establish `hA (i : ν) : IsAffineOpen ((π ≫ q) ⁻¹ᵁ B i)` using `(hB i).preimage _`.

Establish `hA' (i : ν) : IsAffineOpen (π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V))` using `(congrArg IsAffineOpen (hE i)).mpr (hA i)`. Establish `hc' : ⨆ i, π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) = ⊤`. Simplify using `only [hE]`. Rewrite using `[← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]`. Take `⟨e⟩` from `cechLB_pull_iso_of_isOpenImmersion K _ (p ≫ g) F _ π ν (fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) hF fun i => hr ▸ inf_le_right`.

Use `⟨fun i => ?_, fun h₁ n => ?_, fun h₁ κ _ _ D hD hDc => ?_⟩` and prove the remaining obligations. Establish `h₁` using `(hA i).image_of_isOpenImmersion π`. Rewrite `h₁` using `[Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hr, inf_comm]`. Then use the resulting hypothesis. Conclude with `(MumfordCohom.acyclic_cechLB_of_acyclic _ _ _ _ (h₁ ν _ hA' hc') n).of_iso e`. Conclude with `acyclic_of_homology_equiv (cechLB_homology_equiv_of_affine_covers R Y f _ ν _ κ D (LB.isLB_pull hF π) hsep hA' hc' hD hDc) (MumfordCohom.acyclic_cechLB_of_acyclic _ _ _ _ fun n => (h₁ n).of_iso e.symm)`.
-/
theorem over_affineOpen (sq : IsPullback p q g h) [IsSeparated h] (hF : F.IsLB)
    {R : Type} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ T} [IsOpenImmersion t] {Y : Scheme.{0}}
    {π : Y ⟶ Z} {f : Y ⟶ Spec (CommRingCat.of R)} (H : IsPullback π f p t)
    {V : T.Opens} (hV : t.opensRange = V) {ν : Type} [LinearOrder ν] [Fintype ν]
    (B : ν → X.Opens) (hB : ∀ i, IsAffineOpen (B i)) (hc : ⨆ i, B i = ⊤) :
    (∀ i, IsAffineOpen (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V)) ∧
    ((∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) →
        ⨆ i, D i = ⊤ → (cechLB f (F.pull π) D).Acyclic) ↔
      (cechLB (p ≫ g) F fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V).Acyclic) := by
  have H' : IsPullback (π ≫ q) f h (t ≫ g) := H.paste_horiz sq.flip
  have : IsOpenImmersion π := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H.flip ‹_›
  have hq : IsAffineHom (π ≫ q) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) H'.flip inferInstance
  have hsep : IsSeparated f := MorphismProperty.of_isPullback (P := @IsSeparated) H' ‹_›
  have hr : π.opensRange = p ⁻¹ᵁ V := by
    subst hV
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, rfl⟩
      exact ⟨f y, by rw [← Scheme.Hom.comp_apply, ← H.w, Scheme.Hom.comp_apply]⟩
    · rintro x ⟨y, hy⟩
      obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback H x y hy.symm
      exact ⟨w, hw⟩
  have hE (i : ν) : π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) = (π ≫ q) ⁻¹ᵁ B i := by
    rw [← hr, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq,
      Scheme.Hom.comp_preimage]
  have hA (i : ν) : IsAffineOpen ((π ≫ q) ⁻¹ᵁ B i) := (hB i).preimage _
  have hA' (i : ν) : IsAffineOpen (π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V)) :=
    (congrArg IsAffineOpen (hE i)).mpr (hA i)
  have hc' : ⨆ i, π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) = ⊤ := by
    simp only [hE]
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  obtain ⟨e⟩ := cechLB_pull_iso_of_isOpenImmersion K _ (p ≫ g) F _ π ν
    (fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) hF fun i => hr ▸ inf_le_right
  refine ⟨fun i => ?_, fun h₁ n => ?_, fun h₁ κ _ _ D hD hDc => ?_⟩
  · have h₁ := (hA i).image_of_isOpenImmersion π
    rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hr, inf_comm] at h₁
  · exact (MumfordCohom.acyclic_cechLB_of_acyclic _ _ _ _ (h₁ ν _ hA' hc') n).of_iso e
  · exact acyclic_of_homology_equiv (cechLB_homology_equiv_of_affine_covers R Y f _ ν _ κ D
      (LB.isLB_pull hF π) hsep hA' hc' hD hDc)
      (MumfordCohom.acyclic_cechLB_of_acyclic _ _ _ _ fun n => (h₁ n).of_iso e.symm)

/- English proof (translation)
The claim follows from `(over_affineOpen (R := Γ(T, V)) sq hF (IsPullback.of_hasPullback p hV.fromSpec) hV.opensRange_fromSpec B hB hc).1 i`.
-/
theorem isAffineOpen_prod (sq : IsPullback p q g h) [IsSeparated h] (hF : F.IsLB) {V : T.Opens}
    (hV : IsAffineOpen V) {ν : Type} [LinearOrder ν] [Fintype ν]
    (B : ν → X.Opens) (hB : ∀ i, IsAffineOpen (B i)) (hc : ⨆ i, B i = ⊤) (i : ν) :
    IsAffineOpen (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) :=
  (over_affineOpen (R := Γ(T, V)) sq hF (IsPullback.of_hasPullback p hV.fromSpec)
    hV.opensRange_fromSpec B hB hc).1 i

/- English proof (translation)
Establish `: T.IsSeparated` using `⟨by`. Rewrite using `[← terminal.comp_from g]`. Use the proof step `infer_instance⟩`. Establish `: X.IsSeparated` using `⟨by`. Rewrite using `[← terminal.comp_from h]`.

Use the proof step `infer_instance⟩`. Establish `: IsSeparated p` using `MorphismProperty.of_isPullback (P := @IsSeparated) sq.flip ‹_›`. Take `⟨e₁⟩` from `cechLB_homology_equiv_trunc₂ K _ (p ≫ g) F κ D _ (fun i => q ⁻¹ᵁ B i) _ (fun j => p ⁻¹ᵁ V j) hF inferInstance hD hc (by rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top]) (by rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top]) (fun i _ hW => MumfordCohom.is …`. Establish `e₂` using `trunc₂HomologyIsoFstSingleton k (secCube (p ≫ g) F fun u : ν ⊕ₗ σ => Sum.elim (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) (ofLex u)) (fun s hs hs' => by`. Establish `hVs : IsAffineOpen (⨅ j ∈ s, V j)` using `IsAffineOpen.biInf _ s.finite_toSet hs fun j _ => hV j`.

Take `⟨j, hj, hjk⟩ : ∃ j ∈ s, j ≠ k` from `by by_contra! h₀`. Conclude with `hs' (Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨hs, h₀⟩)`. Establish `H₀` using `IsPullback.of_hasPullback p hVs.fromSpec`. Establish `h₁` using `(over_affineOpen (R := Γ(T, ⨅ j ∈ s, V j)) sq hF H₀ hVs.opensRange_fromSpec B hB hBc).2.1 (H Γ(T, ⨅ j ∈ s, V j) _ _ _ _ H₀ inferInstance j hjk fun y => biInf_le V hj (hVs.range_fromSpec.le ⟨y, rfl⟩))`. Take `⟨i₂⟩` from `MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ g) F (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) s _ (preimage_biInf V p s)`.

Conclude with `fun m => (h₁ m).of_iso i₂) n`. Take `⟨i₂⟩` from `MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ g) F (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) {k} (p ⁻¹ᵁ V k) (by simp)`. Conclude with `⟨e₁ ≪≫ₗ (e₂ ≪≫ (HomologicalComplex.homologyMapIso i₂ n).symm).toLinearEquiv⟩`.
-/
theorem homology_equiv_over (sq : IsPullback p q g h) [IsSeparated g] [IsSeparated h] (hF : F.IsLB)
    {σ : Type} [LinearOrder σ] [Fintype σ] (V : σ → T.Opens) (hV : ∀ j, IsAffineOpen (V j))
    (hVc : ⨆ j, V j = ⊤) (k : σ)
    (H : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z)
      (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t →
      ∀ j, j ≠ k → (∀ y, t y ∈ V j) →
      ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) →
        ⨆ i, D i = ⊤ → (cechLB f (F.pull π) D).Acyclic)
    {ν : Type} [LinearOrder ν] [Fintype ν] (B : ν → X.Opens) (hB : ∀ i, IsAffineOpen (B i))
    (hBc : ⨆ i, B i = ⊤) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → Z.Opens)
    (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤) (n : ℕ) :
    Nonempty ((cechLB (p ≫ g) F D).homology n ≃ₗ[K]
      (cechLB (p ≫ g) F fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V k).homology n) := by
  have : T.IsSeparated := ⟨by
    rw [← terminal.comp_from g]
    infer_instance⟩
  have : X.IsSeparated := ⟨by
    rw [← terminal.comp_from h]
    infer_instance⟩
  have : IsSeparated p := MorphismProperty.of_isPullback (P := @IsSeparated) sq.flip ‹_›
  obtain ⟨e₁⟩ := cechLB_homology_equiv_trunc₂ K _ (p ≫ g) F κ D _
    (fun i => q ⁻¹ᵁ B i) _ (fun j => p ⁻¹ᵁ V j) hF inferInstance hD hc
    (by rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
    (by rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
    (fun i _ hW => MumfordCohom.isAffineOpen_preimage_inf _ (hB i) hW)
    (fun j _ hW => MumfordCohom.isAffineOpen_preimage_inf _ (hV j) hW)
    (fun i j => isAffineOpen_prod sq hF (hV j) B hB hBc i) n
  have e₂ := trunc₂HomologyIsoFstSingleton k (secCube (p ≫ g) F fun u : ν ⊕ₗ σ =>
      Sum.elim (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) (ofLex u))
    (fun s hs hs' => by
      have hVs : IsAffineOpen (⨅ j ∈ s, V j) :=
        IsAffineOpen.biInf _ s.finite_toSet hs fun j _ => hV j
      obtain ⟨j, hj, hjk⟩ : ∃ j ∈ s, j ≠ k := by
        by_contra! h₀
        exact hs' (Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨hs, h₀⟩)
      have H₀ := IsPullback.of_hasPullback p hVs.fromSpec
      have h₁ := (over_affineOpen (R := Γ(T, ⨅ j ∈ s, V j)) sq hF H₀ hVs.opensRange_fromSpec
        B hB hBc).2.1 (H Γ(T, ⨅ j ∈ s, V j) _ _ _ _ H₀ inferInstance j hjk
          fun y => biInf_le V hj (hVs.range_fromSpec.le ⟨y, rfl⟩))
      obtain ⟨i₂⟩ := MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ g) F
        (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) s _ (preimage_biInf V p s)
      exact fun m => (h₁ m).of_iso i₂) n
  obtain ⟨i₂⟩ := MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ g) F
    (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) {k} (p ⁻¹ᵁ V k) (by simp)
  exact ⟨e₁ ≪≫ₗ (e₂ ≪≫ (HomologicalComplex.homologyMapIso i₂ n).symm).toLinearEquiv⟩

/- English proof (translation)
Introduce `K _ Z T p g X q h sq _ _ _ _ F hF`. Establish `: CompactSpace T` using `QuasiCompact.compactSpace_of_compactSpace g`. Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace h`. Take `⟨m, B, hB, hBc, -, -⟩` from `exists_cover X (isAffineOpen_bot X) ⊤ fun _ _ => trivial`. Use `⟨fun H κ _ _ D hD hc => ?_, fun t₀ ht₀ H hac R _ t Y π f H₀ ht => ?_⟩` and prove the remaining obligations.

Take `⟨r, V, hV, hVc, -, -⟩` from `exists_cover T (isAffineOpen_bot T) ⊤ fun _ _ => trivial`. Establish `H₀` using `IsPullback.of_hasPullback p (hV 0).fromSpec`. Use `acyclic_of_homology_equiv (fun n => ?_) ((over_affineOpen (R := Γ(T, V 0)) sq hF H₀ (hV 0).opensRange_fromSpec B hB hBc).2.1 (H Γ(T, V 0) _ _ _ _ H₀ inferInstance))` and prove the remaining obligations. Conclude with `(homology_equiv_over sq hF V hV hVc 0 (fun R _ t Y π f H₁ ht _ _ _ => H R t Y π f H₁ ht) B hB hBc D hD hc n).map fun e => e.symm`. Distinguish the cases in `h₀ : t₀ ∈ t.opensRange swap`.

Conclude with `H R t Y π f H₀ ht fun y hy => h₀ ⟨y, hy⟩`. Take `⟨r, V, hV, hVc, hV₀, hV₁⟩` from `exists_cover T (isAffineOpen_opensRange t) ⟨{t₀}ᶜ, ht₀.isOpen_compl⟩ fun x hx hx' => hx ((show x = t₀ from hx') ▸ h₀)`. Set `P : Fin (m + 1) ×ₗ Fin (r + 1) → Z.Opens` to `fun u => q ⁻¹ᵁ B (ofLex u).1 ⊓ p ⁻¹ᵁ V (ofLex u).2`. Establish `hP (u) : IsAffineOpen (P u)` using `isAffineOpen_prod sq hF (hV _) B hB hBc _`. Establish `hPc : ⨆ u, P u = ⊤`.

Use `top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hBc.ge (Set.mem_univ (q x)))`. Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hVc.ge (Set.mem_univ (p x)))`. Conclude with `⟨toLex (i, j), hi, hj⟩`. Use `(over_affineOpen sq hF H₀ hV₀.symm B hB hBc).2.2 ?_` and prove the remaining obligations.

Conclude with `acyclic_of_homology_equiv (homology_equiv_over sq hF V hV hVc 0 (fun R _ t Y π f H₁ ht j hj hy => H R t Y π f H₁ ht fun y e => hV₁ j hj (hy y) e) B hB hBc P hP hPc) (hac _ P hP hPc)`.
-/
theorem acyclic_of_over_affine_and_converse : ∀ (K : Type) [Field K] (Z T : Scheme.{0}) (p : Z ⟶ T) (g : T ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0}) (q : Z ⟶ X) (h : X ⟶ Spec (CommRingCat.of K)), IsPullback p q g h → IsSeparated g → QuasiCompact g → IsSeparated h → QuasiCompact h → ∀ F : LB Z, F.IsLB → ((∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Z).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (p ≫ g) (F) D).Acyclic)) ∧ ∀ t₀ : T, IsClosed ({t₀} : Set T) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ y, t y ≠ t₀) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Z).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (p ≫ g) (F) D).Acyclic) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) := by
  intro K _ Z T p g X q h sq _ _ _ _ F hF
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace g
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace h
  obtain ⟨m, B, hB, hBc, -, -⟩ := exists_cover X (isAffineOpen_bot X) ⊤ fun _ _ => trivial
  refine ⟨fun H κ _ _ D hD hc => ?_, fun t₀ ht₀ H hac R _ t Y π f H₀ ht => ?_⟩
  · obtain ⟨r, V, hV, hVc, -, -⟩ := exists_cover T (isAffineOpen_bot T) ⊤ fun _ _ => trivial
    have H₀ := IsPullback.of_hasPullback p (hV 0).fromSpec
    refine acyclic_of_homology_equiv (fun n => ?_) ((over_affineOpen (R := Γ(T, V 0)) sq hF H₀
      (hV 0).opensRange_fromSpec B hB hBc).2.1 (H Γ(T, V 0) _ _ _ _ H₀ inferInstance))
    exact (homology_equiv_over sq hF V hV hVc 0
      (fun R _ t Y π f H₁ ht _ _ _ => H R t Y π f H₁ ht) B hB hBc D hD hc n).map fun e => e.symm
  · by_cases h₀ : t₀ ∈ t.opensRange
    swap
    · exact H R t Y π f H₀ ht fun y hy => h₀ ⟨y, hy⟩
    obtain ⟨r, V, hV, hVc, hV₀, hV₁⟩ := exists_cover T (isAffineOpen_opensRange t)
      ⟨{t₀}ᶜ, ht₀.isOpen_compl⟩ fun x hx hx' => hx ((show x = t₀ from hx') ▸ h₀)
    let P : Fin (m + 1) ×ₗ Fin (r + 1) → Z.Opens := fun u =>
      q ⁻¹ᵁ B (ofLex u).1 ⊓ p ⁻¹ᵁ V (ofLex u).2
    have hP (u) : IsAffineOpen (P u) := isAffineOpen_prod sq hF (hV _) B hB hBc _
    have hPc : ⨆ u, P u = ⊤ := by
      refine top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hBc.ge (Set.mem_univ (q x)))
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hVc.ge (Set.mem_univ (p x)))
      exact ⟨toLex (i, j), hi, hj⟩
    refine (over_affineOpen sq hF H₀ hV₀.symm B hB hBc).2.2 ?_
    exact acyclic_of_homology_equiv (homology_equiv_over sq hF V hV hVc 0
      (fun R _ t Y π f H₁ ht j hj hy => H R t Y π f H₁ ht fun y e => hV₁ j hj (hy y) e)
      B hB hBc P hP hPc) (hac _ P hP hPc)

end GlobalTheory.ProductAcyclic
