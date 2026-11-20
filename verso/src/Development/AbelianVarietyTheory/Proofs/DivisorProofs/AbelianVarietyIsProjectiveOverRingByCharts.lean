import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRelAmpleOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPwOfAffineLoci
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormChartLineBundleBaseChangeFieldExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ProjField
open GlobalTheory.AbelianProjective

/- English proof (translation)
Introduce `Ω _ _ B _ hB N₀ hN₀ ⟨W, V, π, a, U, N, n, hfin, hop, hne, hlft, hU, hUne, hN, H, hn⟩`. Use `hB.smooth` as an intermediate fact. Use `hB.proper` as an intermediate fact. Establish `: GeometricallyIntegral B.hom` using `GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected`. Establish `: IsIntegral B.left` using `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian B.hom`.

Establish `: IsIntegral W.left` using `isIntegral_of_isOpenImmersion a.left`. Use `choose t ht using fun w : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ W => exists_sec_fibre hN hN₀ H n (w ≫ π)`. Use `⟨_, t, ?_, fun w => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne'`. Establish `hc : ((⨆ i, Out.nonzeroLocus (t i) : B.left.Opens) : Set B.left)ᶜ.Nonempty` using `Set.nonempty_compl.2 fun h => hne' (TopologicalSpace.Opens.ext h)`.

Take `⟨y, hy⟩` from `exists_point B (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed hc`. Take `⟨w, hw⟩` from `exists_fibre_mem π a U hUne (Out.nonzeroLocus n) (fun x => (hn x).2) y`. Use `hy (IsLocalRing.closedPoint Ω) (TopologicalSpace.Opens.mem_iSup.2 ⟨w, ?_⟩)` and prove the remaining obligations. Rewrite using `[ht]`. Conclude with `hw _`.

Establish `hle : Out.nonzeroLocus (t w) ≤ ((toUnit B ≫ w ≫ a) * 𝟙 B).left ⁻¹ᵁ U` using `(ht w).trans_le (fibre_le π a U (Out.nonzeroLocus n) (fun x => (hn x).1) w)`. Use `isIso_transl_left (w ≫ a)` as an intermediate fact. Establish `: IsIso ((toUnit B ≫ w ≫ a) * 𝟙 B).left` using `inferInstanceAs (IsIso ((Over.forget _).map ((toUnit B ≫ w ≫ a) * 𝟙 B)))`. Establish `h` using `GlobalTheory.isAffineOpen_nonzeroLocus_inf hN₀ (t w) (hU.preimage ((toUnit B ≫ w ≫ a) * 𝟙 B).left)`. Rewrite `h` using `[inf_eq_left.2 hle]`. Then use the resulting hypothesis.
-/
theorem exists_affine_loci_of_normChart : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (B : Over (Sp Ω)) [GrpObj B], IsAbelianScheme B → ∀ N₀ : LB B.left, N₀.IsLB → NormChart B N₀ → ∃ (I : Type) (t : I → N₀.Sec), (⨆ i, Out.nonzeroLocus (t i) = ⊤) ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (t i)) := by
  intro Ω _ _ B _ hB N₀ hN₀ ⟨W, V, π, a, U, N, n, hfin, hop, hne, hlft, hU, hUne, hN, H, hn⟩
  have := hB.smooth
  have := hB.proper
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian B.hom
  have : IsIntegral W.left := isIntegral_of_isOpenImmersion a.left
  choose t ht using fun w : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ W => exists_sec_fibre hN hN₀ H n (w ≫ π)
  refine ⟨_, t, ?_, fun w => ?_⟩
  · by_contra hne'
    have hc : ((⨆ i, Out.nonzeroLocus (t i) : B.left.Opens) : Set B.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h => hne' (TopologicalSpace.Opens.ext h)
    obtain ⟨y, hy⟩ := exists_point B (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed hc
    obtain ⟨w, hw⟩ := exists_fibre_mem π a U hUne (Out.nonzeroLocus n) (fun x => (hn x).2) y
    refine hy (IsLocalRing.closedPoint Ω) (TopologicalSpace.Opens.mem_iSup.2 ⟨w, ?_⟩)
    rw [ht]
    exact hw _
  · have hle : Out.nonzeroLocus (t w) ≤ ((toUnit B ≫ w ≫ a) * 𝟙 B).left ⁻¹ᵁ U :=
      (ht w).trans_le (fibre_le π a U (Out.nonzeroLocus n) (fun x => (hn x).1) w)
    have := isIso_transl_left (w ≫ a)
    have : IsIso ((toUnit B ≫ w ≫ a) * 𝟙 B).left :=
      inferInstanceAs (IsIso ((Over.forget _).map ((toUnit B ≫ w ≫ a) * 𝟙 B)))
    have h := GlobalTheory.isAffineOpen_nonzeroLocus_inf hN₀ (t w) (hU.preimage ((toUnit B ≫ w ≫ a) * 𝟙 B).left)
    rwa [inf_eq_left.2 hle] at h

/- English proof (translation)
Introduce `K _ B _ hB`. Use `hB.smooth` as an intermediate fact. Use `hB.proper` as an intermediate fact. Establish `: GeometricallyIntegral B.hom` using `GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected`. Establish `: IsIntegral B.left` using `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian B.hom`.

Establish `: IsLocallyNoetherian B.left` using `LocallyOfFiniteType.isLocallyNoetherian B.hom`. Establish `: B.left.IsSeparated` using `⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint B.left)) isOpen_univ`. Take `⟨L, s, hL, hs⟩` from `GlobalTheory.exists_sec_nonzeroLocus_eq_of_isAffineOpen_of_factorial B.left (ufd_stalk B.hom) U hU ⟨_, hxU⟩`. Take `⟨g, W₀, V₀, π₀, hW, hfin, hflat, -, hπ⟩` from `GlobalTheory.Unif.exists_finite_flat_chart K B.left B.hom`.

Set `A : Over (Spec (CommRingCat.of K))` to `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K))))`. Establish `: Smooth A.hom` using `smooth_affineSpace K g`. Establish `: IsIntegral A.left` using `inferInstanceAs (IsIntegral (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))`. Establish `: IsAffine A.left` using `inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))`. Establish `: IsLocallyNoetherian A.left` using `LocallyOfFiniteType.isLocallyNoetherian A.hom`.

Set `W : Over (Spec (CommRingCat.of K))` to `Over.mk (W₀.ι ≫ B.hom)`. Set `V : Over (Spec (CommRingCat.of K))` to `Over.mk (V₀.ι ≫ A.hom)`. Set `π : W ⟶ V` to `Over.homMk π₀ hπ`. Set `a : W ⟶ B` to `Over.homMk W₀.ι rfl`. Set `j : V ⟶ A` to `Over.homMk V₀.ι rfl`.

Establish `: IsFinite π.left` using `hfin`. Establish `: Flat π.left` using `hflat`. Establish `: IsOpenImmersion a.left` using `inferInstanceAs (IsOpenImmersion W₀.ι)`. Establish `: IsOpenImmersion j.left` using `inferInstanceAs (IsOpenImmersion V₀.ι)`. Establish `: Nonempty W.left` using `⟨⟨hW.choose, hW.choose_spec⟩⟩`.

Establish `: LocallyOfFiniteType W.hom` using `inferInstanceAs (LocallyOfFiniteType (W₀.ι ≫ B.hom))`. Establish `: IsFinite (π ▷ B).left` using `MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›`. Establish `: Flat (π ▷ B).left` using `MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›`. Establish `hj : IsOpenImmersion (j ▷ B).left` using `MorphismProperty.of_isPullback (isPullback_whiskerRight j B) ‹_›`. Establish `: Smooth (A ⊗ B).hom` using `inferInstanceAs (Smooth (pullback.fst A.hom B.hom ≫ A.hom))`.

Establish `: QuasiCompact (A ⊗ B).hom` using `inferInstanceAs (QuasiCompact (pullback.fst A.hom B.hom ≫ A.hom))`. Establish `: IsLocallyNoetherian (A ⊗ B).left` using `LocallyOfFiniteType.isLocallyNoetherian (A ⊗ B).hom`. Establish `: CompactSpace (A ⊗ B).left` using `QuasiCompact.compactSpace_of_compactSpace (A ⊗ B).hom`. Establish `: IsIntegral (A ⊗ B).left` using `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst A.hom B.hom)`. Establish `: IsLocallyNoetherian (V ⊗ B).left` using `LocallyOfFiniteType.isLocallyNoetherian (j ▷ B).left`.

Take `⟨N, n, hN, hn⟩` from `GlobalTheory.FlatNorm.exists_norm_lb _ _ (π ▷ B).left (L.pull ((fst W B ≫ a) * snd W B).left) (GlobalTheory.secPull s _) (pull_isLB hL _)`. Rewrite `hn` using `[GlobalTheory.nonzeroLocus_secPull, hs]`. Take `⟨N', hN', hφ⟩` from `GlobalTheory.exists_lineBundle_extension _ _ (j ▷ B).left hj (ufd_stalk (A ⊗ B).hom) N hN`. Take `⟨N₀, hN₀, hψ⟩` from `GlobalTheory.exists_lbIso_pull_affineSpace K B (ufd_stalk B.hom) g N' hN'`. Establish `e : (snd V B).left = (j ▷ B).left ≫ (snd A B).left`.

Rewrite using `[← Over.comp_left, whiskerRight_snd]`. Establish `H : LBIso N (N₀.pull (snd V B).left)` using `LBIso.trans hN (pull_isLB hN' _) (pull_isLB hN₀ _) (LBIso.symm hφ) (LBIso.chartPull (GlobalTheory.chartPullPull N' _) (chartPullSame N₀ _ _ _ _ fun _ => e) hψ)`. Conclude with `⟨N₀, hN₀, W, V, π, a, U, N, n, hfin, inferInstance, inferInstance, inferInstance, hU, ⟨_, hxU⟩, hN, H, hn⟩`.
-/
theorem exists_normChart : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ N₀ : LB A.left, N₀.IsLB ∧ NormChart A N₀ := by
  intro K _ B _ hB
  have := hB.smooth
  have := hB.proper
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian B.hom
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint B.left)) isOpen_univ
  obtain ⟨L, s, hL, hs⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_isAffineOpen_of_factorial B.left (ufd_stalk B.hom) U hU ⟨_, hxU⟩
  obtain ⟨g, W₀, V₀, π₀, hW, hfin, hflat, -, hπ⟩ := GlobalTheory.Unif.exists_finite_flat_chart K B.left B.hom
  let A : Over (Spec (CommRingCat.of K)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K))))
  have : Smooth A.hom := smooth_affineSpace K g
  have : IsIntegral A.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))
  have : IsAffine A.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  let W : Over (Spec (CommRingCat.of K)) := Over.mk (W₀.ι ≫ B.hom)
  let V : Over (Spec (CommRingCat.of K)) := Over.mk (V₀.ι ≫ A.hom)
  let π : W ⟶ V := Over.homMk π₀ hπ
  let a : W ⟶ B := Over.homMk W₀.ι rfl
  let j : V ⟶ A := Over.homMk V₀.ι rfl
  have : IsFinite π.left := hfin
  have : Flat π.left := hflat
  have : IsOpenImmersion a.left := inferInstanceAs (IsOpenImmersion W₀.ι)
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion V₀.ι)
  have : Nonempty W.left := ⟨⟨hW.choose, hW.choose_spec⟩⟩
  have : LocallyOfFiniteType W.hom := inferInstanceAs (LocallyOfFiniteType (W₀.ι ≫ B.hom))
  have : IsFinite (π ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›
  have : Flat (π ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›
  have hj : IsOpenImmersion (j ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight j B) ‹_›
  have : Smooth (A ⊗ B).hom := inferInstanceAs (Smooth (pullback.fst A.hom B.hom ≫ A.hom))
  have : QuasiCompact (A ⊗ B).hom := inferInstanceAs (QuasiCompact (pullback.fst A.hom B.hom ≫ A.hom))
  have : IsLocallyNoetherian (A ⊗ B).left := LocallyOfFiniteType.isLocallyNoetherian (A ⊗ B).hom
  have : CompactSpace (A ⊗ B).left := QuasiCompact.compactSpace_of_compactSpace (A ⊗ B).hom
  have : IsIntegral (A ⊗ B).left :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst A.hom B.hom)
  have : IsLocallyNoetherian (V ⊗ B).left :=
    LocallyOfFiniteType.isLocallyNoetherian (j ▷ B).left
  obtain ⟨N, n, hN, hn⟩ := GlobalTheory.FlatNorm.exists_norm_lb _ _ (π ▷ B).left (L.pull ((fst W B ≫ a) * snd W B).left)
    (GlobalTheory.secPull s _) (pull_isLB hL _)
  rw [GlobalTheory.nonzeroLocus_secPull, hs] at hn
  obtain ⟨N', hN', hφ⟩ := GlobalTheory.exists_lineBundle_extension _ _ (j ▷ B).left hj (ufd_stalk (A ⊗ B).hom) N hN
  obtain ⟨N₀, hN₀, hψ⟩ := GlobalTheory.exists_lbIso_pull_affineSpace K B (ufd_stalk B.hom) g N' hN'
  have e : (snd V B).left = (j ▷ B).left ≫ (snd A B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have H : LBIso N (N₀.pull (snd V B).left) :=
    LBIso.trans hN (pull_isLB hN' _) (pull_isLB hN₀ _) (LBIso.symm hφ)
      (LBIso.chartPull (GlobalTheory.chartPullPull N' _) (chartPullSame N₀ _ _ _ _ fun _ => e) hψ)
  exact ⟨N₀, hN₀, W, V, π, a, U, N, n, hfin, inferInstance, inferInstance, inferInstance, hU, ⟨_, hxU⟩, hN, H, hn⟩

/- English proof (translation)
Establish `: IsProper B.hom` using `MorphismProperty.of_isPullback (P := @IsProper) h inferInstance`. Establish `: CompactSpace B.left` using `QuasiCompact.compactSpace_of_compactSpace B.hom`. Establish `hN` using `pull_isLB hN₀ φ`. Take `⟨F, hF⟩` from `isCompact_univ.elim_finite_subcover (fun j => (Out.nonzeroLocus (t j) : Set B.left)) (fun j => (Out.nonzeroLocus (t j)).isOpen) fun x _ => by`. Establish `hx : x ∈ ⨆ j, Out.nonzeroLocus (t j)` using `by rw [hc]; trivial`.

Conclude with `Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 hx)`. Establish `hamp : GlobalTheory.IsAmpleLB (N₀.pull φ)` using `GlobalTheory.isAmpleLB_of_cover hN le_rfl (fun j : F => GlobalTheory.secToPow (t j.1) 1) (top_unique fun x _ => by`. Take `⟨j, hj, hx⟩` from `Set.mem_iUnion₂.1 (hF (Set.mem_univ x))`. Use `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨j, hj⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.nonzeroLocus_secToPow _ le_rfl]`.

Conclude with `hx)`. Use `fun j => (GlobalTheory.nonzeroLocus_secToPow (t j.1) le_rfl).symm ▸ ha j.1`. Conclude with `GlobalTheory.ProjFinite.isProjBy_of_fieldExtension i h hN₀ hN (GlobalTheory.lbIso_refl hN) ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B hN).2 hamp)`.
-/
theorem isProjBy_of_cover_baseChange {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) (A : Over (Sp K)) [IsProper A.hom]
    {B : Over (Sp Ω)} {φ : B.left ⟶ A.left} (h : IsPullback φ B.hom A.hom (spMap i)) {N₀ : LB A.left} (hN₀ : N₀.IsLB)
    {I : Type} (t : I → (N₀.pull φ).Sec) (hc : ⨆ j, Out.nonzeroLocus (t j) = ⊤)
    (ha : ∀ j, IsAffineOpen (Out.nonzeroLocus (t j))) : GlobalTheory.AbLaw.IsProjBy A.hom := by
  have : IsProper B.hom := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have hN := pull_isLB hN₀ φ
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun j => (Out.nonzeroLocus (t j) : Set B.left))
    (fun j => (Out.nonzeroLocus (t j)).isOpen) fun x _ => by
      have hx : x ∈ ⨆ j, Out.nonzeroLocus (t j) := by rw [hc]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 hx)
  have hamp : GlobalTheory.IsAmpleLB (N₀.pull φ) := GlobalTheory.isAmpleLB_of_cover hN le_rfl
    (fun j : F => GlobalTheory.secToPow (t j.1) 1) (top_unique fun x _ => by
      obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
      refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨j, hj⟩, ?_⟩
      rw [GlobalTheory.nonzeroLocus_secToPow _ le_rfl]
      exact hx)
    fun j => (GlobalTheory.nonzeroLocus_secToPow (t j.1) le_rfl).symm ▸ ha j.1
  exact GlobalTheory.ProjFinite.isProjBy_of_fieldExtension i h hN₀ hN (GlobalTheory.lbIso_refl hN)
    ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B hN).2 hamp)

/- English proof (translation)
Introduce `K _ A _ hA`. Use `hA.proper` as an intermediate fact. Use `hA.comm` as an intermediate fact. Take `⟨N₀, hN₀, hc⟩` from `exists_normChart K A hA`. Set `Ω` to `AlgebraicClosure K`.

Set `B : Over (Sp Ω)` to `(Over.pullback (spMap (algebraMap K Ω))).obj A`. Establish `sqB : IsPullback (pullback.fst A.hom (spMap (algebraMap K Ω))) B.hom A.hom (spMap (algebraMap K Ω))` using `IsPullback.of_hasPullback _ _`. Establish `hB : IsAbelianScheme B` using `{ comm := inferInstance smooth := MorphismProperty.of_isPullback (P := @Smooth) sqB hA.smooth proper := MorphismProperty.of_isPullback (P := @IsProper) sqB hA.proper geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) sqB hA.geomConnected }`. Take `⟨I, t, hcov, ha⟩` from `exists_affine_loci_of_normChart Ω B hB _ (pull_isLB hN₀ _) (GlobalTheory.T.normChartLineBundle_baseChange_field_extension K Ω A hA N₀ hN₀ hc)`. Conclude with `isProjBy_of_cover_baseChange _ A sqB hN₀ t hcov ha`.
-/
theorem isProjBy_of_isAbelianScheme : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom := by
  intro K _ A _ hA
  have := hA.proper
  have := hA.comm
  obtain ⟨N₀, hN₀, hc⟩ := exists_normChart K A hA
  let Ω := AlgebraicClosure K
  let B : Over (Sp Ω) := (Over.pullback (spMap (algebraMap K Ω))).obj A
  have sqB : IsPullback (pullback.fst A.hom (spMap (algebraMap K Ω))) B.hom A.hom (spMap (algebraMap K Ω)) :=
    IsPullback.of_hasPullback _ _
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) sqB hA.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) sqB hA.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) sqB hA.geomConnected }
  obtain ⟨I, t, hcov, ha⟩ := exists_affine_loci_of_normChart Ω B hB _ (pull_isLB hN₀ _) (GlobalTheory.T.normChartLineBundle_baseChange_field_extension K Ω A hA N₀ hN₀ hc)
  exact isProjBy_of_cover_baseChange _ A sqB hN₀ t hcov ha
end GlobalTheory.ProjField
end
