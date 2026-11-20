import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfFieldPointRelationProperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagChartFramesEigenFramesLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFramesTriangularComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncToroidalGenericBoundaryOfSncBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelPointCarriesUniqueFlagBundlePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsSpecialiseValuationRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelToFlagBundleLocallyQuasiFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoFlagModelFlagBundleOverModuliStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag
open GlobalTheory.FlagMod (FlagCover FlagModel Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.AnForm.R.FinalTheorems (Snc)
open GlobalTheory.Toroidal (gen genι genStr genBd genBdIdeal)
open GlobalTheory.CompHS (Y₀ inc₀ str₀ barComp U₀ IsVariety₀ TorFlag dense_U₀ flagStr flagOpen)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

/- English proof (translation)
Take `⟨φ, k, hz, g, -, -, y, ψ, φ₁, f, t, t', hp, -, hT⟩` from `h`. Rewrite using `[hT.1, hp]`. Simplify using `only [Category.assoc]`.
-/
theorem Rel.over (X : FlagCover Y) (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K] {z : Sp K ⟶ X.YY} {p : Sp K ⟶ C.Y.X}
    (h : Rel X.F C z p) : z ≫ X.π = p ≫ C.π ≫ genι Y := by
  obtain ⟨φ, k, hz, g, -, -, y, ψ, φ₁, f, t, t', hp, -, hT⟩ := h
  rw [hT.1, hp]
  simp only [Category.assoc]

/- English proof (translation)
Establish `hY : ∀ p : Xo.XF c, Y.j p = genι Y (Y.jQ p)` using `fun p => rfl`. Establish `hc : ∀ p : Xo.XF c, ∃ i : Formalism.L2.Pj.Comp Xo c, p ∈ i.1` using `fun p => by`. Take `⟨u, hu, hs⟩` from `exists_mem_irreducibleComponents_subset_of_isIrreducible _ (isIrreducible_singleton (x := p))`. Conclude with `⟨⟨u, hu⟩, hs rfl⟩`. Establish `key : ∀ p : Xo.XF c, Y.jQ p ∈ Set.range (j Z) → p ∈ Z.1` using `fun p hp => by`.

Take `⟨i, hi⟩` from `hc p`. Take `⟨i', -, hu'⟩` from `h3 (Y.jQ p)`. Establish `e : i = Z` using `(hu' i (h2 i p hi)).trans (hu' Z hp).symm`. Conclude with `e ▸ hi`. Take `⟨i, hi, -⟩` from `h3 w`.

Prove the components needed by the constructor for the conclusion. Introduce `hw`. Assume the negation of the conclusion as `hn`. Establish `hiZ : i ≠ Z` using `fun e => hn (e ▸ hi)`. Apply `hw` to reduce the goal to its premises.

Rewrite using `[mem_closure_iff]`. Introduce `O hO hwO`. Use `h1 i` as an intermediate fact. Take `⟨_, hp, ⟨p, rfl⟩⟩` from `Y.jQ_dense.inter_open_nonempty _ ((hO.preimage (genι Y).continuous).inter (j i).isOpenEmbedding.isOpen_range) ⟨w, hwO, hi⟩`. Use `⟨Y.j p, hp.1, p, fun hpZ => ?_, rfl⟩` and prove the remaining obligations.

Take `⟨i', -, hu'⟩` from `h3 (Y.jQ p)`. Conclude with `hiZ ((hu' i hp.2).trans (hu' Z (h2 Z p hpZ)).symm)`. Introduce and unpack `⟨b, rfl⟩ hw`. Use `h1 Z` as an intermediate fact. Rewrite `hw` using `[mem_closure_iff]`.

Take `⟨_, ⟨w', hw', he⟩, ⟨p, hpZ, hp⟩⟩` from `hw (genι Y '' Set.range (j Z)) ((genι Y).isOpenEmbedding.isOpenMap _ (j Z).isOpenEmbedding.isOpen_range) ⟨_, ⟨b, rfl⟩, rfl⟩`. Establish `e : w' = Y.jQ p` using `(genι Y).isOpenEmbedding.injective (he.trans (hp.symm.trans (hY p)))`. Conclude with `hpZ (key p (e ▸ hw'))`.
-/
theorem barComp_iff (Z : Formalism.L2.Pj.Comp Xo c) (B : Formalism.L2.Pj.Comp Xo c → GlobalTheory.ProjVar.Var c.F) (j : ∀ i, (B i).X ⟶ gen Y)
    (h1 : ∀ i, IsOpenImmersion (j i)) (h2 : ∀ i, ∀ p ∈ i.1, Y.jQ p ∈ Set.range (j i))
    (h3 : ∀ z : gen Y, ∃! i, z ∈ Set.range (j i)) (w : gen Y) :
    genι Y w ∈ barComp Y Z ↔ w ∈ Set.range (j Z) := by
  have hY : ∀ p : Xo.XF c, Y.j p = genι Y (Y.jQ p) := fun p => rfl
  have hc : ∀ p : Xo.XF c, ∃ i : Formalism.L2.Pj.Comp Xo c, p ∈ i.1 := fun p => by
    obtain ⟨u, hu, hs⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ (isIrreducible_singleton (x := p))
    exact ⟨⟨u, hu⟩, hs rfl⟩
  have key : ∀ p : Xo.XF c, Y.jQ p ∈ Set.range (j Z) → p ∈ Z.1 := fun p hp => by
    obtain ⟨i, hi⟩ := hc p
    obtain ⟨i', -, hu'⟩ := h3 (Y.jQ p)
    have e : i = Z := (hu' i (h2 i p hi)).trans (hu' Z hp).symm
    exact e ▸ hi
  obtain ⟨i, hi, -⟩ := h3 w
  constructor
  · intro hw
    by_contra hn
    have hiZ : i ≠ Z := fun e => hn (e ▸ hi)
    apply hw
    rw [mem_closure_iff]
    intro O hO hwO
    have := h1 i
    obtain ⟨_, hp, ⟨p, rfl⟩⟩ := Y.jQ_dense.inter_open_nonempty _
      ((hO.preimage (genι Y).continuous).inter (j i).isOpenEmbedding.isOpen_range) ⟨w, hwO, hi⟩
    refine ⟨Y.j p, hp.1, p, fun hpZ => ?_, rfl⟩
    obtain ⟨i', -, hu'⟩ := h3 (Y.jQ p)
    exact hiZ ((hu' i hp.2).trans (hu' Z (h2 Z p hpZ)).symm)
  · rintro ⟨b, rfl⟩ hw
    have := h1 Z
    rw [mem_closure_iff] at hw
    obtain ⟨_, ⟨w', hw', he⟩, ⟨p, hpZ, hp⟩⟩ := hw (genι Y '' Set.range (j Z))
      ((genι Y).isOpenEmbedding.isOpenMap _ (j Z).isOpenEmbedding.isOpen_range) ⟨_, ⟨b, rfl⟩, rfl⟩
    have e : w' = Y.jQ p := (genι Y).isOpenEmbedding.injective (he.trans (hp.symm.trans (hY p)))
    exact hpZ (key p (e ▸ hw'))

/- English proof (translation)
Establish `h : spMap (RingHom.id c.F) = 𝟙 _` using `Spec.map_id _`. Conclude with `((Category.comp_id _).symm.trans (congrArg (genStr Y ≫ ·) h.symm)).trans pullback.condition.symm`.
-/
theorem genStr_eq : genStr Y = genι Y ≫ Y.s := by
  have h : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  exact ((Category.comp_id _).symm.trans (congrArg (genStr Y ≫ ·) h.symm)).trans pullback.condition.symm

/- English proof (translation)
Use `smoothOfRelativeDimension_comp 0 d e g` as an intermediate fact. Rewrite `this` using `[Nat.zero_add]`. Then use the resulting hypothesis.
-/
theorem smooth_iso {A B S : Scheme.{0}} (e : A ⟶ B) [IsIso e] (g : B ⟶ S) {d : ℕ} (h : SmoothOfRelativeDimension d g) :
    SmoothOfRelativeDimension d (e ≫ g) := by
  have := smoothOfRelativeDimension_comp 0 d e g
  rwa [Nat.zero_add] at this

/- English proof (translation)
Rewrite using `[genStr_eq]`. Conclude with `smooth_iso _ _ h`.
-/
theorem smooth_gen {d : ℕ} (h : SmoothOfRelativeDimension d Y.s) : SmoothOfRelativeDimension d (genStr Y) := by
  rw [genStr_eq]
  exact smooth_iso _ _ h

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← he, ← hd]`. Conclude with `smooth_iso _ _ inferInstance`. Take `⟨N, i, hi, hs⟩` from `C.Y.isProjOver`. Conclude with `⟨N, e ≫ i, inferInstance, by rw [Category.assoc, hs, he]⟩`.

Rewrite using `[← he]`. Conclude with `MorphismProperty.of_isPullback (P := @GeometricallyConnected) (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback e (e ≫ C.Y.str) C.Y.str (𝟙 _)) inferInstance`.
-/
theorem isVariety_of_iso (X : FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c) (C : FlagCpt Y (RingEquiv.refl c.F))
    (e : Y₀ X Z ⟶ C.Y.X) [IsIso e] (he : e ≫ C.Y.str = str₀ X Z) (hd : C.Y.dim = GlobalTheory.FlagTan.dimFlag Dw) : IsVariety₀ X Z := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← he, ← hd]
    exact smooth_iso _ _ inferInstance
  · obtain ⟨N, i, hi, hs⟩ := C.Y.isProjOver
    exact ⟨N, e ≫ i, inferInstance, by rw [Category.assoc, hs, he]⟩
  · rw [← he]
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback e (e ≫ C.Y.str) C.Y.str (𝟙 _)) inferInstance

/- English proof (translation)
Rewrite using `[GlobalTheory.FlagDimSum.dim_add_sum_choose, GlobalTheory.FlagTan.dimFlag, Nat.choose_two_right]`.
-/
theorem dim_eq (Dw : Datum H) : Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 = GlobalTheory.FlagTan.dimFlag Dw := by
  rw [GlobalTheory.FlagDimSum.dim_add_sum_choose, GlobalTheory.FlagTan.dimFlag, Nat.choose_two_right]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c T Z hF`. Establish `hsm` using `smooth_gen T.smooth`. Take `⟨B, j, hB, hcov⟩` from `GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) T.Y c.F (RingEquiv.refl _) hF hsm`. Use `(hB Z).1` as an intermediate fact. Take `⟨C, f, hπ, hdim, hl⟩` from `GlobalTheory.FlagBundle.exists_flagCpt T.Y (RingEquiv.refl _) (GlobalTheory.T.snc_toroidalGenericBoundary_of_snc_boundary T.snc) (B Z) (j Z) (hB Z).2.2.1`.

Establish `hJ : ∀ w : gen T.Y, genι T.Y w ∈ barComp T.Y Z ↔ w ∈ Set.range (j Z)` using `barComp_iff Z B j (fun i => (hB i).1) (fun i => (hB i).2.2.2) hcov`. Establish `hX` using `GlobalTheory.T.flagChartFrames_eigenFrames_localRing T.X`. Establish `hC` using `GlobalTheory.T.flagBundlePointFramesTriangular_component C`. Establish `hspid : spMap (RingEquiv.refl c.F).toRingHom = 𝟙 _` using `Spec.map_id _`. Establish `hCs : C.π ≫ genStr T.Y = C.Y.str`.

Use `C.π_str` as an intermediate fact. Rewrite `this` using `[hspid, Category.comp_id]`. Then use the resulting hypothesis. Establish `hps : (C.π ≫ genι T.Y) ≫ T.Y.s = C.Y.str` using `by rw [Category.assoc, ← genStr_eq, hCs]`. Establish `: IsProper T.Y.s` using `projProper _ _ _ T.Y.proj`. Establish `: IsProper ((C.π ≫ genι T.Y) ≫ T.Y.s)` using `by rw [hps]; infer_instance`.

Establish `: IsProper (C.π ≫ genι T.Y)` using `IsProper.of_comp _ T.Y.s`. Establish `hcl : IsClosed (barComp T.Y Z : Set T.Y.X)`. Rewrite using `[← isOpen_compl_iff, isOpen_iff_forall_mem_open]`. Introduce `y hy`. Take `⟨w, rfl⟩ : ∃ w, genι T.Y w = y` from `⟨inv (genι T.Y) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩`.

Take `⟨i, hi, -⟩` from `hcov w`. Use `(hB i).1` as an intermediate fact. Use `⟨genι T.Y '' Set.range (j i), ?_, ?_, ⟨w, hi, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨w', hw', rfl⟩ hb`. Take `⟨i', -, hu'⟩` from `hcov w'`.

Establish `e : i = Z` using `(hu' i hw').trans (hu' Z ((hJ w').1 hb)).symm`. Substitute `e` using the available equality. Conclude with `hy ((hJ w).2 hi)`. Conclude with `(genι T.Y).isOpenEmbedding.isOpenMap _ (j i).isOpenEmbedding.isOpen_range`. Establish `: IsClosedImmersion (inc₀ T.X Z)` using `IsClosedImmersion.of_isPreimmersion _ (by`.

Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hcl.preimage T.X.π.continuous)`. Establish `: IsProper T.X.π` using `T.X.proper`. Establish `: IsNormalScheme T.X.YY` using `GlobalTheory.IsNormalScheme.of_pred T.X.normal`. Establish `: IsLocallyNoetherian T.X.YY` using `LocallyOfFiniteType.isLocallyNoetherian (T.X.π ≫ T.Y.s)`.

Establish `: CompactSpace T.Y.X` using `QuasiCompact.compactSpace_of_compactSpace T.Y.s`. Establish `: CompactSpace T.X.YY` using `QuasiCompact.compactSpace_of_compactSpace T.X.π`. Establish `: CompactSpace (Y₀ T.X Z)` using `QuasiCompact.compactSpace_of_compactSpace (inc₀ T.X Z)`. Establish `: IsNoetherian (Y₀ T.X Z)` using `{}`. Establish `hU : ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ T.X Z), ∃! p : Sp K ⟶ C.Y.X, Rel T.X.F C (z ≫ inc₀ T.X Z) p` using `GlobalTheory.T.flagModel_point_carries_unique_flagBundle_point T.X Z hX C hC (B Z) (j Z) f hπ hl hJ`.

Take `⟨h, hh, hR⟩` from `GlobalTheory.T.exists_hom_of_fieldPoint_relation_proper (Y₀ T.X Z) C.Y.X T.Y.X (inc₀ T.X Z ≫ T.X.π) (C.π ≫ genι T.Y) (fun K _ z w => Rel T.X.F C (z ≫ inc₀ T.X Z) w) (fun K _ z w hw => by rw [← Category.assoc]; exact Rel.over T.X C hw) (fun K _ z => hU K z) (fun K K' _ _ ι z w hw …`. Use `GlobalTheory.T.flagModel_carriesSameFlags_fieldExtension T.X hX C K K' ι _ _ hw` as an intermediate fact. Rewrite using `[← Category.assoc] at this)` and apply the resulting hypothesis. Use the proof step `(fun A _ _ _ u v huv hr => by`. Use `GlobalTheory.T.flagModel_carriesSameFlags_specialise_valuationRing T.X hX C hC A (u ≫ inc₀ T.X Z) v (by simpa only [Category.assoc] using huv) (by simpa only [Category.assoc] using hr)` as an intermediate fact.

Simplify `this)` using `only [Category.assoc]`. Establish `: IsProper (inc₀ T.X Z ≫ T.X.π)` using `inferInstance`. Establish `: IsProper (h ≫ C.π ≫ genι T.Y)` using `by rw [hh]; infer_instance`. Establish `: IsProper h` using `IsProper.of_comp h (C.π ≫ genι T.Y)`. Use `GlobalTheory.T.flagModel_to_flagBundle_locallyQuasiFinite T.flag C hC Z h hR` as an intermediate fact.

Establish `hiso` using `GlobalTheory.T.isIso_flagModel_flagBundle_over_moduli T.X Z hX C hC (B Z) (j Z) f hπ hJ h hU hR`. Establish `hVo : Nonempty (Vo C)`. Use `⟨⟨genericPoint C.Y.X, ?_⟩⟩` and prove the remaining obligations. Use `show C.π (genericPoint C.Y.X) ∈ Set.range T.Y.jQ`. Use `letI := (GlobalTheory.ShFam.constF (RingEquiv.refl c.F) C.Y).toAlgebra`.

Establish `e1` using `Scheme.Hom.comp_apply (GlobalTheory.ShFam.genericPt C.Y) C.π (IsLocalRing.closedPoint C.Y.Fn)`. Establish `e2` using `Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF C.y0) T.Y.jQ (IsLocalRing.closedPoint C.Y.Fn)`. Rewrite `e2` using `[C.y0_x]`. Establish `h1` using `e1.symm.trans e2`. Establish `h2 : (GlobalTheory.ShFam.genericPt C.Y) (IsLocalRing.closedPoint C.Y.Fn) = genericPoint C.Y.X` using `Scheme.fromSpecStalk_closedPoint`.

Rewrite `h1` using `[h2]`. Conclude with `⟨_, h1.symm⟩`. Establish `hpre : (U₀ T.X Z : Set (Y₀ T.X Z)) ⊆ h ⁻¹ᵁ Vo C`. Introduce `y hy`. Use `show C.π (h y) ∈ Set.range T.Y.jQ`.

Establish `e : genι T.Y (C.π (h y)) = T.X.π (inc₀ T.X Z y)`. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hh]`. Take `⟨x, hx⟩ : T.X.π (inc₀ T.X Z y) ∈ Set.range T.Y.j` from `hy`. Use `⟨x, (genι T.Y).isOpenEmbedding.injective ?_⟩` and prove the remaining obligations. Rewrite using `[e, ← hx, Model.j, Scheme.Hom.comp_apply]`.

Establish `: Nonempty (h ⁻¹ᵁ Vo C)`. Take `⟨v⟩` from `hVo`. Conclude with `⟨inv (h ∣_ Vo C) v⟩`. Establish `: IsIntegral (h ⁻¹ᵁ Vo C).toScheme` using `isIntegral_of_isOpenImmersion (h ∣_ Vo C)`. Establish `hirr : IsIrreducible ((h ⁻¹ᵁ Vo C : (Y₀ T.X Z).Opens) : Set (Y₀ T.X Z))`.

Rewrite using `[← Scheme.Opens.range_ι, ← Set.image_univ]`. Conclude with `(IrreducibleSpace.isIrreducible_univ _).image _ (h ⁻¹ᵁ Vo C).ι.continuous.continuousOn`. Establish `hdense : closure ((h ⁻¹ᵁ Vo C : (Y₀ T.X Z).Opens) : Set (Y₀ T.X Z)) = Set.univ` using `((dense_U₀ T.X Z).mono hpre).closure_eq`. Establish `: IrreducibleSpace (Y₀ T.X Z)` using `(irreducibleSpace_def _).2 (by`. Use `hirr.closure` as an intermediate fact.

Rewrite `this` using `[hdense]`. Conclude with `this)`. Establish `: IsIntegral (Y₀ T.X Z)` using `isIntegral_of_irreducibleSpace_of_isReduced _`. Use `C.Y.isNormalScheme` as an intermediate fact. Establish `: IsIso h` using `GlobalTheory.isIso_of_isProper_of_quasiFinite_of_birational h (fun y => inferInstance) (Vo C) hVo`.

Use `isVariety_of_iso T.X Z C h ?_ (by rw [hdim, (hB Z).2.1, dim_eq])` and prove the remaining obligations. Rewrite using `[← hps, ← Category.assoc, hh, Category.assoc]`.
-/
theorem isVariety₀_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → IsVariety₀ T.X Z := by
  intro E _ _ _ H Dw l Xo c T Z hF
  have hsm := smooth_gen T.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) T.Y c.F (RingEquiv.refl _) hF hsm
  have := (hB Z).1
  obtain ⟨C, f, hπ, hdim, hl⟩ := GlobalTheory.FlagBundle.exists_flagCpt T.Y (RingEquiv.refl _) (GlobalTheory.T.snc_toroidalGenericBoundary_of_snc_boundary T.snc) (B Z) (j Z) (hB Z).2.2.1
  have hJ : ∀ w : gen T.Y, genι T.Y w ∈ barComp T.Y Z ↔ w ∈ Set.range (j Z) :=
    barComp_iff Z B j (fun i => (hB i).1) (fun i => (hB i).2.2.2) hcov
  have hX := GlobalTheory.T.flagChartFrames_eigenFrames_localRing T.X
  have hC := GlobalTheory.T.flagBundlePointFramesTriangular_component C

  have hspid : spMap (RingEquiv.refl c.F).toRingHom = 𝟙 _ := Spec.map_id _
  have hCs : C.π ≫ genStr T.Y = C.Y.str := by
    have := C.π_str
    rwa [hspid, Category.comp_id] at this
  have hps : (C.π ≫ genι T.Y) ≫ T.Y.s = C.Y.str := by rw [Category.assoc, ← genStr_eq, hCs]
  have : IsProper T.Y.s := projProper _ _ _ T.Y.proj
  have : IsProper ((C.π ≫ genι T.Y) ≫ T.Y.s) := by rw [hps]; infer_instance
  have : IsProper (C.π ≫ genι T.Y) := IsProper.of_comp _ T.Y.s

  have hcl : IsClosed (barComp T.Y Z : Set T.Y.X) := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨w, rfl⟩ : ∃ w, genι T.Y w = y :=
      ⟨inv (genι T.Y) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    obtain ⟨i, hi, -⟩ := hcov w
    have := (hB i).1
    refine ⟨genι T.Y '' Set.range (j i), ?_, ?_, ⟨w, hi, rfl⟩⟩
    · rintro _ ⟨w', hw', rfl⟩ hb
      obtain ⟨i', -, hu'⟩ := hcov w'
      have e : i = Z := (hu' i hw').trans (hu' Z ((hJ w').1 hb)).symm
      subst e
      exact hy ((hJ w).2 hi)
    · exact (genι T.Y).isOpenEmbedding.isOpenMap _ (j i).isOpenEmbedding.isOpen_range
  have : IsClosedImmersion (inc₀ T.X Z) := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact hcl.preimage T.X.π.continuous)
  have : IsProper T.X.π := T.X.proper
  have : IsNormalScheme T.X.YY := GlobalTheory.IsNormalScheme.of_pred T.X.normal
  have : IsLocallyNoetherian T.X.YY := LocallyOfFiniteType.isLocallyNoetherian (T.X.π ≫ T.Y.s)
  have : CompactSpace T.Y.X := QuasiCompact.compactSpace_of_compactSpace T.Y.s
  have : CompactSpace T.X.YY := QuasiCompact.compactSpace_of_compactSpace T.X.π
  have : CompactSpace (Y₀ T.X Z) := QuasiCompact.compactSpace_of_compactSpace (inc₀ T.X Z)
  have : IsNoetherian (Y₀ T.X Z) := {}
  have hU : ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ T.X Z), ∃! p : Sp K ⟶ C.Y.X, Rel T.X.F C (z ≫ inc₀ T.X Z) p :=
    GlobalTheory.T.flagModel_point_carries_unique_flagBundle_point T.X Z hX C hC (B Z) (j Z) f hπ hl hJ
  obtain ⟨h, hh, hR⟩ := GlobalTheory.T.exists_hom_of_fieldPoint_relation_proper (Y₀ T.X Z) C.Y.X T.Y.X (inc₀ T.X Z ≫ T.X.π) (C.π ≫ genι T.Y)
    (fun K _ z w => Rel T.X.F C (z ≫ inc₀ T.X Z) w)
    (fun K _ z w hw => by rw [← Category.assoc]; exact Rel.over T.X C hw)
    (fun K _ z => hU K z)
    (fun K K' _ _ ι z w hw => by
      have := GlobalTheory.T.flagModel_carriesSameFlags_fieldExtension T.X hX C K K' ι _ _ hw
      rwa [← Category.assoc] at this)
    (fun A _ _ _ u v huv hr => by
      have := GlobalTheory.T.flagModel_carriesSameFlags_specialise_valuationRing T.X hX C hC A (u ≫ inc₀ T.X Z) v (by simpa only [Category.assoc] using huv)
        (by simpa only [Category.assoc] using hr)
      simpa only [Category.assoc] using this)
  have : IsProper (inc₀ T.X Z ≫ T.X.π) := inferInstance
  have : IsProper (h ≫ C.π ≫ genι T.Y) := by rw [hh]; infer_instance
  have : IsProper h := IsProper.of_comp h (C.π ≫ genι T.Y)
  have := GlobalTheory.T.flagModel_to_flagBundle_locallyQuasiFinite T.flag C hC Z h hR
  have hiso := GlobalTheory.T.isIso_flagModel_flagBundle_over_moduli T.X Z hX C hC (B Z) (j Z) f hπ hJ h hU hR
  have hVo : Nonempty (Vo C) := by
    refine ⟨⟨genericPoint C.Y.X, ?_⟩⟩
    show C.π (genericPoint C.Y.X) ∈ Set.range T.Y.jQ
    letI := (GlobalTheory.ShFam.constF (RingEquiv.refl c.F) C.Y).toAlgebra
    have e1 := Scheme.Hom.comp_apply (GlobalTheory.ShFam.genericPt C.Y) C.π (IsLocalRing.closedPoint C.Y.Fn)
    have e2 := Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF C.y0) T.Y.jQ (IsLocalRing.closedPoint C.Y.Fn)
    rw [C.y0_x] at e2
    have h1 := e1.symm.trans e2
    have h2 : (GlobalTheory.ShFam.genericPt C.Y) (IsLocalRing.closedPoint C.Y.Fn) = genericPoint C.Y.X :=
      Scheme.fromSpecStalk_closedPoint
    rw [h2] at h1
    exact ⟨_, h1.symm⟩
  have hpre : (U₀ T.X Z : Set (Y₀ T.X Z)) ⊆ h ⁻¹ᵁ Vo C := by
    intro y hy
    show C.π (h y) ∈ Set.range T.Y.jQ
    have e : genι T.Y (C.π (h y)) = T.X.π (inc₀ T.X Z y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hh]
    obtain ⟨x, hx⟩ : T.X.π (inc₀ T.X Z y) ∈ Set.range T.Y.j := hy
    refine ⟨x, (genι T.Y).isOpenEmbedding.injective ?_⟩
    rw [e, ← hx, Model.j, Scheme.Hom.comp_apply]
  have : Nonempty (h ⁻¹ᵁ Vo C) := by
    obtain ⟨v⟩ := hVo
    exact ⟨inv (h ∣_ Vo C) v⟩
  have : IsIntegral (h ⁻¹ᵁ Vo C).toScheme := isIntegral_of_isOpenImmersion (h ∣_ Vo C)
  have hirr : IsIrreducible ((h ⁻¹ᵁ Vo C : (Y₀ T.X Z).Opens) : Set (Y₀ T.X Z)) := by
    rw [← Scheme.Opens.range_ι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (h ⁻¹ᵁ Vo C).ι.continuous.continuousOn
  have hdense : closure ((h ⁻¹ᵁ Vo C : (Y₀ T.X Z).Opens) : Set (Y₀ T.X Z)) = Set.univ :=
    ((dense_U₀ T.X Z).mono hpre).closure_eq
  have : IrreducibleSpace (Y₀ T.X Z) := (irreducibleSpace_def _).2 (by
    have := hirr.closure
    rw [hdense] at this
    exact this)
  have : IsIntegral (Y₀ T.X Z) := isIntegral_of_irreducibleSpace_of_isReduced _
  have := C.Y.isNormalScheme
  have : IsIso h := GlobalTheory.isIso_of_isProper_of_quasiFinite_of_birational h
    (fun y => inferInstance) (Vo C) hVo
  refine isVariety_of_iso T.X Z C h ?_ (by rw [hdim, (hB Z).2.1, dim_eq])
  rw [← hps, ← Category.assoc, hh, Category.assoc]

end GlobalTheory.VarFlag
