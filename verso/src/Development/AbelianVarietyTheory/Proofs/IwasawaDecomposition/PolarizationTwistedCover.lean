import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalizationAwayModelStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Models

noncomputable section

namespace GlobalTheory.TorRef

/- English proof (translation)
Use `letI := f.toAlgebra`. Use `haveI : Algebra.FiniteType A S := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) S`. Conclude with `Algebra.FiniteType.trans hA ‹_›`.
-/
theorem finiteType_int_of_away {A S : Type} [CommRing A] [CommRing S] (f : A →+* S) (a : A)
    (hA : Algebra.FiniteType ℤ A) (h : @IsLocalization.Away A _ a S _ f.toAlgebra) : Algebra.FiniteType ℤ S := by
  letI := f.toAlgebra
  haveI : Algebra.FiniteType A S := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) S
  exact Algebra.FiniteType.trans hA ‹_›

/- English proof (translation)
Take `⟨⟨_, _⟩, -, hfr⟩` from `hY`. Take `⟨⟨_, _⟩, -, hfr'⟩` from `hW`. Use `letI := β.toAlgebra`. Use `letI := β'.toAlgebra`. Take `⟨-, -, -, -, -, hdom, -⟩` from `genericPart_dense_proOpen O c.F Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense`.

Take `⟨-, -, hsep, -⟩` from `genericPart_dense_proOpen O' c.F W.X (Xo.XF c) W.s W.jQ W.flat W.proj W.jQ_open W.jQ_dense`. Use `haveI := GlobalTheory.Coisotropic.isReduced_of_isNormalScheme Y.normal`. Use `haveI : IsDominant Y.j := hdom`. Use `haveI : IsSeparated W.s := inferInstance`. Conclude with `ext_of_isDominant_of_isSeparated W.s hs Y.j hj`.
-/
theorem eq_of_comp_j {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    (Y : Model Xo c β) (W : Model Xo c β') (f g : Y.X ⟶ W.X) (hY : IsDedFrac β) (hW : IsDedFrac β')
    (hs : f ≫ W.s = g ≫ W.s) (hj : Y.j ≫ f = Y.j ≫ g) : f = g := by
  obtain ⟨⟨_, _⟩, -, hfr⟩ := hY
  obtain ⟨⟨_, _⟩, -, hfr'⟩ := hW
  letI := β.toAlgebra
  letI := β'.toAlgebra
  obtain ⟨-, -, -, -, -, hdom, -⟩ :=
    genericPart_dense_proOpen O c.F Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense
  obtain ⟨-, -, hsep, -⟩ :=
    genericPart_dense_proOpen O' c.F W.X (Xo.XF c) W.s W.jQ W.flat W.proj W.jQ_open W.jQ_dense
  haveI := GlobalTheory.Coisotropic.isReduced_of_isNormalScheme Y.normal
  haveI : IsDominant Y.j := hdom
  haveI : IsSeparated W.s := inferInstance
  exact ext_of_isDominant_of_isSeparated W.s hs Y.j hj

/- English proof (translation)
Establish `hsub : Set.range (pullback.snd ui uj) ⊆ Set.range v`. Introduce and unpack `_ ⟨p, rfl⟩`. Apply `hr` to reduce the goal to its premises. Use `⟨pullback.fst ui uj p, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]`.

Establish `hq : IsOpenImmersion.lift v (pullback.snd ui uj) hsub ≫ v = pullback.snd ui uj` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hq' : IsOpenImmersion.lift v (pullback.snd ui uj) hsub ≫ π = pullback.fst ui uj`. Rewrite using `[← cancel_mono ui, Category.assoc, h, reassoc_of% hq, pullback.condition]`. Rewrite using `[← hq, ← hq', Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hI]`.
-/
theorem comap_fst_eq_comap_snd {X Y P Z : Scheme.{0}} (ui : X ⟶ Z) (uj : Y ⟶ Z) (v : P ⟶ Y) (π : P ⟶ X)
    [IsOpenImmersion ui] [IsOpenImmersion v] (Ii : X.IdealSheafData) (Ij : Y.IdealSheafData) (h : π ≫ ui = v ≫ uj)
    (hr : ∀ y, uj y ∈ Set.range ui → y ∈ Set.range v) (hI : Ij.comap v = Ii.comap π) :
    Ii.comap (pullback.fst ui uj) = Ij.comap (pullback.snd ui uj) := by
  have hsub : Set.range (pullback.snd ui uj) ⊆ Set.range v := by
    rintro _ ⟨p, rfl⟩
    apply hr
    refine ⟨pullback.fst ui uj p, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hq : IsOpenImmersion.lift v (pullback.snd ui uj) hsub ≫ v = pullback.snd ui uj :=
    IsOpenImmersion.lift_fac _ _ _
  have hq' : IsOpenImmersion.lift v (pullback.snd ui uj) hsub ≫ π = pullback.fst ui uj := by
    rw [← cancel_mono ui, Category.assoc, h, reassoc_of% hq, pullback.condition]
  rw [← hq, ← hq', Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hI]

/- English proof (translation)
Introduce `hPM E _ _ _ H D l Xo c I _ R _ a b ω Z C u φ m BD htw hcov hchart hpol i j`. Take `⟨hZd, hR, -⟩` from `hcov`. Take `⟨hdi, hωi, hloci⟩` from `hR i`. Take `⟨hdj, hωj, hlocj⟩` from `hR j`. Establish `hai : a i ≠ 0`.

Introduce and unpack `h0`. Use `letI := (b i).toAlgebra`. Use `haveI := hloci`. Use `haveI : Subsingleton (R i) := IsLocalization.subsingleton (M := Submonoid.powers (a i)) ⟨1, by simp [h0]⟩`. Take `⟨⟨hdom, -⟩, -⟩` from `hdi`.

Conclude with `not_subsingleton (R i) ‹_›`. Establish `hne : ω j (b j (a i)) ≠ 0`. Rewrite using `[← RingHom.comp_apply, hωj]`. Introduce `h0`. Conclude with `hai (by simpa using h0)`.

Take `⟨R', _, e, ω', C', v, hloc', hωe, hd', hv, hvs, hrange, hvj, ⟨mv⟩⟩` from `GlobalTheory.T.exists_localization_away_model (C j) (b j (a i)) hdj hne`. Use `c.fin` as an intermediate fact. Establish `: NumberField c.F` using `{}`. Establish `hFT : Algebra.FiniteType ℤ R'` using `finiteType_int_of_away e (b j (a i)) (finiteType_int_of_away (b j) (a j) inferInstance hlocj) hloc'`. Establish `hu : IsUnit ((e.comp (b j)) (a i))`.

Use `letI := e.toAlgebra`. Use `haveI := hloc'`. Conclude with `IsLocalization.Away.algebraMap_isUnit (b j (a i))`. Use `letI := (b i).toAlgebra`. Use `haveI := hloci`.

Set `b' : R i →+* R'` to `IsLocalization.Away.lift (a i) hu`. Establish `hb' : b'.comp (b i) = e.comp (b j)` using `IsLocalization.Away.lift_comp (a i) hu`. Establish `hbi : IsOpenImmersion (spMap (b i))` using `IsOpenImmersion.of_isLocalization (R := 𝓞 c.F) (S := R i) (a i)`. Establish `hZi : (C i).j ≫ u i = Z.j` using `(hchart i).2.2.2.1`. Establish `hZj : (C j).j ≫ u j = Z.j` using `(hchart j).2.2.2.1`.

Establish `hsi : u i ≫ Z.s = (C i).s ≫ spMap (b i)` using `(hchart i).2.1`. Establish `hsj : u j ≫ Z.s = (C j).s ≫ spMap (b j)` using `(hchart j).2.1`. Establish `hspm : spMap b' ≫ spMap (b i) = spMap e ≫ spMap (b j)`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hb']`. Establish `hjs : 𝟙 _ ≫ (C i).j ≫ (C i).s = C'.j ≫ C'.s ≫ spMap b'`.

Rewrite using `[Category.id_comp, ← cancel_mono (spMap (b i))]`. Simplify using `only [Category.assoc]`. Rewrite using `[hspm, ← reassoc_of% hvs, ← hsj, ← hsi, reassoc_of% hvj, reassoc_of% hZj, reassoc_of% hZi]`. Take `⟨ν₀, -⟩` from `GlobalTheory.LevelCover.sab_cancel (C i).m0.toSABMap C'.m0.toSABMap (𝟙 _) (Category.id_comp _)`. Establish `hcpt : CompactSpace C'.X`.

Take `⟨⟨_, _⟩, -, hfr⟩` from `hd'`. Use `letI := ω'.toAlgebra`. Conclude with `(genericPart_dense_proOpen R' c.F C'.X (Xo.XF c) C'.s C'.jQ C'.flat C'.proj C'.jQ_open C'.jQ_dense).2.1`. Use `haveI := hv`. Establish `hkr : (BD j).KeepsRegular v` using `(BD j).keepsRegular_of_flat v`.

Establish `hpol' : IsPol φ m C' ((BD j).pull v hkr)`. Use `⟨isPhiDiv_pull E H D l Xo c (R j) R' (ω j) ω' (C j) C' v φ (BD j) hkr hvj ⟨mv⟩ (hpol j).1, ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.T.polarization_open_immersion (C j) C' v (BD j) ((BD j).pull v hkr) m hv ⟨mv⟩ ((BD j).idealSheaf_pull v hkr).symm).2 (GlobalTheory.IsAmpleLB.pull_of_isOpenImmersion (hpol j).2 v)`. Take `⟨π, hπ, -, -, hjπ, -, hBD⟩` from `hPM E H D l l Xo Xo c c (R i) R' (ω i) ω' (C i) C' (BD i) ((BD j).pull v hkr) φ m b' (RingEquiv.refl _) (𝟙 _) ((TwMap.reflEquiv _ _ _).symm ν₀) hdi hd' hFT htw rfl (hpol i) hpol' hjs`. Establish `hag : π ≫ u i = v ≫ u j`.

Use `eq_of_comp_j C' Z _ _ hd' hZd ?_ ?_` and prove the remaining obligations. Simplify using `only [Category.assoc]`. Rewrite using `[hsi, reassoc_of% hπ, hspm, ← reassoc_of% hvs, hsj]`. Rewrite using `[reassoc_of% hjπ, hZi, reassoc_of% hvj, hZj]`. Use `haveI := (hchart i).1`.

Use `comap_fst_eq_comap_snd (u i) (u j) v π (BD i).idealSheaf (BD j).idealSheaf hag ?_ ?_` and prove the remaining obligations. Introduce `y hy`. Rewrite using `[hrange]`. Rewrite `hy` using `[(hchart i).2.2.1]`. Establish `e1 : Z.s (u j y) = spMap (b j) ((C j).s y)`.

Rewrite using `[← Scheme.Hom.comp_apply, hsj, Scheme.Hom.comp_apply]`. Use `show b j (a i) ∉ ((C j).s y).asIdeal`. Establish `hy' : a i ∉ (Z.s (u j y)).asIdeal` using `hy`. Rewrite `hy'` using `[e1]`. Conclude with `hy'`.

Rewrite using `[← (BD j).idealSheaf_pull v hkr, hBD]`.
-/
theorem charts_divisor_compat : PolMapSt → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)] {a : I → 𝓞 c.F} {b : ∀ i, 𝓞 c.F →+* R i} {ω : ∀ i, R i →+* c.F} (Z : GMod Xo c) (C : ∀ i, Model Xo c (ω i)) (u : ∀ i, (C i).X ⟶ Z.X) (φ : InvFun (𝓞 E)) (m : ℕ) (BD : ∀ i, EffCartierData (C i).X), IsTwInv H φ → IsCover (algebraMap (𝓞 c.F) c.F) R a b ω → (∀ i, IsChartOf Z (C i) (a i) (b i) (u i)) → (∀ i, IsPol φ m (C i) (BD i)) → ∀ i j, (BD i).idealSheaf.comap (pullback.fst (u i) (u j)) = (BD j).idealSheaf.comap (pullback.snd (u i) (u j)) := by
  intro hPM E _ _ _ H D l Xo c I _ R _ a b ω Z C u φ m BD htw hcov hchart hpol i j
  obtain ⟨hZd, hR, -⟩ := hcov
  obtain ⟨hdi, hωi, hloci⟩ := hR i
  obtain ⟨hdj, hωj, hlocj⟩ := hR j
  have hai : a i ≠ 0 := by
    rintro h0
    letI := (b i).toAlgebra
    haveI := hloci
    haveI : Subsingleton (R i) := IsLocalization.subsingleton (M := Submonoid.powers (a i)) ⟨1, by simp [h0]⟩
    obtain ⟨⟨hdom, -⟩, -⟩ := hdi
    exact not_subsingleton (R i) ‹_›
  have hne : ω j (b j (a i)) ≠ 0 := by
    rw [← RingHom.comp_apply, hωj]
    intro h0
    exact hai (by simpa using h0)
  obtain ⟨R', _, e, ω', C', v, hloc', hωe, hd', hv, hvs, hrange, hvj, ⟨mv⟩⟩ := GlobalTheory.T.exists_localization_away_model (C j) (b j (a i)) hdj hne
  have := c.fin
  have : NumberField c.F := {}
  have hFT : Algebra.FiniteType ℤ R' :=
    finiteType_int_of_away e (b j (a i))
      (finiteType_int_of_away (b j) (a j) inferInstance hlocj) hloc'
  have hu : IsUnit ((e.comp (b j)) (a i)) := by
    letI := e.toAlgebra
    haveI := hloc'
    exact IsLocalization.Away.algebraMap_isUnit (b j (a i))
  letI := (b i).toAlgebra
  haveI := hloci
  let b' : R i →+* R' := IsLocalization.Away.lift (a i) hu
  have hb' : b'.comp (b i) = e.comp (b j) := IsLocalization.Away.lift_comp (a i) hu
  have hbi : IsOpenImmersion (spMap (b i)) := IsOpenImmersion.of_isLocalization (R := 𝓞 c.F) (S := R i) (a i)
  have hZi : (C i).j ≫ u i = Z.j := (hchart i).2.2.2.1
  have hZj : (C j).j ≫ u j = Z.j := (hchart j).2.2.2.1
  have hsi : u i ≫ Z.s = (C i).s ≫ spMap (b i) := (hchart i).2.1
  have hsj : u j ≫ Z.s = (C j).s ≫ spMap (b j) := (hchart j).2.1
  have hspm : spMap b' ≫ spMap (b i) = spMap e ≫ spMap (b j) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hb']
  have hjs : 𝟙 _ ≫ (C i).j ≫ (C i).s = C'.j ≫ C'.s ≫ spMap b' := by
    rw [Category.id_comp, ← cancel_mono (spMap (b i))]
    simp only [Category.assoc]
    rw [hspm, ← reassoc_of% hvs, ← hsj, ← hsi, reassoc_of% hvj, reassoc_of% hZj, reassoc_of% hZi]
  obtain ⟨ν₀, -⟩ := GlobalTheory.LevelCover.sab_cancel (C i).m0.toSABMap C'.m0.toSABMap (𝟙 _) (Category.id_comp _)
  have hcpt : CompactSpace C'.X := by
    obtain ⟨⟨_, _⟩, -, hfr⟩ := hd'
    letI := ω'.toAlgebra
    exact (genericPart_dense_proOpen R' c.F C'.X (Xo.XF c) C'.s C'.jQ C'.flat C'.proj C'.jQ_open C'.jQ_dense).2.1
  haveI := hv
  have hkr : (BD j).KeepsRegular v := (BD j).keepsRegular_of_flat v
  have hpol' : IsPol φ m C' ((BD j).pull v hkr) := by
    refine ⟨isPhiDiv_pull E H D l Xo c (R j) R' (ω j) ω' (C j) C' v φ (BD j) hkr hvj ⟨mv⟩ (hpol j).1, ?_⟩
    exact (GlobalTheory.T.polarization_open_immersion (C j) C' v (BD j) ((BD j).pull v hkr) m hv ⟨mv⟩ ((BD j).idealSheaf_pull v hkr).symm).2
      (GlobalTheory.IsAmpleLB.pull_of_isOpenImmersion (hpol j).2 v)
  obtain ⟨π, hπ, -, -, hjπ, -, hBD⟩ := hPM E H D l l Xo Xo c c (R i) R' (ω i) ω' (C i) C' (BD i) ((BD j).pull v hkr) φ m
    b' (RingEquiv.refl _) (𝟙 _) ((TwMap.reflEquiv _ _ _).symm ν₀) hdi hd' hFT htw rfl (hpol i) hpol' hjs
  have hag : π ≫ u i = v ≫ u j := by
    refine eq_of_comp_j C' Z _ _ hd' hZd ?_ ?_
    · simp only [Category.assoc]
      rw [hsi, reassoc_of% hπ, hspm, ← reassoc_of% hvs, hsj]
    · rw [reassoc_of% hjπ, hZi, reassoc_of% hvj, hZj]
  haveI := (hchart i).1
  refine comap_fst_eq_comap_snd (u i) (u j) v π (BD i).idealSheaf (BD j).idealSheaf hag ?_ ?_
  · intro y hy
    rw [hrange]
    rw [(hchart i).2.2.1] at hy
    have e1 : Z.s (u j y) = spMap (b j) ((C j).s y) := by
      rw [← Scheme.Hom.comp_apply, hsj, Scheme.Hom.comp_apply]
    show b j (a i) ∉ ((C j).s y).asIdeal
    have hy' : a i ∉ (Z.s (u j y)).asIdeal := hy
    rw [e1] at hy'
    exact hy'
  · rw [← (BD j).idealSheaf_pull v hkr, hBD]

end GlobalTheory.TorRef
