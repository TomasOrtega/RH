import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfAmpleNearFibres
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverIsIsoMorphismRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAmpleLBOfFibres
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSectionLiftFibreNoFirstCohomology
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw TopologicalSpace

namespace GlobalTheory.ProperFinite

/- English proof (translation)
The claim follows from `finite_coh_of_forall_modification f (fun Z _ ι _ => GlobalTheory.ChowLemma.exists_isProjOver_isIso_morphismRestrict R Z (ι ≫ f)) F p`.
-/
theorem finite_coh_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} (f : X ⟶ Sp R)
    [IsProper f] (F : X.Modules) [QCoh.IsFiniteQC F] (p : ℕ) :
    letI := algebraΓOfHom f; Module.Finite R (coh F p) :=
  finite_coh_of_forall_modification f (fun Z _ ι _ => GlobalTheory.ChowLemma.exists_isProjOver_isIso_morphismRestrict R Z (ι ≫ f)) F p

/- English proof (translation)
Set `` to `algebraΓOfHom f`. Establish `: CompactSpace Y` using `QuasiCompact.compactSpace_of_compactSpace f`. Use `isAffineHom_diagonal_of_isSeparated f` as an intermediate fact. Take `⟨m, D, hD, hc⟩` from `exists_fin_affine_cover (X := Y) (V := ⊤) isCompact_univ`. Establish `hD'` using `isAffineOpen_finset_biInf hD`.

Use `Twist.isFiniteQC_twist (F := structureModule Y) hM` as an intermediate fact. Take `⟨K, φ, -, h2, -, h4, -, -, h7⟩` from `GlobalTheory.exists_finite_projective_complex_quasiIso.{0, 0} (cechLB f M D) m (fun p hp => isZero_cechLB_X f M _ (by rw [Fintype.card_fin]; exact hp.le)) (flat_cechLB_X f hM hD') (fun n => by`. Take `⟨e⟩` from `FieldChangeInter.nonempty_coh_equiv f hM hc hD' n`. Use `finite_coh_of_isProper f (twist (structureModule Y) M) n` as an intermediate fact. Conclude with `Module.Finite.equiv e.symm)`.

Conclude with `perf_of_projective_model R Y f M (Fin m) _ K φ hM hc hD' ⟨fun p => ⟨h2 p, h4 p⟩, h7⟩`.
-/
theorem nonempty_perf_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R)
    [IsProper f] [Flat f] {M : LB Y} (hM : M.IsLB) : Nonempty (Perf f M) := by
  let := algebraΓOfHom f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := Y) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have := Twist.isFiniteQC_twist (F := structureModule Y) hM
  obtain ⟨K, φ, -, h2, -, h4, -, -, h7⟩ :=
    GlobalTheory.exists_finite_projective_complex_quasiIso.{0, 0} (cechLB f M D) m
      (fun p hp => isZero_cechLB_X f M _ (by rw [Fintype.card_fin]; exact hp.le))
      (flat_cechLB_X f hM hD') (fun n => by
        obtain ⟨e⟩ := FieldChangeInter.nonempty_coh_equiv f hM hc hD' n
        have := finite_coh_of_isProper f (twist (structureModule Y) M) n
        exact Module.Finite.equiv e.symm)
  exact perf_of_projective_model R Y f M (Fin m) _ K φ hM hc hD' ⟨fun p => ⟨h2 p, h4 p⟩, h7⟩

open FibreLift in

/- English proof (translation)
Take `⟨P⟩` from `nonempty_perf_of_isProper f hM`. Take `⟨r, n, B, hr, hB, hu⟩` from `exists_matrix_basis_ker_of_exact_at_point R K g _ _ _ P.D₀ P.D₁ P.comp (P.exact K g Y₀ π f₀ h hH)`. Take `⟨E, hE⟩` from `P.sec K g Y₀ π f₀ h`. Take `⟨v₀, hv₀⟩` from `E.surjective (SecOnR.topEquiv f₀ _ x₀)`. Take `⟨z, hz, -⟩` from `hu K g hr.isUnit v₀.1 v₀.2`.

Take `⟨c, w, hc, hw⟩` from `exists_common_denominator g hg z`. Establish `hv : g ∘ B.mulVec w = g c • v₀.1`. Rewrite using `[← hz, ← Matrix.mulVec_smul, ← hw]`. Conclude with `funext fun j => RingHom.map_mulVec g _ _ j`. Take `⟨s, hs⟩` from `exists_sec_of_ker P (B.mulVec w) (by rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec])`.

Use `⟨c, (SecOnR.topEquiv f M).symm s, hc, (SecOnR.topEquiv f₀ _).injective ?_⟩` and prove the remaining obligations. Use `Seesaw.sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull M π (P.le i)) (fun y => Seesaw.exists_mem P (π y)) fun i => ?_` and prove the remaining obligations. Establish `e₁` using `Seesaw.loc_comp P h (B.mulVec w) i`. Rewrite `e₁` using `[hv, Seesaw.loc_smul, ← hs]`. Establish `e₂ : Seesaw.loc P π f₀ v₀.1 i = _` using `(hE v₀ i).symm`.

Rewrite `e₁` using `[e₂, hv₀]`. Use `Eq.trans ?_ ((rs_topEquiv_smul f₀ _ (g c) x₀ _ _).trans e₁).symm` and prove the remaining obligations. Use `(rs_rs _ _ _).trans ?_` and prove the remaining obligations. Use `(congrArg (rs Y₀ _) (SecOn.coord_pullLE π le_top _ _)).trans ?_` and prove the remaining obligations. Use `(GlobalTheory.LB.resG_appLE π _ _ _).trans ?_` and prove the remaining obligations.

Use `(GlobalTheory.LB.appLE_resG π inf_le_right _ (s.f (P.ch i))).trans ?_` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.appLE_eq_app]`. Conclude with `(GlobalTheory.LB.appLE_resG π (P.le i) le_rfl _).symm`.
-/
theorem exists_pull_eq_smul {R : Type} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R)
    [IsProper f] [Flat f] {M : LB Y} (hM : M.IsLB) {K : Type} [Field K] (g : R →+* K)
    (hg : ∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a) {Y₀ : Scheme.{0}} {π : Y₀ ⟶ Y} {f₀ : Y₀ ⟶ Sp K}
    (h : IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g))) (hH : FirstCohomologyVanishes (M.pull π))
    (x₀ : SecOnR f₀ (M.pull π) ⊤) :
    ∃ (c : R) (x : SecOnR f M ⊤), g c ≠ 0 ∧ SecOnR.pull M h.w ⊤ ⊤ le_top x = g c • x₀ := by
  obtain ⟨P⟩ := nonempty_perf_of_isProper f hM
  obtain ⟨r, n, B, hr, hB, hu⟩ := exists_matrix_basis_ker_of_exact_at_point R K g _ _ _ P.D₀ P.D₁
    P.comp (P.exact K g Y₀ π f₀ h hH)
  obtain ⟨E, hE⟩ := P.sec K g Y₀ π f₀ h
  obtain ⟨v₀, hv₀⟩ := E.surjective (SecOnR.topEquiv f₀ _ x₀)
  obtain ⟨z, hz, -⟩ := hu K g hr.isUnit v₀.1 v₀.2
  obtain ⟨c, w, hc, hw⟩ := exists_common_denominator g hg z
  have hv : g ∘ B.mulVec w = g c • v₀.1 := by
    rw [← hz, ← Matrix.mulVec_smul, ← hw]
    exact funext fun j => RingHom.map_mulVec g _ _ j
  obtain ⟨s, hs⟩ := exists_sec_of_ker P (B.mulVec w)
    (by rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec])
  refine ⟨c, (SecOnR.topEquiv f M).symm s, hc, (SecOnR.topEquiv f₀ _).injective ?_⟩
  refine Seesaw.sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i)
    (fun i => le_pull M π (P.le i)) (fun y => Seesaw.exists_mem P (π y)) fun i => ?_
  have e₁ := Seesaw.loc_comp P h (B.mulVec w) i
  rw [hv, Seesaw.loc_smul, ← hs] at e₁
  have e₂ : Seesaw.loc P π f₀ v₀.1 i = _ := (hE v₀ i).symm
  rw [e₂, hv₀] at e₁
  refine Eq.trans ?_ ((rs_topEquiv_smul f₀ _ (g c) x₀ _ _).trans e₁).symm
  refine (rs_rs _ _ _).trans ?_
  refine (congrArg (rs Y₀ _) (SecOn.coord_pullLE π le_top _ _)).trans ?_
  refine (GlobalTheory.LB.resG_appLE π _ _ _).trans ?_
  refine (GlobalTheory.LB.appLE_resG π inf_le_right _ (s.f (P.ch i))).trans ?_
  rw [← Scheme.Hom.appLE_eq_app]
  exact (GlobalTheory.LB.appLE_resG π (P.le i) le_rfl _).symm

open AmpleNear in

/- English proof (translation)
Establish `h` using `IsPullback.of_hasPullback B.hom (spMap g)`. Take `⟨d, hd, h0, hv⟩` from `exists_pw_h1Zero K _ _ (LB.isLB_pull hL _) hA`. Establish `hv' : FirstCohomologyVanishes ((pw L d).pull (pullback.fst B.hom (spMap g))) ∧ ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec ((pw L d).pull (pullback.fst B.hom (spMap g)))), ⨆ i, nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i))`. Rewrite using `[pw_pull]`. Take `⟨n, s, hs⟩` from `hv`.

Conclude with `⟨h0, n, s, hs.1, fun i => (hs.2 i).1⟩`. Take `⟨h1, n, s₀, hs₀, hs₀'⟩` from `hv'`. Use `choose c x hc hx using fun i => exists_pull_eq_smul B.hom (isLB_pw hL d) g hg h h1 ((SecOnR.topEquiv _ _).symm (s₀ i))`. Establish `e` using `fun i => preimage_nonzeroLocus_of_pull_eq h.w (pw L d) (x i) _ (hc i) (hx i)`. Simplify using `only [LinearEquiv.apply_symm_apply] at e`.

Take `⟨r, hr, hr'⟩` from `exists_affine_loci_near B.hom (pw L d) (isLB_pw hL d) (fun i => SecOnR.topEquiv B.hom _ (x i)) g _ _ h (by simpa only [e] using hs₀) (by simpa only [e] using hs₀')`. Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Set `j` to `Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r)`. Establish `: IsAffine (Scheme.Opens.toScheme (X` using `Sp R) (PrimeSpectrum.basicOpen r)) := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) r`. Establish `hv : ∃ s : Fin (n + 1) → LB.Sec (pw (L.pull (pullback.fst B.hom j)) d), ⨆ i, nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i))`.

Rewrite using `[← pw_pull]`. Use `⟨fun i => secPull (SecOnR.topEquiv B.hom _ (x i)) _, ?_⟩` and prove the remaining obligations. Simplify using `only [nonzeroLocus_secPull]`. Conclude with `hr' _ _ _ (IsPullback.of_hasPullback B.hom j)`. Take `⟨s, hs, hs'⟩` from `hv`.

Establish `: IsProper ((Over.pullback j).obj B).hom` using `inferInstanceAs (IsProper (pullback.snd B.hom j))`. Conclude with `relAmple_of_affine_loci ((Over.pullback j).obj B) _ (LB.isLB_pull hL _) hd s hs hs'`.
-/
theorem relAmple_near_fibre {R : Type} [CommRing R] [IsNoetherianRing R] (B : Over (Sp R)) [IsProper B.hom]
    [Flat B.hom] {L : LB B.left} (hL : L.IsLB) {K : Type} [Field K] (g : R →+* K)
    (hg : ∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a)
    (hA : RelAmple ((Over.pullback (spMap g)).obj B) (L.pull (pullback.fst B.hom (spMap g)))) :
    ∃ r : R, g r ≠ 0 ∧
      RelAmple ((Over.pullback (Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r))).obj B)
        (L.pull (pullback.fst B.hom (Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r)))) := by
  have h := IsPullback.of_hasPullback B.hom (spMap g)
  obtain ⟨d, hd, h0, hv⟩ := exists_pw_h1Zero K _ _ (LB.isLB_pull hL _) hA
  have hv' : FirstCohomologyVanishes ((pw L d).pull (pullback.fst B.hom (spMap g))) ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec ((pw L d).pull (pullback.fst B.hom (spMap g)))),
      ⨆ i, nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
    rw [pw_pull]
    obtain ⟨n, s, hs⟩ := hv
    exact ⟨h0, n, s, hs.1, fun i => (hs.2 i).1⟩
  obtain ⟨h1, n, s₀, hs₀, hs₀'⟩ := hv'
  choose c x hc hx using fun i => exists_pull_eq_smul B.hom (isLB_pw hL d) g hg h h1
    ((SecOnR.topEquiv _ _).symm (s₀ i))
  have e := fun i => preimage_nonzeroLocus_of_pull_eq h.w (pw L d) (x i) _ (hc i) (hx i)
  simp only [LinearEquiv.apply_symm_apply] at e
  obtain ⟨r, hr, hr'⟩ := exists_affine_loci_near B.hom (pw L d) (isLB_pw hL d)
    (fun i => SecOnR.topEquiv B.hom _ (x i)) g _ _ h (by simpa only [e] using hs₀)
    (by simpa only [e] using hs₀')
  refine ⟨r, hr, ?_⟩
  let j := Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r)
  have : IsAffine (Scheme.Opens.toScheme (X := Sp R) (PrimeSpectrum.basicOpen r)) :=
    IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) r
  have hv : ∃ s : Fin (n + 1) → LB.Sec (pw (L.pull (pullback.fst B.hom j)) d),
      ⨆ i, nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
    rw [← pw_pull]
    refine ⟨fun i => secPull (SecOnR.topEquiv B.hom _ (x i)) _, ?_⟩
    simp only [nonzeroLocus_secPull]
    exact hr' _ _ _ (IsPullback.of_hasPullback B.hom j)
  obtain ⟨s, hs, hs'⟩ := hv
  have : IsProper ((Over.pullback j).obj B).hom := inferInstanceAs (IsProper (pullback.snd B.hom j))
  exact relAmple_of_affine_loci ((Over.pullback j).obj B) _ (LB.isLB_pull hL _) hd s hs hs'

open FibreAmple in

/- English proof (translation)
Use `AmpleLocal.relAmple_of_locally S A M hM inferInstance inferInstance fun s => ?_` and prove the remaining obligations. Take `⟨V, hV, hs, -⟩` from `exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := s) trivial`. Establish `: IsNoetherianRing Γ(S, V)` using `IsLocallyNoetherian.component_noetherian ⟨V, hV⟩`. Set `t : Sp Γ(S, V) ⟶ S` to `hV.fromSpec`. Take `⟨p, hp⟩ : s ∈ Set.range t` from `by rw [hV.range_fromSpec]; exact hs`.

Establish `hB` using `IsPullback.of_hasPullback A.hom t`. Establish `hL` using `pull_isLB hM (pullback.fst A.hom t)`. Use `p.isPrime` as an intermediate fact. Set `g` to `algebraMap Γ(S, V) p.asIdeal.ResidueField`. Set `i` to `algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)`.

Establish `: IsProper (Over.mk (pullback.snd A.hom t)).hom` using `inferInstanceAs (IsProper (pullback.snd A.hom t))`. Establish `: Flat (Over.mk (pullback.snd A.hom t)).hom` using `inferInstanceAs (Flat (pullback.snd A.hom t))`. Establish `: IsProper (Over.mk (pullback.snd A.hom (spMap i ≫ spMap g ≫ t))).hom` using `inferInstanceAs (IsProper (pullback.snd A.hom _))`. Take `⟨r, hr, hA⟩` from `relAmple_near_fibre (Over.mk (pullback.snd A.hom t)) hL g (residueField_fraction p.asIdeal) (relAmple_of_fieldExtension hM i ((IsPullback.of_hasPullback (pullback.snd A.hom t) (spMap g)).paste_horiz hB) (IsPullback.of_hasPullback A.hom _) (pull_isLB hL _) (lbIso_pull_pull hM _ _) …`. Set `D : (Sp Γ(S, V)).Opens` to `PrimeSpectrum.basicOpen r`.

Establish `hD : p ∈ D` using `fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)`. Establish `hrange : Set.range (t ''ᵁ D).ι ⊆ Set.range (D.ι ≫ t)`. Introduce and unpack `_ ⟨⟨_, x, hx, rfl⟩, rfl⟩`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Use `⟨t ''ᵁ D, ⟨p, hD, hp⟩, ?_⟩` and prove the remaining obligations.

Conclude with `relAmple_of_factor hM ((IsPullback.of_hasPullback (pullback.snd A.hom t) D.ι).paste_horiz hB) (isPullback_morphismRestrict A.hom (t ''ᵁ D)).flip (IsOpenImmersion.lift (D.ι ≫ t) _ hrange) (IsOpenImmersion.lift_fac _ _ _) (pull_isLB hL _) (lbIso_pull_pull hM _ _) hA`.
-/
theorem relAmple_of_geometricFibres {S : Scheme.{0}} [IsLocallyNoetherian S] (A : Over S) [IsProper A.hom]
    [Flat A.hom] {M : LB A.left} (hM : M.IsLB)
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), IsAmpleLB (M.pull (pullback.fst A.hom y))) :
    RelAmple A M := by
  refine AmpleLocal.relAmple_of_locally S A M hM inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := s) trivial
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let t : Sp Γ(S, V) ⟶ S := hV.fromSpec
  obtain ⟨p, hp⟩ : s ∈ Set.range t := by rw [hV.range_fromSpec]; exact hs
  have hB := IsPullback.of_hasPullback A.hom t
  have hL := pull_isLB hM (pullback.fst A.hom t)
  have := p.isPrime
  let g := algebraMap Γ(S, V) p.asIdeal.ResidueField
  let i := algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)
  have : IsProper (Over.mk (pullback.snd A.hom t)).hom := inferInstanceAs (IsProper (pullback.snd A.hom t))
  have : Flat (Over.mk (pullback.snd A.hom t)).hom := inferInstanceAs (Flat (pullback.snd A.hom t))
  have : IsProper (Over.mk (pullback.snd A.hom (spMap i ≫ spMap g ≫ t))).hom :=
    inferInstanceAs (IsProper (pullback.snd A.hom _))
  obtain ⟨r, hr, hA⟩ := relAmple_near_fibre (Over.mk (pullback.snd A.hom t)) hL g (residueField_fraction p.asIdeal)
    (relAmple_of_fieldExtension hM i
      ((IsPullback.of_hasPullback (pullback.snd A.hom t) (spMap g)).paste_horiz hB)
      (IsPullback.of_hasPullback A.hom _) (pull_isLB hL _) (lbIso_pull_pull hM _ _)
      ((relAmple_iff_isAmpleLB_of_isAffine _ (pull_isLB hM _)).2 (hfib _ _)))
  let D : (Sp Γ(S, V)).Opens := PrimeSpectrum.basicOpen r
  have hD : p ∈ D := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
  have hrange : Set.range (t ''ᵁ D).ι ⊆ Set.range (D.ι ≫ t) := by
    rintro _ ⟨⟨_, x, hx, rfl⟩, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨t ''ᵁ D, ⟨p, hD, hp⟩, ?_⟩
  exact relAmple_of_factor hM ((IsPullback.of_hasPullback (pullback.snd A.hom t) D.ι).paste_horiz hB)
    (isPullback_morphismRestrict A.hom (t ''ᵁ D)).flip (IsOpenImmersion.lift (D.ι ≫ t) _ hrange)
    (IsOpenImmersion.lift_fac _ _ _) (pull_isLB hL _) (lbIso_pull_pull hM _ _) hA

end GlobalTheory.ProperFinite

/- English proof (translation)
Introduce `S P hS`. Use `P.isAb.proper` as an intermediate fact. Use `P.isAb.smooth` as an intermediate fact. Use `(isProper_and_exists_isAmpleLB_of_isProjOver hS).1` as an intermediate fact. Establish `: IsLocallyNoetherian S` using `LocallyOfFiniteType.isLocallyNoetherian (ShFam.Pad.toSpZ S)`.

Take `⟨M, hM, e⟩` from `CechPic.cls_surj (CechPic.pull (lift (𝟙 P.A) (𝟙 P.A)).left P.c)`. Establish `hA` using `ProperFinite.relAmple_of_geometricFibres P.A hM (DiagonalAmple.isAmpleLB_geometricFibre P hM e)`. Use `DiagonalAmple.isProjOver_of_locally P.A hM (fun y => ?_) hS` and prove the remaining obligations. Take `⟨V, hV, hy, -⟩` from `exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := y) trivial`. Conclude with `⟨V, hV, hy, isAmpleLB_of_relAmple P.A hM hA V hV⟩`.
-/
theorem GlobalTheory.PPAS.isProjOver_of_isProjOver_base : ∀ (S : Scheme.{0}) (P : GlobalTheory.PPAS S),
    IsProjOver (GlobalTheory.ShFam.Pad.toSpZ S) → IsProjOver (GlobalTheory.ShFam.Pad.toSpZ P.A.left) := by
  intro S P hS
  have := P.isAb.proper
  have := P.isAb.smooth
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hS).1
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (ShFam.Pad.toSpZ S)
  obtain ⟨M, hM, e⟩ := CechPic.cls_surj (CechPic.pull (lift (𝟙 P.A) (𝟙 P.A)).left P.c)
  have hA := ProperFinite.relAmple_of_geometricFibres P.A hM (DiagonalAmple.isAmpleLB_geometricFibre P hM e)
  refine DiagonalAmple.isProjOver_of_locally P.A hM (fun y => ?_) hS
  obtain ⟨V, hV, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := y) trivial
  exact ⟨V, hV, hy, isAmpleLB_of_relAmple P.A hM hA V hV⟩
