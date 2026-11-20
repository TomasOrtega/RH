import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubsingletonOfForallIsMaximalSmulEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBPullIsoOfIsOpenImmersion
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

open CategoryTheory.Limits
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RelAcyclicAmple

open GlobalTheory.AbLaw

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Use `letI : Algebra R K := χ.toAlgebra`. Take `⟨L, φ, -, h2, -, h4, h5, -, h7⟩` from `exists_finite_projective_complex_quasiIso.{0, 0} C n hn hflat hfin`. Establish `h8 : QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).map φ)` using `h7 K`. Establish `h9 : (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj L).ExactAt p` using `(exactAt_iff_of_quasiIsoAt (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).map φ) p).2 hac`. Establish `h10 : Function.Exact ((L.sc p).f.hom.lTensor K) ((L.sc p).g.hom.lTensor K)` using `(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h9`.

Establish `hpt : ∀ z : L.homology p, ∃ r : R, χ r ≠ 0 ∧ r • z = 0`. Introduce `z`. Set `e` to `(L.sc p).moduleCatHomologyIso.toLinearEquiv`. Take `⟨b, hb⟩` from `Submodule.Quotient.mk_surjective _ (e z)`. Use `haveI : Module.Finite R (L.sc p).X₂ := h2 _`.

Use `haveI : Module.Finite R (L.sc p).X₃ := h2 _`. Use `haveI : Module.Projective R (L.sc p).X₂ := h4 _`. Use `haveI : Module.Projective R (L.sc p).X₃ := h4 _`. Take `⟨r, hr, a, ha⟩` from `exists_smul_mem_range_of_exact_fibre K (congrArg ModuleCat.Hom.hom (L.sc p).zero) h10 b.1 b.2`. Use `⟨r, hr, e.injective ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, map_zero, ← hb]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 (show r • b ∈ _ from ⟨a, Subtype.ext ha⟩)`. Set `e` to `(isoOfQuasiIsoAt φ p).toLinearEquiv`. Set `P : PrimeSpectrum R` to `⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩`. Establish `hP : P ∉ Module.support R (C.homology p)`.

Rewrite using `[Module.notMem_support_iff']`. Introduce `z`. Take `⟨r, hr, hz⟩` from `hpt (e.symm z)`. Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Rewrite using `[← e.apply_symm_apply z, ← map_smul, hz, map_zero]`.

Use `haveI := hfin p`. Rewrite `hP` using `[Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists]`. Take `⟨r, hr, hr'⟩` from `hP`. Conclude with `⟨r, hr', Module.mem_annihilator.1 hr⟩`.
-/
theorem exists_smul_homology_eq_zero_of_exactAt_fibre (R : Type) [CommRing R] [IsNoetherianRing R]
    (K : Type) [Field K] (χ : R →+* K) (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (hn : ∀ p, n < p → IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p)) (p : ℕ)
    (hac : (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj C).ExactAt p) :
    ∃ r : R, χ r ≠ 0 ∧ ∀ z : C.homology p, r • z = 0 := by
  letI : Algebra R K := χ.toAlgebra
  obtain ⟨L, φ, -, h2, -, h4, h5, -, h7⟩ :=
    exists_finite_projective_complex_quasiIso.{0, 0} C n hn hflat hfin
  have h8 : QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).map φ) := h7 K
  have h9 : (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj L).ExactAt p :=
    (exactAt_iff_of_quasiIsoAt
      (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).map φ) p).2 hac
  have h10 : Function.Exact ((L.sc p).f.hom.lTensor K) ((L.sc p).g.hom.lTensor K) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h9
  have hpt : ∀ z : L.homology p, ∃ r : R, χ r ≠ 0 ∧ r • z = 0 := by
    intro z
    let e := (L.sc p).moduleCatHomologyIso.toLinearEquiv
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (e z)
    haveI : Module.Finite R (L.sc p).X₂ := h2 _
    haveI : Module.Finite R (L.sc p).X₃ := h2 _
    haveI : Module.Projective R (L.sc p).X₂ := h4 _
    haveI : Module.Projective R (L.sc p).X₃ := h4 _
    obtain ⟨r, hr, a, ha⟩ := exists_smul_mem_range_of_exact_fibre K
      (congrArg ModuleCat.Hom.hom (L.sc p).zero) h10 b.1 b.2
    refine ⟨r, hr, e.injective ?_⟩
    rw [map_smul, map_zero, ← hb]
    exact (Submodule.Quotient.mk_eq_zero _).2 (show r • b ∈ _ from ⟨a, Subtype.ext ha⟩)
  let e := (isoOfQuasiIsoAt φ p).toLinearEquiv
  let P : PrimeSpectrum R := ⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩
  have hP : P ∉ Module.support R (C.homology p) := by
    rw [Module.notMem_support_iff']
    intro z
    obtain ⟨r, hr, hz⟩ := hpt (e.symm z)
    refine ⟨r, hr, ?_⟩
    rw [← e.apply_symm_apply z, ← map_smul, hz, map_zero]
  haveI := hfin p
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hP
  obtain ⟨r, hr, hr'⟩ := hP
  exact ⟨r, hr', Module.mem_annihilator.1 hr⟩

/- English proof (translation)
Use `isProper_of_isProjBy R Y f hproj` as an intermediate fact. Establish `: Y.IsSeparated`. Rewrite using `[Scheme.isSeparated_iff, ← terminal.comp_from f]`. Use `infer_instance`. Establish `hI' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)` using `fun s hs => IsAffineOpen.biInf _ (Finset.finite_toSet _) (by exact_mod_cast hs) fun i _ => hD i`.

Rewrite using `[HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]`. Use `subsingleton_of_forall_isMaximal_smul_eq_zero (R := R) fun P hP => ?_` and prove the remaining obligations. Take `⟨K, _, χ, rfl, HK⟩` from `H P hP`. Establish `h'` using `IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))`. Establish `hac` using `HK κ (fun i => pullback.fst f (Spec.map (CommRingCat.ofHom χ)) ⁻¹ᵁ D i) (fun i => isAffineOpen_preimage_of_isPullback h' (hD i)) (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) n`.

Conclude with `exists_smul_homology_eq_zero_of_exactAt_fibre R K χ _ (Fintype.card κ) (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X f hF hI') (cechLB_homology_finite_of_affine_cover R Y f F κ D hF inferInstance hproj hD hc) (n + 1) (hac.of_iso (cechLBBaseChangeIso hF h' hI').symm)`.
-/
theorem cechLB_exactAt_succ_of_fibres (R : Type) [CommRing R] [IsNoetherianRing R] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) [Flat f] (hproj : IsProjBy f) (F : LB Y) (hF : F.IsLB)
    (H : ∀ P : Ideal R, P.IsMaximal → ∃ (K : Type) (_ : Field K) (χ : R →+* K), RingHom.ker χ = P ∧
      ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (pullback f (Spec.map (CommRingCat.ofHom χ))).Opens),
        (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ n : ℕ,
          (cechLB (pullback.snd f (Spec.map (CommRingCat.ofHom χ)))
            (F.pull (pullback.fst f (Spec.map (CommRingCat.ofHom χ)))) D).ExactAt (n + 1))
    (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (hD : ∀ i, IsAffineOpen (D i))
    (hc : ⨆ i, D i = ⊤) (n : ℕ) : (cechLB f F D).ExactAt (n + 1) := by
  have := isProper_of_isProjBy R Y f hproj
  have : Y.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from f]
    infer_instance
  have hI' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i) := fun s hs =>
    IsAffineOpen.biInf _ (Finset.finite_toSet _) (by exact_mod_cast hs) fun i _ => hD i
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_isMaximal_smul_eq_zero (R := R) fun P hP => ?_
  obtain ⟨K, _, χ, rfl, HK⟩ := H P hP
  have h' := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))
  have hac := HK κ (fun i => pullback.fst f (Spec.map (CommRingCat.ofHom χ)) ⁻¹ᵁ D i)
    (fun i => isAffineOpen_preimage_of_isPullback h' (hD i))
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) n
  exact exists_smul_homology_eq_zero_of_exactAt_fibre R K χ _ (Fintype.card κ)
    (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X f hF hI')
    (cechLB_homology_finite_of_affine_cover R Y f F κ D hF inferInstance hproj hD hc) (n + 1)
    (hac.of_iso (cechLBBaseChangeIso hF h' hI').symm)

/- English proof (translation)
Establish `e (p : ℕ) : (Cube.d (secCube f' M D) p : Cube.Term (secCube f' M D) p → _) = (Cube.d (secCube f M D) p : Cube.Term (secCube f M D) p → _)`. Use function extensionality and compare the values at `fun x => funext fun t => (Cube.d_apply (secCube f' M D) p x t).trans (Cube.d_apply (secCube f M D) p x t).symm`. Use `(cechComplex_exactAt_succ_iff (secCube f M D) n).trans (Iff.trans ?_ (cechComplex_exactAt_succ_iff (secCube f' M D) n).symm)` and prove the remaining obligations. Rewrite using `[e, e]`. Conclude with `Iff.rfl`.
-/
theorem cechLB_exactAt_succ_iff {R R' : Type} [CommRing R] [CommRing R'] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of R)) (f' : Y ⟶ Spec (CommRingCat.of R')) (M : LB Y) {κ : Type}
    [LinearOrder κ] (D : κ → Y.Opens) (n : ℕ) :
    (cechLB f M D).ExactAt (n + 1) ↔ (cechLB f' M D).ExactAt (n + 1) := by
  have e (p : ℕ) : (Cube.d (secCube f' M D) p : Cube.Term (secCube f' M D) p → _) =
      (Cube.d (secCube f M D) p : Cube.Term (secCube f M D) p → _) :=
    funext fun x => funext fun t => (Cube.d_apply (secCube f' M D) p x t).trans
      (Cube.d_apply (secCube f M D) p x t).symm
  refine (cechComplex_exactAt_succ_iff (secCube f M D) n).trans
    (Iff.trans ?_ (cechComplex_exactAt_succ_iff (secCube f' M D) n).symm)
  rw [e, e]
  exact Iff.rfl

/- English proof (translation)
Introduce `AV k _ S p D hS A _ hA L hL hamp U hU κ _ _ W hW hWU n`. Use `hS.isLocallyNoetherian` as an intermediate fact. Use `haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Set `t : Spec (CommRingCat.of Γ(S, U)) ⟶ S` to `hU.fromSpec`. Establish `h : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom t` using `IsPullback.of_hasPullback _ _`.

Take `⟨hproj, hsm, -, -⟩` from `AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S A L hA hL hamp Γ(S, U) t _ _ _ h`. Use `haveI : Flat (pullback.snd A.hom t) := inferInstance`. Establish `hrange : (pullback.fst A.hom t).opensRange = A.hom ⁻¹ᵁ U`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `x ∈ Set.range (pullback.fst A.hom t) ↔ A.hom x ∈ (U : Set S)`.

Rewrite using `[Scheme.Pullback.range_fst, hU.range_fromSpec]`. Both sides reduce to the same expression. Establish `hle : ∀ i, W i ≤ (pullback.fst A.hom t).opensRange` using `fun i => hrange ▸ (le_iSup W i).trans hWU.le`. Take `⟨e⟩` from `cechLB_pull_iso_of_isOpenImmersion k A.left (A.hom ≫ p) L _ (pullback.fst A.hom t) κ W hL hle`. Use `HomologicalComplex.ExactAt.of_iso ?_ e` and prove the remaining obligations.

Use `(cechLB_exactAt_succ_iff (pullback.snd A.hom t) _ _ _ n).1 ?_` and prove the remaining obligations. Use `cechLB_exactAt_succ_of_fibres Γ(S, U) _ (pullback.snd A.hom t) hproj _ (LB.isLB_pull hL _) ?_ κ _ (fun i => (hW i).preimage_of_isOpenImmersion _ (hle i)) ?_ n` and prove the remaining obligations. Introduce `P hP`. Use `letI : Field (Γ(S, U) ⧸ P) := Ideal.Quotient.field P`. Set `χ : Γ(S, U) →+* AlgebraicClosure (Γ(S, U) ⧸ P)` to `(algebraMap (Γ(S, U) ⧸ P) (AlgebraicClosure (Γ(S, U) ⧸ P))).comp (Ideal.Quotient.mk P)`.

Use `⟨AlgebraicClosure (Γ(S, U) ⧸ P), inferInstance, χ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.ker_comp_of_injective _ (algebraMap (Γ(S, U) ⧸ P) _).injective, Ideal.mk_ker]`. Introduce `κ' _ _ D' hD' hc' m`. Use `hA.proper` as an intermediate fact. Set `B` to `(Over.pullback t).obj A`.

Establish `hB : IsAbelianScheme B` using `isAbelianScheme_pullback_obj t A hA`. Establish `: IsProper B.hom` using `hB.proper`. Establish `hLB : (L.pull (pullback.fst A.hom t)).IsLB` using `LB.isLB_pull hL _`. Establish `hampB : Out.RelAmple B (L.pull (pullback.fst A.hom t))` using `AmpleBaseChange.relAmple_of_isPullback hL hamp h`. Set `A₀` to `(Over.pullback (Spec.map (CommRingCat.ofHom χ))).obj B`.

Establish `hA₀ : IsAbelianScheme A₀` using `isAbelianScheme_pullback_obj _ B hB`. Establish `hamp₀` using `AmpleBaseChange.relAmple_of_isPullback hLB hampB (IsPullback.of_hasPullback B.hom (Spec.map (CommRingCat.ofHom χ)))`. Conclude with `AV _ A₀ hA₀ _ (LB.isLB_pull hLB _) hamp₀ ⊤ (isAffineOpen_top _) κ' D' hD' (by rw [hc', Scheme.Hom.preimage_top]) m`. Rewrite using `[← Scheme.Hom.preimage_iSup, hWU, ← hrange]`. Conclude with `Scheme.Hom.preimage_opensRange _`.
-/
theorem isRelAcyclic_of_relAmple : GlobalTheory.Published.AmpleVanishing → ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → IsRelAcyclic (A.hom ≫ p) A.hom L := by
  intro AV k _ S p D hS A _ hA L hL hamp U hU κ _ _ W hW hWU n
  have := hS.isLocallyNoetherian
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let t : Spec (CommRingCat.of Γ(S, U)) ⟶ S := hU.fromSpec
  have h : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom t := IsPullback.of_hasPullback _ _
  obtain ⟨hproj, hsm, -, -⟩ := AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S A L hA hL hamp
    Γ(S, U) t _ _ _ h
  haveI : Flat (pullback.snd A.hom t) := inferInstance
  have hrange : (pullback.fst A.hom t).opensRange = A.hom ⁻¹ᵁ U := by
    ext x
    change x ∈ Set.range (pullback.fst A.hom t) ↔ A.hom x ∈ (U : Set S)
    rw [Scheme.Pullback.range_fst, hU.range_fromSpec]
    rfl
  have hle : ∀ i, W i ≤ (pullback.fst A.hom t).opensRange := fun i =>
    hrange ▸ (le_iSup W i).trans hWU.le
  obtain ⟨e⟩ := cechLB_pull_iso_of_isOpenImmersion k A.left (A.hom ≫ p) L _ (pullback.fst A.hom t) κ W hL hle
  refine HomologicalComplex.ExactAt.of_iso ?_ e
  refine (cechLB_exactAt_succ_iff (pullback.snd A.hom t) _ _ _ n).1 ?_
  refine cechLB_exactAt_succ_of_fibres Γ(S, U) _ (pullback.snd A.hom t) hproj _ (LB.isLB_pull hL _) ?_ κ _
    (fun i => (hW i).preimage_of_isOpenImmersion _ (hle i)) ?_ n
  · intro P hP
    letI : Field (Γ(S, U) ⧸ P) := Ideal.Quotient.field P
    let χ : Γ(S, U) →+* AlgebraicClosure (Γ(S, U) ⧸ P) :=
      (algebraMap (Γ(S, U) ⧸ P) (AlgebraicClosure (Γ(S, U) ⧸ P))).comp (Ideal.Quotient.mk P)
    refine ⟨AlgebraicClosure (Γ(S, U) ⧸ P), inferInstance, χ, ?_, ?_⟩
    · rw [RingHom.ker_comp_of_injective _ (algebraMap (Γ(S, U) ⧸ P) _).injective, Ideal.mk_ker]
    · intro κ' _ _ D' hD' hc' m
      have := hA.proper
      let B := (Over.pullback t).obj A
      have hB : IsAbelianScheme B := isAbelianScheme_pullback_obj t A hA
      have : IsProper B.hom := hB.proper
      have hLB : (L.pull (pullback.fst A.hom t)).IsLB := LB.isLB_pull hL _
      have hampB : Out.RelAmple B (L.pull (pullback.fst A.hom t)) := AmpleBaseChange.relAmple_of_isPullback hL hamp h
      let A₀ := (Over.pullback (Spec.map (CommRingCat.ofHom χ))).obj B
      have hA₀ : IsAbelianScheme A₀ := isAbelianScheme_pullback_obj _ B hB
      have hamp₀ := AmpleBaseChange.relAmple_of_isPullback hLB hampB
        (IsPullback.of_hasPullback B.hom (Spec.map (CommRingCat.ofHom χ)))
      exact AV _ A₀ hA₀ _ (LB.isLB_pull hLB _) hamp₀ ⊤ (isAffineOpen_top _) κ' D' hD'
        (by rw [hc', Scheme.Hom.preimage_top]) m
  · rw [← Scheme.Hom.preimage_iSup, hWU, ← hrange]
    exact Scheme.Hom.preimage_opensRange _

end GlobalTheory.RelAcyclicAmple
