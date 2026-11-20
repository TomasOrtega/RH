import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsTwoPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjectiveCoordinateRepresentationClosedSubschStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FibreEmbed

open GlobalTheory.AmpleSpan GlobalTheory.SegreCoord GlobalTheory.ProjSpace GlobalTheory.Cartier TopologicalSpace

/- English proof (translation)
Take `⟨P', g, hg, -, -, w⟩` from `hB S _ x P`. Establish `h : IsPullback (snd (Over.mk x) P.A).left (fst (Over.mk x) P.A).left P.A.hom x` using `(IsPullback.of_hasPullback x P.A.hom).flip`. Set `e` to `h.isoIsPullback _ _ hg`. Establish `he : e.hom ≫ g = (snd (Over.mk x) P.A).left` using `h.isoIsPullback_hom_fst _ _ hg`. Establish `he' : e.hom ≫ P'.A.hom = (fst (Over.mk x) P.A).left` using `h.isoIsPullback_hom_snd _ _ hg`.

Establish `haff : IsAffine (Over.mk x).left` using `inferInstanceAs (IsAffine (Sp K))`. Establish `sq : IsPullback e.hom (fst (Over.mk x) P.A).left P'.A.hom ((𝟙 (Sp K) ≫ (Sp K).topIso.inv) ≫ Scheme.Opens.ι (⊤ : (Sp K).Opens))`. Rewrite using `[comp_topIso_inv_ι]`. Conclude with `@IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance (IsIso.id (Sp K)) ⟨he'.trans (Category.comp_id _).symm⟩`. Take `⟨M, s, hs⟩` from `exists_embedsBy_of_isPullback P'.A P'.isLB (hA _ P' N hN).2 (isAffineOpen_top _) sq (K := Fin 1) (ε := fun _ => (N : ℤ)) (by simp)`.

Take `⟨w', hw'⟩` from `LBIso.symm w`. Establish `hP` using `DVR.linComb_isLB P'.L P'.isLB (K := Fin 1) (fun _ => e.hom) (fun _ => (N : ℤ))`. Establish `hQ : (Out.LPow P.A P.L N (Over.mk x)).IsLB` using `DVR.linComb_isLB P.L P.isLB _ _`. Take `⟨W, hW⟩ : LBIso (Out.LPow P.A P.L N (Over.mk x)) ((LB.LinComb P'.L (K` from `Fin 1) (fun _ => e.hom) (fun _ => (N : ℤ))).pull (𝟙 _)) := LBIso.chartPull (chartPullSame P.L _ _ _ (𝟙 _) fun _ => he.symm.trans (Category.id_comp _).symm) (Geo.Tor.chartPullPull _ _ _ rfl) (LBIso.symm (iso_linComb ((isGen_iff w').1 hw') (fun _ : Fin 1 => e.hom) (fun _ => (N : ℤ) …`. Use `choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hQ (s i)`.

Establish `hs₂ : EmbedsBy (fst (Over.mk x) P.A).left s'`. Use `hs.pull (ψ := 𝟙 _) (g := 𝟙 _) IsPullback.of_id_fst fun y => ?_` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_chart hP y`. Take `⟨k, hk⟩` from `exists_chart hQ y`. Use `⟨j, k, hj, hk, gw W (𝟙 _) y j k, fun i => ?_⟩` and prove the remaining obligations.

Use `hs' i _ (𝟙 _) y j k hj hk` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Then use the resulting hypothesis. Use `P.isAb.proper` as an intermediate fact. Establish `: UniversallyClosed (fst (Over.mk x) P.A).left` using `MorphismProperty.of_isPullback (P := @UniversallyClosed) h inferInstance`. Conclude with `hs₂.of_inSpan fun j => (inSpan_iff_mem_span P.A t _).2 (by rw [ht]; trivial)`.
-/
theorem embedsBy_fibre (hA : Out.AmpleSt) (hB : Out.PolBaseChangeSt) {S : Scheme.{0}} (P : Out.PolAV S) {K : Type}
    [Field K] (x : Sp K ⟶ S) {N : ℕ} (hN : 4 ≤ N) {I : Type} [Fintype I]
    (t : I → LB.Sec (Out.LPow P.A P.L N (Over.mk x)))
    (ht : Submodule.span Γ((Over.mk x).left, ⊤)
      (Set.range fun a => (Out.SecM.ofSec P.A (t a) : Out.SecM P.A P.L N (Over.mk x))) = ⊤) :
    EmbedsBy (fst (Over.mk x) P.A).left t := by
  obtain ⟨P', g, hg, -, -, w⟩ := hB S _ x P
  have h : IsPullback (snd (Over.mk x) P.A).left (fst (Over.mk x) P.A).left P.A.hom x :=
    (IsPullback.of_hasPullback x P.A.hom).flip
  let e := h.isoIsPullback _ _ hg
  have he : e.hom ≫ g = (snd (Over.mk x) P.A).left := h.isoIsPullback_hom_fst _ _ hg
  have he' : e.hom ≫ P'.A.hom = (fst (Over.mk x) P.A).left := h.isoIsPullback_hom_snd _ _ hg
  have haff : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Sp K))
  have sq : IsPullback e.hom (fst (Over.mk x) P.A).left P'.A.hom
      ((𝟙 (Sp K) ≫ (Sp K).topIso.inv) ≫ Scheme.Opens.ι (⊤ : (Sp K).Opens)) := by
    rw [comp_topIso_inv_ι]
    exact @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance (IsIso.id (Sp K))
      ⟨he'.trans (Category.comp_id _).symm⟩
  obtain ⟨M, s, hs⟩ := exists_embedsBy_of_isPullback P'.A P'.isLB (hA _ P' N hN).2 (isAffineOpen_top _) sq
    (K := Fin 1) (ε := fun _ => (N : ℤ)) (by simp)
  obtain ⟨w', hw'⟩ := LBIso.symm w
  have hP := DVR.linComb_isLB P'.L P'.isLB (K := Fin 1) (fun _ => e.hom) (fun _ => (N : ℤ))
  have hQ : (Out.LPow P.A P.L N (Over.mk x)).IsLB := DVR.linComb_isLB P.L P.isLB _ _
  obtain ⟨W, hW⟩ : LBIso (Out.LPow P.A P.L N (Over.mk x))
      ((LB.LinComb P'.L (K := Fin 1) (fun _ => e.hom) (fun _ => (N : ℤ))).pull (𝟙 _)) :=
    LBIso.chartPull (chartPullSame P.L _ _ _ (𝟙 _) fun _ => he.symm.trans (Category.id_comp _).symm)
      (Geo.Tor.chartPullPull _ _ _ rfl)
      (LBIso.symm (iso_linComb ((isGen_iff w').1 hw') (fun _ : Fin 1 => e.hom) (fun _ => (N : ℤ))))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hQ (s i)
  have hs₂ : EmbedsBy (fst (Over.mk x) P.A).left s' := by
    refine hs.pull (ψ := 𝟙 _) (g := 𝟙 _) IsPullback.of_id_fst fun y => ?_
    obtain ⟨j, hj⟩ := exists_chart hP y
    obtain ⟨k, hk⟩ := exists_chart hQ y
    refine ⟨j, k, hj, hk, gw W (𝟙 _) y j k, fun i => ?_⟩
    have := hs' i _ (𝟙 _) y j k hj hk
    rwa [Category.id_comp] at this
  have := P.isAb.proper
  have : UniversallyClosed (fst (Over.mk x) P.A).left :=
    MorphismProperty.of_isPullback (P := @UniversallyClosed) h inferInstance
  exact hs₂.of_inSpan fun j => (inSpan_iff_mem_span P.A t _).2 (by rw [ht]; trivial)

variable {X : Scheme.{0}} {A B : LB X} {σ : Type} {a : σ → A.Sec} {b : σ → B.Sec} {T : Type} [CommRing T]
  {x : Sp T ⟶ X} {v : σ → T}

/- English proof (translation)
Establish `hm : x y ∈ B.U p ⊓ A.U q` using `⟨hp, hq⟩`. Use `⟨gm x y (B.U p ⊓ A.U q) (w.s (p, q)), fun i => ?_⟩` and prove the remaining obligations. Conclude with `(gs_res x y _ hm _).symm.trans ((congrArg (gs x y _) (hw i (p, q))).trans ((gs_mul x y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit x y _ hm _) (gs_res x y _ hm _))))`.
-/
theorem gs_of_secMaps {w : LB.Iso A B} (hw : ∀ i, SecMaps w (a i) (b i)) (y : Sp T) {p : B.ι} {q : A.ι}
    (hp : x y ∈ B.U p) (hq : x y ∈ A.U q) :
    ∃ u : ((Sp T).presheaf.stalk y)ˣ, ∀ i, gs x y _ ((b i).f p) = u * gs x y _ ((a i).f q) := by
  have hm : x y ∈ B.U p ⊓ A.U q := ⟨hp, hq⟩
  refine ⟨gm x y (B.U p ⊓ A.U q) (w.s (p, q)), fun i => ?_⟩
  exact (gs_res x y _ hm _).symm.trans ((congrArg (gs x y _) (hw i (p, q))).trans ((gs_mul x y _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit x y _ hm _) (gs_res x y _ hm _))))

/- English proof (translation)
Use `⟨fun h y p hp => ?_, fun h y q hq => ?_⟩` and prove the remaining obligations. Take `⟨q, hq⟩` from `exists_chart hA (x y)`. Take `⟨u, hu⟩` from `h y q hq`. Take `⟨u', hu'⟩` from `gs_of_secMaps hw y hp hq`. Conclude with `⟨u' * u, fun i => by rw [hu', hu, Units.val_mul, mul_left_comm]⟩`.

Take `⟨p, hp⟩` from `exists_chart hB (x y)`. Take `⟨u, hu⟩` from `h y p hp`. Take `⟨u', hu'⟩` from `gs_of_secMaps hw y hp hq`. Conclude with `⟨u'⁻¹ * u, fun i => by rw [Units.val_mul, mul_left_comm, ← hu, hu', Units.inv_mul_cancel_left]⟩`.
-/
theorem loc_iff_of_secMaps (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : ∀ i, SecMaps w (a i) (b i)) :
    Loc A a x v ↔ Loc B b x v := by
  refine ⟨fun h y p hp => ?_, fun h y q hq => ?_⟩
  · obtain ⟨q, hq⟩ := exists_chart hA (x y)
    obtain ⟨u, hu⟩ := h y q hq
    obtain ⟨u', hu'⟩ := gs_of_secMaps hw y hp hq
    exact ⟨u' * u, fun i => by rw [hu', hu, Units.val_mul, mul_left_comm]⟩
  · obtain ⟨p, hp⟩ := exists_chart hB (x y)
    obtain ⟨u, hu⟩ := h y p hp
    obtain ⟨u', hu'⟩ := gs_of_secMaps hw y hp hq
    exact ⟨u'⁻¹ * u, fun i => by rw [Units.val_mul, mul_left_comm, ← hu, hu', Units.inv_mul_cancel_left]⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`. Set `y : Sp T` to `⟨m, hm.isPrime⟩`. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 (hc.ge (Set.mem_univ (x y)))`. Take `⟨k, hk⟩` from `exists_chart_of_mem _ hi`.

Take `⟨u, hu⟩` from `h y k hk`. Establish `h1` using `(mem_nonzeroLocus_iff_gs (a i) x y hk).1 hi`. Rewrite `h1` using `[hu]`. Establish `h2` using `((Sp T).mem_basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (v i)) y trivial).2 (isUnit_of_mul_isUnit_left h1)`. Establish `h3` using `(basicOpen_eq_of_affine (R := CommRingCat.of T) (v i)).le h2`.

Conclude with `h3 (hle (Ideal.subset_span ⟨i, rfl⟩))`.
-/
theorem span_eq_top_of_loc (hc : ⨆ i, Out.nonzeroLocus (a i) = ⊤) (h : Loc A a x v) :
    Ideal.span (Set.range v) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let y : Sp T := ⟨m, hm.isPrime⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ (x y)))
  obtain ⟨k, hk⟩ := exists_chart_of_mem _ hi
  obtain ⟨u, hu⟩ := h y k hk
  have h1 := (mem_nonzeroLocus_iff_gs (a i) x y hk).1 hi
  rw [hu] at h1
  have h2 := ((Sp T).mem_basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (v i)) y trivial).2
    (isUnit_of_mul_isUnit_left h1)
  have h3 := (basicOpen_eq_of_affine (R := CommRingCat.of T) (v i)).le h2
  exact h3 (hle (Ideal.subset_span ⟨i, rfl⟩))

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => secCoord_of_loc (span_eq_top_of_loc ha (loc_of_secCoord h)) ((loc_iff_of_secMaps hA hB hw).1 (loc_of_secCoord h)), fun h => secCoord_of_loc (span_eq_top_of_loc hb (loc_of_secCoord h)) ((loc_iff_of_secMaps hA hB hw).2 (loc_of_secCoord h))⟩`.
-/
theorem secCoord_iff_of_secMaps (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : ∀ i, SecMaps w (a i) (b i))
    (ha : ⨆ i, Out.nonzeroLocus (a i) = ⊤) (hb : ⨆ i, Out.nonzeroLocus (b i) = ⊤) :
    SecCoord A a x v ↔ SecCoord B b x v :=
  ⟨fun h => secCoord_of_loc (span_eq_top_of_loc ha (loc_of_secCoord h))
      ((loc_iff_of_secMaps hA hB hw).1 (loc_of_secCoord h)),
    fun h => secCoord_of_loc (span_eq_top_of_loc hb (loc_of_secCoord h))
      ((loc_iff_of_secMaps hA hB hw).2 (loc_of_secCoord h))⟩

/- English proof (translation)
Use `⟨pull_isLB (O1_isLB R N) _, fun R' _ β x v hx h => ?_, fun R' _ β v hv _ => ?_⟩` and prove the remaining obligations. Take `⟨hv, -⟩` from `(ProjCoord.secCoord_iff e (𝟙 _) β x (by simpa using hx) v).1 h`. Rewrite `hv` using `[ProjCoord.range_comp_symm]`. Conclude with `⟨hv, fun F hF => by rw [Ideal.mem_bot.1 hF, MvPolynomial.eval₂_zero]⟩`. Rewrite `hv` using `[← ProjCoord.range_comp_symm e]`.

Use `⟨pt β _ hv, ⟨pt_str _ _ _, ?_⟩, fun x hx => ?_⟩` and prove the remaining obligations. Conclude with `(ProjCoord.secCoord_iff e (𝟙 _) β _ (by simpa using pt_str β _ hv) v).2 ⟨hv, Category.comp_id _⟩`. Take `⟨_, h⟩` from `(ProjCoord.secCoord_iff e (𝟙 _) β x (by simpa using hx.1) v).1 hx.2`. Conclude with `(Category.comp_id _).symm.trans h`.
-/
theorem projRep_bot (R : Type) [CommRing R] {N : ℕ} (e : σ ≃ Fin (N + 1)) :
    ProjRep (⊥ : Ideal (MvPolynomial σ R)) (PSpace.str R N) ((O1 R N).pull (𝟙 _))
      (fun c => secPull (coord R N (e c)) (𝟙 _)) := by
  refine ⟨pull_isLB (O1_isLB R N) _, fun R' _ β x v hx h => ?_, fun R' _ β v hv _ => ?_⟩
  · obtain ⟨hv, -⟩ := (ProjCoord.secCoord_iff e (𝟙 _) β x (by simpa using hx) v).1 h
    rw [ProjCoord.range_comp_symm] at hv
    exact ⟨hv, fun F hF => by rw [Ideal.mem_bot.1 hF, MvPolynomial.eval₂_zero]⟩
  · rw [← ProjCoord.range_comp_symm e] at hv
    refine ⟨pt β _ hv, ⟨pt_str _ _ _, ?_⟩, fun x hx => ?_⟩
    · exact (ProjCoord.secCoord_iff e (𝟙 _) β _ (by simpa using pt_str β _ hv) v).2 ⟨hv, Category.comp_id _⟩
    · obtain ⟨_, h⟩ := (ProjCoord.secCoord_iff e (𝟙 _) β x (by simpa using hx.1) v).1 hx.2
      exact (Category.comp_id _).symm.trans h

/- English proof (translation)
Establish `: Finite σ` using `Finite.of_equiv _ e.symm`. Take `⟨hs, hcl⟩` from `(veryAmpleBy_iff f (fun j => a (e.symm j))).1 ((embedsBy_spec_iff f _).1 h)`. Establish `key` using `GlobalTheory.T.isProjectiveCoordinateRepresentation_closedSubscheme R σ ⊥ _ X (PSpace.str R N) _ _ (toProj f _ hs) A a (projRep_bot R e) hcl hA fun R' _ y v => by`. Set `c : R →+* R'` to `(Spec.preimage (y ≫ f)).hom`. Establish `hc : (y ≫ toProj f _ hs) ≫ PSpace.str R N = spMap c`.

Rewrite using `[Category.assoc, toProj_str]`. Conclude with `(Spec.map_preimage (y ≫ f)).symm`. Establish `h1` using `ProjCoord.secCoord_iff e (toProj f _ hs) c y hc v`. Establish `h2` using `ProjCoord.secCoord_iff e (𝟙 _) c (y ≫ toProj f _ hs) (by rw [Category.comp_id]; exact hc) v`. Rewrite `h2` using `[Category.comp_id]`.

Use `Iff.trans ?_ (h1.trans h2.symm)` and prove the remaining obligations. Use `(secCoord_iff_of_secMaps (pull_isLB (O1_isLB R N) _) hA (w := toProjIso f _ hs) (fun i => ?_) ?_ ?_).symm` and prove the remaining obligations. Simplify `secMaps_toProjIso f _ hs (e i)` using `only [Equiv.symm_apply_apply]`. Conclude with `(e.iSup_comp (g := fun j => Out.nonzeroLocus (secPull (coord R N j) (toProj f _ hs)))).trans (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R N) _)`. Conclude with `(e.symm.iSup_comp (g := fun c => Out.nonzeroLocus (a c))).symm.trans hs`.

Rewrite `key` using `[toProj_str]`. Then use the resulting hypothesis.
-/
theorem projRep_of_embedsBy {R : Type} [CommRing R] (f : X ⟶ Sp R) (hA : A.IsLB) {N : ℕ} (e : σ ≃ Fin (N + 1))
    (h : EmbedsBy f (fun j => a (e.symm j))) : ProjRep (idealOf f A a (𝟙 X)) f A a := by
  have : Finite σ := Finite.of_equiv _ e.symm
  obtain ⟨hs, hcl⟩ := (veryAmpleBy_iff f (fun j => a (e.symm j))).1 ((embedsBy_spec_iff f _).1 h)
  have key := GlobalTheory.T.isProjectiveCoordinateRepresentation_closedSubscheme R σ ⊥ _ X (PSpace.str R N) _ _ (toProj f _ hs) A a (projRep_bot R e) hcl hA
    fun R' _ y v => by
      let c : R →+* R' := (Spec.preimage (y ≫ f)).hom
      have hc : (y ≫ toProj f _ hs) ≫ PSpace.str R N = spMap c := by
        rw [Category.assoc, toProj_str]
        exact (Spec.map_preimage (y ≫ f)).symm
      have h1 := ProjCoord.secCoord_iff e (toProj f _ hs) c y hc v
      have h2 := ProjCoord.secCoord_iff e (𝟙 _) c (y ≫ toProj f _ hs) (by rw [Category.comp_id]; exact hc) v
      rw [Category.comp_id] at h2
      refine Iff.trans ?_ (h1.trans h2.symm)
      refine (secCoord_iff_of_secMaps (pull_isLB (O1_isLB R N) _) hA (w := toProjIso f _ hs) (fun i => ?_) ?_ ?_).symm
      · simpa only [Equiv.symm_apply_apply] using secMaps_toProjIso f _ hs (e i)
      · exact (e.iSup_comp (g := fun j => Out.nonzeroLocus (secPull (coord R N j) (toProj f _ hs)))).trans
          (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R N) _)
      · exact (e.symm.iSup_comp (g := fun c => Out.nonzeroLocus (a c))).symm.trans hs
  rwa [toProj_str] at key

/- English proof (translation)
Introduce `hL _ S P K _ _ x k I _ σ hk hσ`. Take `⟨N, rfl⟩` from `Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)`. Establish `hN : 4 ≤ N` using `by exact_mod_cast hk`. Use `Fintype.ofFinite I` as an intermediate fact. Establish `h₀` using `embedsBy_fibre hL.ample hL.polBaseChange P x hN σ hσ`.

Establish `hne : Nonempty I`. Take `⟨p⟩ : Nonempty (Sp K)` from `inferInstance`. Take `⟨i, -⟩` from `Opens.mem_iSup.1 (h₀.1.ge (Set.mem_univ ((lift (𝟙 (Over.mk x)) (1 : Over.mk x ⟶ P.A)).left p)))`. Conclude with `⟨i⟩`. Take `⟨M, hM⟩ : ∃ M, Fintype.card I = M + 1` from `⟨_, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩`.

Set `e` to `Fintype.equivFinOfCardEq hM`. Use `projRep_of_embedsBy _ (DVR.linComb_isLB P.L P.isLB _ _) e (embedsBy_fibre hL.ample hL.polBaseChange P x hN _ ?_)` and prove the remaining obligations. Rewrite using `[← hσ]`. Conclude with `congrArg _ (e.symm.surjective.range_comp fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L N (Over.mk x)))`.
-/
theorem projRep_fibre : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (k : ℤ) (I : Type) [Finite I] (σ : I → LB.Sec (Out.LPow P.A P.L k (Over.mk x))), 4 ≤ k → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L k (Over.mk x))) = ⊤ → ProjRep (idealOf (fst (Over.mk x) P.A).left _ σ (𝟙 _)) (fst (Over.mk x) P.A).left _ σ := by
  intro hL _ S P K _ _ x k I _ σ hk hσ
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
  have hN : 4 ≤ N := by exact_mod_cast hk
  have := Fintype.ofFinite I
  have h₀ := embedsBy_fibre hL.ample hL.polBaseChange P x hN σ hσ
  have hne : Nonempty I := by
    obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
    obtain ⟨i, -⟩ := Opens.mem_iSup.1 (h₀.1.ge (Set.mem_univ
      ((lift (𝟙 (Over.mk x)) (1 : Over.mk x ⟶ P.A)).left p)))
    exact ⟨i⟩
  obtain ⟨M, hM⟩ : ∃ M, Fintype.card I = M + 1 := ⟨_, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  let e := Fintype.equivFinOfCardEq hM
  refine projRep_of_embedsBy _ (DVR.linComb_isLB P.L P.isLB _ _) e
    (embedsBy_fibre hL.ample hL.polBaseChange P x hN _ ?_)
  rw [← hσ]
  exact congrArg _ (e.symm.surjective.range_comp
    fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L N (Over.mk x)))

end GlobalTheory.FibreEmbed
end
