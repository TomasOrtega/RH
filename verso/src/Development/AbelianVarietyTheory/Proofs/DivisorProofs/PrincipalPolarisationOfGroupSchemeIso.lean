import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolOfIso

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

/- English proof (translation)
Introduce `U' hU'`. Take `⟨U, hU, le⟩` from `hf U' hU'`. Take `⟨N, hN, M, s, hcov, hs⟩` from `hA U hU`. Establish `le' : A'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U)` using `fun y hy => (congrArg (fun q => q y ∈ U) h.w).mpr (le hy)`. Set `ψ` to `φ.resLE (A.hom ⁻¹ᵁ U) (A'.hom ⁻¹ᵁ U') le'`.

Establish `hψ : ψ ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ U').ι ≫ φ` using `Scheme.Hom.resLE_comp_ι φ le'`. Establish `H : IsPullback ψ (A'.hom ∣_ U') (A.hom ∣_ U) (f.resLE U U' le)`. Use `IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict A.hom U).flip` and prove the remaining obligations. Rewrite using `[hψ, Scheme.Hom.resLE_comp_ι]`. Conclude with `(isPullback_morphismRestrict A'.hom U').flip.paste_horiz h`.

Rewrite using `[← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, Category.assoc, h.w, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]`. Establish `: IsAffine U` using `hU`. Establish `: IsAffine U'` using `hU'`. Establish `: IsAffineHom ψ` using `MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance`. Establish `hP` using `linComb_isLB L hL (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)`.

Establish `hP'` using `linComb_isLB L' hL' (K := Fin N) (fun _ => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1)`. Take `⟨W, hW⟩` from `LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin N => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1) ψ _ fun _ => hψ.symm) (iso_linComb hw (fun _ : Fin N => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1))`. Use `choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)`. Establish `loc : ∀ i, nonzeroLocus (M` using `powOver A' L' U' N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by`. Use extensionality with `y`.

Use `(mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (ψ y)).symm)` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_chart hP (ψ y)`. Establish `e` using `hs' i _ (𝟙 _) y j k hj hk`. Rewrite `e` using `[Category.id_comp, gs_stalkMap ψ y _ hj]`. Conclude with `⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩`.

Take `⟨k, hk⟩` from `exists_chart hP' y`. Establish `e` using `hs' i _ (𝟙 _) y j k hj hk`. Rewrite `e` using `[Category.id_comp]`. Conclude with `⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩`. Use `⟨N, hN, M, s', ?_, fun i => ?_⟩` and prove the remaining obligations.

Use `top_le_iff.1 fun y _ => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)`. Conclude with `Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩`. Take `⟨haff, r, hr, hsurj⟩` from `hs i`. Use `⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩` and prove the remaining obligations.

Take `⟨l, hl⟩` from `exists_chart hP (ψ y)`. Establish `hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver A L U N).U l` using `⟨(loc i).le hy.1, hl⟩`. Establish `e` using `congrArg (gs ψ y _) (hr j l)`. Rewrite `e` using `[gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm]`. Establish `e₁` using `hs' j _ (𝟙 _) y l k hl hy.2`.

Establish `e₂` using `hs' i _ (𝟙 _) y l k hl hy.2`. Rewrite `e₁`, `e₂` using `[Category.id_comp]`. Establish `e₃` using `(gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))`. Use `(gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))` and prove the remaining obligations. Establish `po` using `(isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top (UY := nonzeroLocus (M := powOver A' L' U' N) (s' i)) (by rw [loc]; simp)).1 (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)`.

Rewrite using `[← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]`. Introduce and unpack `_ (⟨d, rfl⟩ | ⟨c, rfl⟩)`. Take `⟨p, rfl⟩` from `hsurj d`. Use `⟨MvPolynomial.map ((f.resLE U U' le).appLE ⊤ ⊤ le_top).hom p, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval₂Hom_map_hom]`.

Conclude with `((congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (congrArg CommRingCat.Hom.hom po.w.symm)).trans (MvPolynomial.map_eval₂Hom _ _ _ p).symm)`. Conclude with `⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩`.
-/
theorem relAmple_pull_of_affine (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull φ)} (hw : PGen w)
    (hf : ∀ U' : S'.Opens, IsAffineOpen U' → ∃ U : S.Opens, IsAffineOpen U ∧ U' ≤ f ⁻¹ᵁ U) (hA : RelAmple A L) :
    RelAmple A' L' := by
  intro U' hU'
  obtain ⟨U, hU, le⟩ := hf U' hU'
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA U hU
  have le' : A'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy => (congrArg (fun q => q y ∈ U) h.w).mpr (le hy)
  let ψ := φ.resLE (A.hom ⁻¹ᵁ U) (A'.hom ⁻¹ᵁ U') le'
  have hψ : ψ ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ U').ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  have H : IsPullback ψ (A'.hom ∣_ U') (A.hom ∣_ U) (f.resLE U U' le) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict A.hom U).flip
    · rw [hψ, Scheme.Hom.resLE_comp_ι]
      exact (isPullback_morphismRestrict A'.hom U').flip.paste_horiz h
    · rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, Category.assoc, h.w, Category.assoc,
        Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have : IsAffine U := hU
  have : IsAffine U' := hU'
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := linComb_isLB L hL (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)
  have hP' := linComb_isLB L' hL' (K := Fin N) (fun _ => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1)
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin N => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1) ψ _
    fun _ => hψ.symm) (iso_linComb hw (fun _ : Fin N => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver A' L' U' N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨N, hN, M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver A L U N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver A' L' U' N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po,
      Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map ((f.resLE U U' le).appLE ⊤ ⊤ le_top).hom p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      exact ((congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (congrArg CommRingCat.Hom.hom po.w.symm)).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

/- English proof (translation)
Introduce `s`. Take `⟨U, hU, t, ht⟩` from `hs (f s)`. Use `⟨f ⁻¹ᵁ U, hU, ?_⟩` and prove the remaining obligations. Establish `le' : A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U)` using `fun y hy => (congrArg (fun q => q y ∈ U) h.1.w).mpr hy`. Establish `hψ : φ.resLE _ _ le' ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ φ` using `Scheme.Hom.resLE_comp_ι φ le'`.

Take `⟨t', ht'⟩` from `gen_chartPull (chartPullSame L (fun k => ![(A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ (GrpObj.inv : A' ⟶ A').left, (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι] k ≫ φ) _ _ (φ.resLE _ _ le') fun k => by fin_cases k`. Use `show (_ ≫ _) ≫ φ = _ ≫ _ ≫ _`. Rewrite using `[Category.assoc, PolBaseChange.inv_comm h, ← Category.assoc, ← hψ, Category.assoc]`. Conclude with `hψ.symm) t ht`. Conclude with `exists_down hw hL hL' t' ht'`.
-/
theorem sym_pull_of_iso [GrpObj A] [GrpObj A'] (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull φ)} (hw : PGen w) (hs : Sym A L) : Sym A' L' := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := hs (f s)
  refine ⟨f ⁻¹ᵁ U, hU, ?_⟩
  have le' : A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy =>
    (congrArg (fun q => q y ∈ U) h.1.w).mpr hy
  have hψ : φ.resLE _ _ le' ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  obtain ⟨t', ht'⟩ := gen_chartPull (chartPullSame L
    (fun k => ![(A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ (GrpObj.inv : A' ⟶ A').left, (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι] k ≫ φ) _ _
    (φ.resLE _ _ le') fun k => by
      fin_cases k
      · show (_ ≫ _) ≫ φ = _ ≫ _ ≫ _
        rw [Category.assoc, PolBaseChange.inv_comm h, ← Category.assoc, ← hψ, Category.assoc]
      · exact hψ.symm) t ht
  exact exists_down hw hL hL' t' ht'

end GlobalTheory.PolOfIso

namespace GlobalTheory

/- English proof (translation)
Introduce `S P B _ e he L hL ⟨w, hw⟩`. Establish `h` using `isGrpPullback_of_iso e`. Establish `hw'` using `(isGen_iff w).1 hw`. Conclude with `⟨MorphismProperty.of_isPullback (P := @IsProper) h.1 P.isAb.proper, (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim, PolOfIso.sym_pull_of_iso h P.isLB hL hw' P.sym, PolOfIso.relAmple_pull_of_affine h.1 P.isLB hL hw' (fun U hU => ⟨U, hU, fun _ h …`.
-/
theorem polarisation_of_iso :
    ∀ (S : Scheme.{0}) (P : PolAV S) (B : Over S) [GrpObj B] (e : B ≅ P.A), IsMonHom e.hom → ∀ L : LB B.left, L.IsLB → LBIso L (P.L.pull e.hom.left) → IsProper B.hom ∧ SmoothOfRelativeDimension P.g B.hom ∧ Sym B L ∧ RelAmple B L ∧ KTriv B L := by
  intro S P B _ e he L hL ⟨w, hw⟩
  have h := isGrpPullback_of_iso e
  have hw' := (isGen_iff w).1 hw
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) h.1 P.isAb.proper,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim,
    PolOfIso.sym_pull_of_iso h P.isLB hL hw' P.sym,
    PolOfIso.relAmple_pull_of_affine h.1 P.isLB hL hw' (fun U hU => ⟨U, hU, fun _ hy => hy⟩) P.ample,
    kTriv_pull h P.isLB hL hw' P.ktriv⟩

end GlobalTheory
