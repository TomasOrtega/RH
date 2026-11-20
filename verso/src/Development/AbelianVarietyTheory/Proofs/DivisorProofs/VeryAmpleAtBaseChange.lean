import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 TopologicalSpace

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RelAmpleFixed

/- English proof (translation)
Introduce `Rg _ B _ _ L _ hL hA`. Take `⟨N, hN, M, s, hcov, hs⟩` from `hA ⊤ (isAffineOpen_top _)`. Use `⟨N, hN, fun R' _ fr B' _ φ hg => ?_⟩` and prove the remaining obligations. Establish `h : IsPullback φ B'.hom B.hom (spMap fr)` using `hg.1`. Establish `hL' : (L.pull φ).IsLB` using `pull_isLB hL φ`.

Take `⟨w, hw'⟩` from `PolBaseChange.lbIso_refl hL'`. Establish `hw` using `(isGen_iff w).1 hw'`. Introduce `U' hU'`. Establish `le : U' ≤ (spMap fr) ⁻¹ᵁ (⊤ : (Sp Rg).Opens)` using `fun y _ => trivial`. Establish `le' : B'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (B.hom ⁻¹ᵁ ⊤)` using `fun y _ => trivial`.

Set `ψ` to `φ.resLE (B.hom ⁻¹ᵁ ⊤) (B'.hom ⁻¹ᵁ U') le'`. Establish `hψ : ψ ≫ (B.hom ⁻¹ᵁ ⊤).ι = (B'.hom ⁻¹ᵁ U').ι ≫ φ` using `Scheme.Hom.resLE_comp_ι φ le'`. Establish `H : IsPullback ψ (B'.hom ∣_ U') (B.hom ∣_ ⊤) ((spMap fr).resLE ⊤ U' le)`. Use `IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict B.hom ⊤).flip` and prove the remaining obligations. Rewrite using `[hψ, Scheme.Hom.resLE_comp_ι]`.

Conclude with `(isPullback_morphismRestrict B'.hom U').flip.paste_horiz h`. Rewrite using `[← cancel_mono (⊤ : (Sp Rg).Opens).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, Category.assoc, h.w, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]`. Establish `: IsAffine (⊤ : (Sp Rg).Opens)` using `isAffineOpen_top _`. Establish `: IsAffine U'` using `hU'`. Establish `: IsAffineHom ψ` using `MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance`.

Establish `hP` using `linComb_isLB L hL (K := Fin N) (fun _ => (B.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1)`. Establish `hP'` using `linComb_isLB (L.pull φ) hL' (K := Fin N) (fun _ => (B'.hom ⁻¹ᵁ U').ι) (fun _ => 1)`. Take `⟨W, hW⟩` from `LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin N => (B.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1) ψ _ fun _ => hψ.symm) (iso_linComb hw (fun _ : Fin N => (B'.hom ⁻¹ᵁ U').ι) (fun _ => 1))`. Use `choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)`. Establish `loc : ∀ i, nonzeroLocus (M` using `powOver B' (L.pull φ) U' N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by`.

Use extensionality with `y`. Use `(mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (ψ y)).symm)` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_chart hP (ψ y)`. Establish `e` using `hs' i _ (𝟙 _) y j k hj hk`. Rewrite `e` using `[Category.id_comp, gs_stalkMap ψ y _ hj]`.

Conclude with `⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩`. Take `⟨k, hk⟩` from `exists_chart hP' y`. Establish `e` using `hs' i _ (𝟙 _) y j k hj hk`. Rewrite `e` using `[Category.id_comp]`. Conclude with `⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩`.

Use `⟨M, s', ?_, fun i => ?_⟩` and prove the remaining obligations. Use `top_le_iff.1 fun y _ => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)`. Conclude with `Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩`. Take `⟨haff, r, hr, hsurj⟩` from `hs i`.

Use `⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩` and prove the remaining obligations. Take `⟨l, hl⟩` from `exists_chart hP (ψ y)`. Establish `hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver B L ⊤ N).U l` using `⟨(loc i).le hy.1, hl⟩`. Establish `e` using `congrArg (gs ψ y _) (hr j l)`. Rewrite `e` using `[gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm]`.

Establish `e₁` using `hs' j _ (𝟙 _) y l k hl hy.2`. Establish `e₂` using `hs' i _ (𝟙 _) y l k hl hy.2`. Rewrite `e₁`, `e₂` using `[Category.id_comp]`. Establish `e₃` using `(gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))`. Use `(gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))` and prove the remaining obligations.

Establish `po` using `(isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top (UY := nonzeroLocus (M := powOver B' (L.pull φ) U' N) (s' i)) (by rw [loc]; simp)).1 (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)`. Rewrite using `[← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]`. Introduce and unpack `_ (⟨d, rfl⟩ | ⟨c, rfl⟩)`. Take `⟨p, rfl⟩` from `hsurj d`. Use `⟨MvPolynomial.map (((spMap fr).resLE ⊤ U' le).appLE ⊤ ⊤ le_top).hom p, ?_⟩` and prove the remaining obligations.

Rewrite using `[MvPolynomial.eval₂Hom_map_hom]`. Conclude with `((congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (congrArg CommRingCat.Hom.hom po.w.symm)).trans (MvPolynomial.map_eval₂Hom _ _ _ p).symm)`. Conclude with `⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩`.
-/
theorem veryAmpleAt_baseChange : ∀ (Rg : Type) [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] [IsCommMonObj B] (M : LB B.left),
    IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∃ k : ℕ, 1 ≤ k ∧ ∀ (R' : Type) [CommRing R'] (φ : Rg →+* R')
      (B' : Over (Sp R')) [GrpObj B'] (φB : B'.left ⟶ B.left), IsGrpPullback B' B (spMap φ) φB →
      Out.VeryAmpleAt B' (M.pull φB) k := by
  intro Rg _ B _ _ L _ hL hA
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA ⊤ (isAffineOpen_top _)
  refine ⟨N, hN, fun R' _ fr B' _ φ hg => ?_⟩
  have h : IsPullback φ B'.hom B.hom (spMap fr) := hg.1
  have hL' : (L.pull φ).IsLB := pull_isLB hL φ
  obtain ⟨w, hw'⟩ := PolBaseChange.lbIso_refl hL'
  have hw := (isGen_iff w).1 hw'
  intro U' hU'
  have le : U' ≤ (spMap fr) ⁻¹ᵁ (⊤ : (Sp Rg).Opens) := fun y _ => trivial
  have le' : B'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (B.hom ⁻¹ᵁ ⊤) := fun y _ => trivial
  let ψ := φ.resLE (B.hom ⁻¹ᵁ ⊤) (B'.hom ⁻¹ᵁ U') le'
  have hψ : ψ ≫ (B.hom ⁻¹ᵁ ⊤).ι = (B'.hom ⁻¹ᵁ U').ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  have H : IsPullback ψ (B'.hom ∣_ U') (B.hom ∣_ ⊤) ((spMap fr).resLE ⊤ U' le) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict B.hom ⊤).flip
    · rw [hψ, Scheme.Hom.resLE_comp_ι]
      exact (isPullback_morphismRestrict B'.hom U').flip.paste_horiz h
    · rw [← cancel_mono (⊤ : (Sp Rg).Opens).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, Category.assoc, h.w,
        Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have : IsAffine (⊤ : (Sp Rg).Opens) := isAffineOpen_top _
  have : IsAffine U' := hU'
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := linComb_isLB L hL (K := Fin N) (fun _ => (B.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1)
  have hP' := linComb_isLB (L.pull φ) hL' (K := Fin N) (fun _ => (B'.hom ⁻¹ᵁ U').ι) (fun _ => 1)
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin N => (B.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1) ψ _
    fun _ => hψ.symm) (iso_linComb hw (fun _ : Fin N => (B'.hom ⁻¹ᵁ U').ι) (fun _ => 1))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver B' (L.pull φ) U' N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
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
  refine ⟨M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver B L ⊤ N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver B' (L.pull φ) U' N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po,
      Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map (((spMap fr).resLE ⊤ U' le).appLE ⊤ ⊤ le_top).hom p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      exact ((congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (congrArg CommRingCat.Hom.hom po.w.symm)).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

end GlobalTheory.RelAmpleFixed
