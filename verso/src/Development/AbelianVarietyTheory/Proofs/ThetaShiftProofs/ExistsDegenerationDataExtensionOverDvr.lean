import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationPreDataOverSubfield

noncomputable section

namespace GlobalTheory.DvrDeg

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull
attribute [local instance] Over.cartesianMonoidalCategory

section General

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

/- English proof (translation)
Set `W` to `(jK R).opensRange`. Set `s : W.toScheme ⟶ (TK R).left` to `(jK R).isoOpensRange.inv`. Establish `hs : s ≫ jK R = W.ι` using `(jK R).isoOpensRange_inv_comp`. Establish `hr : (jK R ∣_ W) ≫ s = (jK R ⁻¹ᵁ W).ι`. Rewrite using `[← cancel_mono (jK R), Category.assoc, hs, morphismRestrict_ι]`.

Establish `hx : ∀ χ, s ≫ D.xK χ = (toUnit (TW W) ≫ D.c χ).left` using `fun χ => by show s ≫ jK R ≫ (D.c χ).left = W.ι ≫ (D.c χ).left`. Rewrite using `[← Category.assoc, hs]`. Use `choose t ht vt using fun χ => exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => (toUnit (TW W) ≫ D.c χ).left) (ε' := fun _ => -1) (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx χ)) (LB.pullGen D.P.L _ _ (D.psi χ) s) (DVR.pullGen_isGen _ _ _ …`. Use `⟨⟨t, ht, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩` and prove the remaining obligations. Use `(val_pull hJ _ _ _).trans ((vt χ _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)))` and prove the remaining obligations.

Conclude with `congrArg (fun q => val (D.psi χ) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) hr))`.
-/
theorem nonempty_psiOn_generic (D : DegPre R) [IsOpenImmersion (jK R)] : Nonempty (PsiOn D (jK R).opensRange) := by
  let W := (jK R).opensRange
  let s : W.toScheme ⟶ (TK R).left := (jK R).isoOpensRange.inv
  have hs : s ≫ jK R = W.ι := (jK R).isoOpensRange_inv_comp
  have hr : (jK R ∣_ W) ≫ s = (jK R ⁻¹ᵁ W).ι := by
    rw [← cancel_mono (jK R), Category.assoc, hs, morphismRestrict_ι]
  have hx : ∀ χ, s ≫ D.xK χ = (toUnit (TW W) ≫ D.c χ).left := fun χ => by
    show s ≫ jK R ≫ (D.c χ).left = W.ι ≫ (D.c χ).left
    rw [← Category.assoc, hs]
  choose t ht vt using fun χ => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => (toUnit (TW W) ≫ D.c χ).left) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx χ))
    (LB.pullGen D.P.L _ _ (D.psi χ) s) (DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) s)
  refine ⟨⟨t, ht, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  refine (val_pull hJ _ _ _).trans ((vt χ _ _ y J hJ).trans ((val_pull hJ _ _ _).trans
    (Eq.trans ?_ (val_pull hJ _ _ _).symm)))
  exact congrArg (fun q => val (D.psi χ) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) hr))

/- English proof (translation)
Take `⟨e, e_hom, he⟩` from `grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))`. Substitute `he` using the available equality. Establish `hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A` using `(cubeMapOf gp).e_comm`. Take `⟨g, sq⟩ : ∃ g : (TK R').left ⟶ (TW W).left, g ≫ W.ι = genMap hi ≫ jK R` from `⟨genMap hi ≫ s, (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hs)⟩`. Establish `hg : g ≫ W.ι = jK R' ≫ specOf i` using `sq.trans ((fracMap_sq hi).symm.trans (Category.id_comp _))`.

Take `⟨lam, l₁, l₂⟩ : ∃ lam : (TK R').left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = genMap hi ∧ lam ≫ (jK R ∣_ W) = g` from `⟨(isPullback_morphismRestrict (jK R) W).lift _ _ sq, (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _, (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩`. Establish `hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left = D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)` using `fun x => by show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _`. Rewrite using `[Category.assoc, hc, ← Category.assoc, hg, Category.assoc]`. Use `choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1) (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x)) (LB.pullGen D.P.L _ _ (ψW.psi (x …`. Use `choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit) (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)`.

Establish `eψ : ∀ x, psi x = D'.psi x` using `fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by`. Take `⟨J, hJ⟩` from `DegPull.exists_good' D.P.isLB y`. Establish `v` using `vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))`. Establish `u` using `(val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))`. Rewrite `u` using `[l₁, l₂, hψ x y J J' hJ hJ']`.

Establish `v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J` using `(vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))`. Establish `v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J'`. Use `v.trans (congrArg₂ (· * ·) ?_ rfl)` and prove the remaining obligations. Rewrite using `[pw, Fintype.prod_unique, zpow_neg_one]`. Simplify using `only [om, Category.id_comp]`.

Conclude with `mul_left_cancel (v₂.symm.trans (v₁.trans u))`. Use `⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_, corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl⟩` and prove the remaining obligations. Conclude with `(maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _ (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr`. Rewrite using `[← eψ]`. Use `unit_ext fun y hy => ?_` and prove the remaining obligations.

Establish `v` using `vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)`. Use `(gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res _ y _ hy _)))))` and prove the remaining obligations. Rewrite using `[pw, Fintype.prod_unique]`. Conclude with `(map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))`.
-/
theorem exists_isPullDeg_of_val {i : R →+* R'} (hi : Function.Injective i) (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (s : (TK R).left ⟶ W.toScheme) (hs : s ≫ W.ι = jK R)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (genMap hi) z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨g, sq⟩ : ∃ g : (TK R').left ⟶ (TW W).left, g ≫ W.ι = genMap hi ≫ jK R :=
    ⟨genMap hi ≫ s, (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hs)⟩
  have hg : g ≫ W.ι = jK R' ≫ specOf i := sq.trans ((fracMap_sq hi).symm.trans (Category.id_comp _))
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R').left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = genMap hi ∧
      lam ≫ (jK R ∣_ W) = g :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ sq,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂, hψ x y J J' hJ hJ'] at u
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

attribute [local instance] TorusExt.gtGroup in

/- English proof (translation)
Take `⟨g, h₁, h₂⟩` from `q.eq`. Take `⟨hb, hv⟩` from `(isIota_iff _ _).1 h₂`. Establish `e₁ : GtPtF.IsNsmul k (TorusExt.gtExt D σ hσ q.g) (TorusExt.gtExt D σ hσ g)`. Rewrite `h₁`, the goal using `[TorusExt.isNsmul_iff_eq]`. Rewrite using `[h₁, map_nsmul]`.

Establish `e₂ : GtPtF.IsIota q.y (TorusExt.gtExt D σ hσ g)` using `(isIota_iff _ _).2 ⟨by rw [TorusExt.gtExt_b, hb, DVR.comp_cP], fun χ y J hJ => (TorusExt.gtExt_val σ hσ _ χ hJ).trans ((val_corr hJ (h₂.2 χ) _).trans ((val_pull hJ _ _ _).trans (congrArg (fun r => val (D.tau q.y χ) r y J) (TorusExt.extMap_jFK σ hσ))))⟩`. Establish `hs : spMap f ≫ spMap σ = 𝟙 _`. Rewrite using `[← spMap_comp, h]`. Conclude with `Spec.map_id (CommRingCat.of F')`. Take `⟨b, v⟩` from `(TorusExt.eq_gtExt_iff σ hσ q.g _).1 rfl`.

Use `⟨⟨q.y, TorusExt.gtExt D σ hσ q.g, _, e₁, e₂⟩, rfl, ?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩` and prove the remaining obligations. Use `show q.g.b.left = spMap f ≫ (TorusExt.gtExt D σ hσ q.g).b.left`. Rewrite using `[b, ← Category.assoc, hs]`. Conclude with `(Category.id_comp _).symm`. Use `Eq.symm ((val_pull hJ _ _ _).trans ((val_corr hJ (v χ) _).trans ((val_pull hJ _ _ _).trans ?_)))` and prove the remaining obligations.

Conclude with `congrArg (fun r => val (q.g.s χ) r y J) ((Category.assoc _ _ _).trans ((congrArg (𝟙 _ ≫ ·) hs).trans (Category.id_comp _)))`.
-/
theorem exists_qkExt_of_inverse {D : DegPre R} {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R) F'] (f : F →+* F') (σ : F' →+* F) (h : f.comp σ = RingHom.id F')
    (hσ : σ.comp (algebraMap (FractionRing R) F') = algebraMap (FractionRing R) F) {k : ℕ} (q : QkPt D F' k) :
    ∃ p : QkPt D F k, QkExt f p q := by
  obtain ⟨g, h₁, h₂⟩ := q.eq
  obtain ⟨hb, hv⟩ := (isIota_iff _ _).1 h₂
  have e₁ : GtPtF.IsNsmul k (TorusExt.gtExt D σ hσ q.g) (TorusExt.gtExt D σ hσ g) := by
    rw [TorusExt.isNsmul_iff_eq] at h₁ ⊢
    rw [h₁, map_nsmul]
  have e₂ : GtPtF.IsIota q.y (TorusExt.gtExt D σ hσ g) :=
    (isIota_iff _ _).2 ⟨by rw [TorusExt.gtExt_b, hb, DVR.comp_cP], fun χ y J hJ =>
      (TorusExt.gtExt_val σ hσ _ χ hJ).trans ((val_corr hJ (h₂.2 χ) _).trans ((val_pull hJ _ _ _).trans
        (congrArg (fun r => val (D.tau q.y χ) r y J) (TorusExt.extMap_jFK σ hσ))))⟩
  have hs : spMap f ≫ spMap σ = 𝟙 _ := by
    rw [← spMap_comp, h]; exact Spec.map_id (CommRingCat.of F')
  obtain ⟨b, v⟩ := (TorusExt.eq_gtExt_iff σ hσ q.g _).1 rfl
  refine ⟨⟨q.y, TorusExt.gtExt D σ hσ q.g, _, e₁, e₂⟩, rfl, ?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · show q.g.b.left = spMap f ≫ (TorusExt.gtExt D σ hσ q.g).b.left
    rw [b, ← Category.assoc, hs]
    exact (Category.id_comp _).symm
  · refine Eq.symm ((val_pull hJ _ _ _).trans ((val_corr hJ (v χ) _).trans ((val_pull hJ _ _ _).trans ?_)))
    exact congrArg (fun r => val (q.g.s χ) r y J) ((Category.assoc _ _ _).trans
      ((congrArg (𝟙 _ ≫ ·) hs).trans (Category.id_comp _)))

end General

section Dvr

variable (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Establish `: IsLocalization.Away ϖ (FractionRing V)`. Use `(IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ) (nonZeroDivisors V) (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero) fun a ha => ?_).2 inferInstance` and prove the remaining obligations. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero ha) hϖ`. Conclude with `⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩`.

Conclude with `IsOpenImmersion.of_isLocalization ϖ`.
-/
theorem isOpenImmersion_generic : IsOpenImmersion (jK V) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have : IsLocalization.Away ϖ (FractionRing V) := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ)
      (nonZeroDivisors V) (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero)
      fun a ha => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero ha) hϖ
    exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact IsOpenImmersion.of_isLocalization ϖ

omit [IsDiscreteValuationRing V] in

/- English proof (translation)
Set `σ : FractionRing K ≃+* FractionRing V` to `(FractionRing.algEquiv K K).toRingEquiv.trans (FractionRing.algEquiv V K).symm.toRingEquiv`. Establish `h : σ.toRingHom.comp (fracMap (IsFractionRing.injective V K)) = RingHom.id _` using `IsLocalization.ringHom_ext (nonZeroDivisors V) (RingHom.ext fun r => by show (FractionRing.algEquiv V K).symm (FractionRing.algEquiv K K (fracMap _ (algebraMap V _ r))) = algebraMap V _ r`. Rewrite using `[fracMap_algebraMap, AlgEquiv.commutes]`. Conclude with `(FractionRing.algEquiv V K).symm.commutes r)`. Conclude with `⟨σ.toRingHom, RingHom.ext fun x => σ.injective (RingHom.congr_fun h (σ x)), h⟩`.
-/
theorem exists_fracInv : ∃ σ : FractionRing K →+* FractionRing V,
    (fracMap (IsFractionRing.injective V K)).comp σ = RingHom.id _ ∧
    σ.comp (fracMap (IsFractionRing.injective V K)) = RingHom.id _ := by
  let σ : FractionRing K ≃+* FractionRing V :=
    (FractionRing.algEquiv K K).toRingEquiv.trans (FractionRing.algEquiv V K).symm.toRingEquiv
  have h : σ.toRingHom.comp (fracMap (IsFractionRing.injective V K)) = RingHom.id _ :=
    IsLocalization.ringHom_ext (nonZeroDivisors V) (RingHom.ext fun r => by
      show (FractionRing.algEquiv V K).symm (FractionRing.algEquiv K K (fracMap _ (algebraMap V _ r))) = algebraMap V _ r
      rw [fracMap_algebraMap, AlgEquiv.commutes]
      exact (FractionRing.algEquiv V K).symm.commutes r)
  exact ⟨σ.toRingHom, RingHom.ext fun x => σ.injective (RingHom.congr_fun h (σ x)), h⟩

variable {V K}

/- English proof (translation)
Establish `hE : ValuativeCriterion.Existence A.hom`. Establish `h : UniversallyClosed A.hom` using `inferInstance`. Rewrite `h` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `h.1`. Establish `ex : ∀ x, ∃ c₀ : 𝟙_ (Over (Sp V)) ⟶ A, (c x).left ≫ Φ = spMap (algebraMap V K) ≫ c₀.left` using `fun x => by`.

Set `Q : ValuativeCommSq A.hom` to `{ R := V, K := K, i₁ := (c x).left ≫ Φ, i₂ := 𝟙 _, commSq := ⟨by`. Rewrite using `[Category.assoc, gp.1.w, ← Category.assoc, Over.w]`. Conclude with `(Category.id_comp _).trans (Category.comp_id _).symm⟩ }`. Take `⟨⟨l, h1, h2⟩⟩` from `hE Q`. Conclude with `⟨Over.homMk l h2, h1.symm⟩`.

Use `choose c₀ h₀ using ex`. Use `⟨c₀, fun a b => ?_, h₀⟩` and prove the remaining obligations. Establish `e : spMap (algebraMap V K) ≫ (c₀ (a + b)).left = spMap (algebraMap V K) ≫ (c₀ a * c₀ b).left`. Rewrite using `[← h₀, hc]`. Conclude with `mul_push gp (T' := 𝟙_ _) (T := 𝟙_ _) _ (h₀ a) (h₀ b)`.

Set `Q : ValuativeCommSq A.hom` to `{ R := V, K := K, i₁ := spMap (algebraMap V K) ≫ (c₀ (a + b)).left, i₂ := 𝟙 _, commSq := ⟨(Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w (c₀ (a + b))))⟩ }`. Use `(IsSeparated.valuativeCriterion A.hom Q).elim ⟨(c₀ (a + b)).left, rfl, Over.w _⟩ ⟨(c₀ a * c₀ b).left, e.symm, Over.w _⟩` as an intermediate fact. Conclude with `Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)`.
-/
theorem exists_points {A : Over (Sp V)} {A' : Over (Sp K)} [GrpObj A] [GrpObj A'] [IsProper A.hom]
    {Φ : A'.left ⟶ A.left} (gp : IsGrpPullback A' A (spMap (algebraMap V K)) Φ) {X : Type} [Add X]
    (c : X → (𝟙_ (Over (Sp K)) ⟶ A')) (hc : ∀ a b, c (a + b) = c a * c b) :
    ∃ c₀ : X → (𝟙_ (Over (Sp V)) ⟶ A), (∀ a b, c₀ (a + b) = c₀ a * c₀ b) ∧
      ∀ x, (c x).left ≫ Φ = spMap (algebraMap V K) ≫ (c₀ x).left := by
  have hE : ValuativeCriterion.Existence A.hom := by
    have h : UniversallyClosed A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have ex : ∀ x, ∃ c₀ : 𝟙_ (Over (Sp V)) ⟶ A, (c x).left ≫ Φ = spMap (algebraMap V K) ≫ c₀.left := fun x => by
    let Q : ValuativeCommSq A.hom :=
      { R := V, K := K, i₁ := (c x).left ≫ Φ, i₂ := 𝟙 _, commSq := ⟨by
          rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w]
          exact (Category.id_comp _).trans (Category.comp_id _).symm⟩ }
    obtain ⟨⟨l, h1, h2⟩⟩ := hE Q
    exact ⟨Over.homMk l h2, h1.symm⟩
  choose c₀ h₀ using ex
  refine ⟨c₀, fun a b => ?_, h₀⟩
  have e : spMap (algebraMap V K) ≫ (c₀ (a + b)).left = spMap (algebraMap V K) ≫ (c₀ a * c₀ b).left := by
    rw [← h₀, hc]
    exact mul_push gp (T' := 𝟙_ _) (T := 𝟙_ _) _ (h₀ a) (h₀ b)
  let Q : ValuativeCommSq A.hom :=
    { R := V, K := K, i₁ := spMap (algebraMap V K) ≫ (c₀ (a + b)).left, i₂ := 𝟙 _,
      commSq := ⟨(Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w (c₀ (a + b))))⟩ }
  have := (IsSeparated.valuativeCriterion A.hom Q).elim ⟨(c₀ (a + b)).left, rfl, Over.w _⟩
    ⟨(c₀ a * c₀ b).left, e.symm, Over.w _⟩
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)

/- English proof (translation)
Take `⟨w₀, hw₀⟩` from `hw₀`. Establish `hi` using `IsFractionRing.injective V K`. Use `P.isAb.proper` as an intermediate fact. Use `isOpenImmersion_generic V` as an intermediate fact. Take `⟨c₀, cadd, hc⟩` from `exists_points gp D.c D.c_add`.

Take `⟨rig, hrig⟩` from `P.rigid`. Take `⟨cub⟩` from `(hC _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1`. Take `⟨sym, hsym, hsr⟩` from `SelfUnif.exists_sym P`. Take `⟨w, hw, hr⟩` from `TripleMap.exists_rigidified P.isLB D.P.isLB w₀ ((isGen_iff w₀).1 hw₀) (eSec P.A) (eSec D.P.A) D.P.A.hom (Over.w η[D.P.A]) (spMap (algebraMap V K)) (cubeMapOf gp).e_comm rig hrig D.rig D.rig_gen`. Take `⟨σ, h₁, h₂⟩` from `exists_fracInv V K`.

Set `s : (TK V).left ⟶ (TK K).left` to `spMap σ`. Establish `s₁ : genMap hi ≫ s = 𝟙 _` using `(spMap_comp _ _).symm.trans ((congrArg spMap h₁).trans (Spec.map_id (CommRingCat.of (FractionRing K))))`. Establish `s₂ : s ≫ genMap hi = 𝟙 _` using `(spMap_comp _ _).symm.trans ((congrArg spMap h₂).trans (Spec.map_id (CommRingCat.of (FractionRing V))))`. Establish `hx : ∀ χ, D.xK χ ≫ Φ = genMap hi ≫ ptK (c₀ χ)` using `fun χ => by show (jK K ≫ (D.c χ).left) ≫ Φ = genMap hi ≫ jK V ≫ (c₀ χ).left`. Rewrite using `[Category.assoc, hc, ← Category.assoc, ← Category.assoc]`.

Conclude with `congrArg (· ≫ _) ((Category.id_comp _).symm.trans (fracMap_sq hi))`. Use `choose t ht vt using fun χ : D.X => exists_up hw P.isLB D.P.isLB (D.psi χ) (D.psi_gen χ)`. Use `choose psi hpsi vpsi using fun χ : D.X => exists_gen P.isLB (K' := PUnit) (φ' := fun _ => ptK (c₀ χ)) (ε' := fun _ => -1) (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (by show s ≫ D.xK χ ≫ Φ = _`. Rewrite using `[hx, ← Category.assoc, s₂, Category.id_comp]))`. Use the proof step `(LB.pullGen P.L _ _ (t χ) s) (DVR.pullGen_isGen _ _ _ _ (ht χ) s)`.

Set `D₀ : DegPre V` to `{ P := P, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D.X, c := c₀, c_add := cadd, psi := psi, psi_gen := hpsi }`. Take `⟨ψW⟩` from `nonempty_psiOn_generic D₀`. Take `⟨hD, e⟩` from `exists_isPullDeg_of_val hi D₀ D ψW (jK V).isoOpensRange.hom (jK V).isoOpensRange_hom_ι gp w hw hr (AddEquiv.refl _) hc (fun x z J J' hJ hJ' => by`. Establish `v` using `vt x _ (𝟙 _) z _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))`. Use `(vpsi x _ _ z J hJ).trans ((val_pull hJ _ _ _).trans ((congrArg (fun r => val (t x) r z J) s₁).trans (v.trans (congrArg₂ (· * ·) ?_ rfl))))` and prove the remaining obligations.

Rewrite using `[pw, Fintype.prod_unique, zpow_neg_one]`. Simplify using `only [om, Category.id_comp])`. Conclude with `⟨D₀, hD, rfl, heq_of_eq e⟩`.
-/
theorem exists_isPullDeg (hC : CubeSt) (P : PolAV (Sp V)) (D : DegPre K) (Φ : D.P.A.left ⟶ P.A.left)
    (gp : IsGrpPullback D.P.A P.A (spMap (algebraMap V K)) Φ) (hw₀ : LBIso D.P.L (P.L.pull Φ)) :
    ∃ (D₀ : DegPre V) (hD : IsPullDeg (algebraMap V K) D₀ D), D₀.P = P ∧ HEq (proj hD) Φ := by
  obtain ⟨w₀, hw₀⟩ := hw₀
  have hi := IsFractionRing.injective V K
  have := P.isAb.proper
  have := isOpenImmersion_generic V
  obtain ⟨c₀, cadd, hc⟩ := exists_points gp D.c D.c_add
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (hC _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := SelfUnif.exists_sym P
  obtain ⟨w, hw, hr⟩ := TripleMap.exists_rigidified P.isLB D.P.isLB w₀ ((isGen_iff w₀).1 hw₀) (eSec P.A)
    (eSec D.P.A) D.P.A.hom (Over.w η[D.P.A]) (spMap (algebraMap V K)) (cubeMapOf gp).e_comm rig hrig D.rig D.rig_gen
  obtain ⟨σ, h₁, h₂⟩ := exists_fracInv V K
  let s : (TK V).left ⟶ (TK K).left := spMap σ
  have s₁ : genMap hi ≫ s = 𝟙 _ :=
    (spMap_comp _ _).symm.trans ((congrArg spMap h₁).trans (Spec.map_id (CommRingCat.of (FractionRing K))))
  have s₂ : s ≫ genMap hi = 𝟙 _ :=
    (spMap_comp _ _).symm.trans ((congrArg spMap h₂).trans (Spec.map_id (CommRingCat.of (FractionRing V))))
  have hx : ∀ χ, D.xK χ ≫ Φ = genMap hi ≫ ptK (c₀ χ) := fun χ => by
    show (jK K ≫ (D.c χ).left) ≫ Φ = genMap hi ≫ jK V ≫ (c₀ χ).left
    rw [Category.assoc, hc, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ _) ((Category.id_comp _).symm.trans (fracMap_sq hi))
  choose t ht vt using fun χ : D.X => exists_up hw P.isLB D.P.isLB (D.psi χ) (D.psi_gen χ)
  choose psi hpsi vpsi using fun χ : D.X => exists_gen P.isLB (K' := PUnit)
    (φ' := fun _ => ptK (c₀ χ)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (by
      show s ≫ D.xK χ ≫ Φ = _
      rw [hx, ← Category.assoc, s₂, Category.id_comp]))
    (LB.pullGen P.L _ _ (t χ) s) (DVR.pullGen_isGen _ _ _ _ (ht χ) s)
  let D₀ : DegPre V :=
    { P := P, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D.X,
      c := c₀, c_add := cadd, psi := psi, psi_gen := hpsi }
  obtain ⟨ψW⟩ := nonempty_psiOn_generic D₀
  obtain ⟨hD, e⟩ := exists_isPullDeg_of_val hi D₀ D ψW (jK V).isoOpensRange.hom (jK V).isoOpensRange_hom_ι gp w hw hr
    (AddEquiv.refl _) hc (fun x z J J' hJ hJ' => by
      have v := vt x _ (𝟙 _) z _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
      refine (vpsi x _ _ z J hJ).trans ((val_pull hJ _ _ _).trans
        ((congrArg (fun r => val (t x) r z J) s₁).trans (v.trans (congrArg₂ (· * ·) ?_ rfl))))
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp])
  exact ⟨D₀, hD, rfl, heq_of_eq e⟩

/- English proof (translation)
Establish `hi` using `IsFractionRing.injective V K`. Use `letI : Algebra (FractionRing V) (FractionRing K) := (fracMap hi).toAlgebra`. Establish `hK : Compat (algebraMap V K) (FractionRing K)` using `fracMap_algebraMap hi`. Take `⟨σ, h₁, h₂⟩` from `exists_fracInv V K`. Take `⟨q, hy, hg⟩` from `qkPullExists hG V K _ D₀ D hD (FractionRing K) hK k q'`.

Take `⟨p, hp⟩` from `exists_qkExt_of_inverse (F := FractionRing V) (fracMap hi) σ h₁ h₂ q`. Conclude with `⟨p, _, hK, q, hp, hy, hg⟩`.
-/
theorem exists_isPullQk_surj (hG : GlobalFnsSt) {D₀ : DegPre V} {D : DegPre K} (hD : IsPullDeg (algebraMap V K) D₀ D)
    {k : ℕ} (q' : QkPt D (FractionRing K) k) : ∃ q, IsPullQk hD q q' := by
  have hi := IsFractionRing.injective V K
  letI : Algebra (FractionRing V) (FractionRing K) := (fracMap hi).toAlgebra
  have hK : Compat (algebraMap V K) (FractionRing K) := fracMap_algebraMap hi
  obtain ⟨σ, h₁, h₂⟩ := exists_fracInv V K
  obtain ⟨q, hy, hg⟩ := qkPullExists hG V K _ D₀ D hD (FractionRing K) hK k q'
  obtain ⟨p, hp⟩ := exists_qkExt_of_inverse (F := FractionRing V) (fracMap hi) σ h₁ h₂ q
  exact ⟨p, _, hK, q, hp, hy, hg⟩

end Dvr

end GlobalTheory.DvrDeg

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

/- English proof (translation)
Introduce `hK V K _ _ _ _ _ _ Pv DK φ h`. Take `⟨DV, p, h₁, h₂⟩` from `GlobalTheory.DvrDeg.exists_isPullDeg hK.laws.cube Pv DK φ h.2.1 h.2.2.symm`. Conclude with `⟨DV, p, h₁, h₂, fun k q' _ => GlobalTheory.DvrDeg.exists_isPullQk_surj hK.laws.globalFns p q'⟩`.
-/
theorem GlobalTheory.DvrDeg.exists_extension : Known → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (Pv : Out.PolAV (Sp V)) (DK : Out.DegPre K) (φ : DK.P.A.left ⟶ Pv.A.left), IsPolFibre (algebraMap V K) Pv DK.P φ → ∃ (DV : Out.DegPre V) (p : Out.IsPullDeg (algebraMap V K) DV DK), DV.P = Pv ∧ HEq (prj p) φ ∧ ∀ (k : ℕ) (q' : Out.QkPt DK (FractionRing K) k), DK.TauBimult → ∃ q, GlobalTheory.ArcPull.IsPullQk p q q' := by
  intro hK V K _ _ _ _ _ _ Pv DK φ h
  obtain ⟨DV, p, h₁, h₂⟩ := GlobalTheory.DvrDeg.exists_isPullDeg hK.laws.cube Pv DK φ h.2.1 h.2.2.symm
  exact ⟨DV, p, h₁, h₂, fun k q' _ => GlobalTheory.DvrDeg.exists_isPullQk_surj hK.laws.globalFns p q'⟩

end
