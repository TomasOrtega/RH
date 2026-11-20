import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section

namespace GlobalTheory.PsiRing

/- English proof (translation)
Introduce `R V _ _ _ _ φ D D' β v xe gp hv hc hr gam hgam hψ hB`. Take `⟨e, me, he⟩` from `grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf φ))`. Substitute `he` using the available equality. Establish `hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ eSec D.P.A` using `(cubeMapOf gp).e_comm`. Take `⟨W, hW, ⟨ψW⟩⟩` from `PsiSpread.exists_psiOn D hB`.

Take `⟨gW, hgW⟩ : ∃ gW : (TK R).left ⟶ (TW W).left, gW ≫ W.ι = jK R` from `⟨IsOpenImmersion.lift W.ι (jK R) (by`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `TauPull.jK_mem y W ⟨_, hW⟩), IsOpenImmersion.lift_fac _ _ _⟩`. Take `⟨lam, l₁, l₂⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ ∧ lam ≫ (jK R ∣_ W) = gW` from `⟨(isPullback_morphismRestrict (jK R) W).lift _ _ (hgW.trans (Category.id_comp _).symm), (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _, (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩`.

Use `⟨⟨e, me, v, hv, hE, ?_, xe, hc, W, ψW, gam ≫ gW, (Category.assoc _ _ _).trans ((congrArg (gam ≫ ·) hgW).trans hgam), fun x => ?_⟩, rfl, HEq.rfl, rfl⟩` and prove the remaining obligations. Conclude with `(maps_iff v _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _ (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf φ) hE D.P.L) (fun _ => rfl)).2 hr`. Take `⟨b, -, vb⟩` from `exists_up ((isGen_iff v).1 hv) D.P.isLB D'.P.isLB (D'.psi x) (D'.psi_gen x)`. Establish `hx : D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = gam ≫ D.xK (xe x)` using `(Category.assoc _ _ _).trans ((congrArg (jK V ≫ ·) (hc x)).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (D.c (xe x)).left) hgam.symm).trans (Category.assoc _ _ _))))`. Use `⟨b, fun jN jL => unit_ext fun y hy => ?_, corr_of_val D.P.isLB fun y J hJ => ?_⟩` and prove the remaining obligations.

Establish `e₁` using `vb _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)`. Rewrite `e₁` using `[pw, Fintype.prod_unique]`. Use `(gm_res _ y _ hy _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res _ y _ hy _)))))` and prove the remaining obligations. Conclude with `(map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ _ y _ hy _))`. Take `⟨q, hq⟩` from `exists_chart D'.P.isLB (D'.xK x y)`.

Take `⟨p, hp⟩ : ∃ p, p = J (D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))` from `⟨_, rfl⟩`. Establish `mp : (e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (D'.xK x y) ∈ D.P.L.U p` using `hp ▸ hJ _`. Establish `e₁` using `vb _ (𝟙 _) y (fun _ => p) (fun _ => q) (Set.mem_iInter.2 fun _ => mp) (Set.mem_iInter.2 fun _ => hq)`. Establish `e₂` using `hψ x _ (𝟙 _) y (fun _ => p) (fun _ => q) (fun _ => mp) (fun _ => hq)`. Establish `w₁` using `(val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) (gam ≫ lam)).trans (val_pull hJ _ _ _))`.

Rewrite `w₁` using `[Category.assoc, Category.assoc, l₁, l₂, Category.comp_id]`. Use `(val_of b _ y J (fun _ => p) (fun _ => by rw [Category.id_comp, hp])).trans (e₁.trans (e₂.symm.trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)))` and prove the remaining obligations. Rewrite using `[Category.id_comp, Category.id_comp]`. Conclude with `(val_of (D.psi (xe x)) gam y J (fun _ => p) (fun _ => by rw [hp, hx])).symm.trans w₁.symm`.
-/
theorem exists_isPullDeg_of_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D.TauBimult → ∃ hD : IsPullDeg φ D D', hD.e.hom.left ≫ pullback.fst _ _ = β ∧ HEq hD.w v ∧ hD.xe = xe := by
  intro R V _ _ _ _ φ D D' β v xe gp hv hc hr gam hgam hψ hB
  obtain ⟨e, me, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf φ))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨W, hW, ⟨ψW⟩⟩ := PsiSpread.exists_psiOn D hB
  obtain ⟨gW, hgW⟩ : ∃ gW : (TK R).left ⟶ (TW W).left, gW ≫ W.ι = jK R :=
    ⟨IsOpenImmersion.lift W.ι (jK R) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact TauPull.jK_mem y W ⟨_, hW⟩), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ ∧
      lam ≫ (jK R ∣_ W) = gW :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ (hgW.trans (Category.id_comp _).symm),
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  refine ⟨⟨e, me, v, hv, hE, ?_, xe, hc, W, ψW, gam ≫ gW,
    (Category.assoc _ _ _).trans ((congrArg (gam ≫ ·) hgW).trans hgam), fun x => ?_⟩, rfl, HEq.rfl, rfl⟩
  · exact (maps_iff v _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf φ) hE D.P.L) (fun _ => rfl)).2 hr
  · obtain ⟨b, -, vb⟩ := exists_up ((isGen_iff v).1 hv) D.P.isLB D'.P.isLB (D'.psi x) (D'.psi_gen x)
    have hx : D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = gam ≫ D.xK (xe x) :=
      (Category.assoc _ _ _).trans ((congrArg (jK V ≫ ·) (hc x)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (D.c (xe x)).left) hgam.symm).trans (Category.assoc _ _ _))))
    refine ⟨b, fun jN jL => unit_ext fun y hy => ?_, corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · have e₁ := vb _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
      rw [pw, Fintype.prod_unique] at e₁
      refine (gm_res _ y _ hy _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) ?_ (gm_res _ y _ hy _)))))
      exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ _ y _ hy _))
    · obtain ⟨q, hq⟩ := exists_chart D'.P.isLB (D'.xK x y)
      obtain ⟨p, hp⟩ : ∃ p, p = J (D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := ⟨_, rfl⟩
      have mp : (e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (D'.xK x y) ∈ D.P.L.U p := hp ▸ hJ _
      have e₁ := vb _ (𝟙 _) y (fun _ => p) (fun _ => q) (Set.mem_iInter.2 fun _ => mp) (Set.mem_iInter.2 fun _ => hq)
      have e₂ := hψ x _ (𝟙 _) y (fun _ => p) (fun _ => q) (fun _ => mp) (fun _ => hq)
      have w₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) (gam ≫ lam)).trans (val_pull hJ _ _ _))
      rw [Category.assoc, Category.assoc, l₁, l₂, Category.comp_id] at w₁
      refine (val_of b _ y J (fun _ => p) (fun _ => by rw [Category.id_comp, hp])).trans (e₁.trans (e₂.symm.trans
        (Eq.trans ?_ (val_pull hJ _ _ _).symm)))
      rw [Category.id_comp, Category.id_comp]
      exact (val_of (D.psi (xe x)) gam y J (fun _ => p) (fun _ => by rw [hp, hx])).symm.trans w₁.symm

end GlobalTheory.PsiRing

end
