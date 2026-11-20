import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsDegenerationDataExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.PullDegUniq

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

/- English proof (translation)
Establish `hm : (specOf φ ∣_ hD.W) ≫ hD.W.ι = (specOf φ ⁻¹ᵁ hD.W).ι ≫ specOf φ` using `morphismRestrict_ι _ _`. Establish `key : ∀ x : D'.X, ∃ a : LB.Gen (LB.LinComb D'.P.L (K` using `PUnit) (fun _ => (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left) (fun _ => -1)), a.IsGen ∧ LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ a (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W))) (LB.pullGen D'.P.L _ _ (D'.psi x) (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι) := by`. Introduce `x`. Establish `hψ : (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left ≫ proj hD = (specOf φ ∣_ hD.W) ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left` using `by show (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = (specOf φ ∣_ hD.W) ≫ hD.W.ι ≫ (D.c (hD.xe x)).left`. Rewrite using `[hD.c_pr x, ← Category.assoc, ← Category.assoc, hm]`.

Take `⟨a, ha, H⟩` from `DegPull.exists_pmaps ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (K := PUnit) (ε := fun _ => -1) (specOf φ ∣_ hD.W) (fun _ => hψ) (hD.psiW.psi (hD.xe x)) (hD.psiW.psi_gen _)`. Use `⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩` and prove the remaining obligations. Take `⟨J, hJ⟩` from `DegPull.exists_good' D.P.isLB y`. Establish `hz : ((jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ∣_ hD.W)) ≫ hD.W.ι = (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ specOf φ`. Rewrite using `[Category.assoc, hm, ← Category.assoc, morphismRestrict_ι, Category.assoc]`.

Take `⟨hp, P⟩` from `ArcSpecialise.pmaps_psiOn hD hD.psiW _ _ hz x`. Establish `v₁` using `DegPull.pmaps_val (fun _ => hψ) H (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) y hJ hJ'`. Establish `v₂` using `DegPull.pmaps_val (fun _ => hp) P (𝟙 _) y hJ hJ'`. Rewrite using `[val_pull hJ', val_pull hJ']`. Rewrite `v₂` using `[val_pull hJ, val_pull hJ']`.

Simplify using `only [Category.id_comp] at v₁ v₂ ⊢`. Establish `hmor : (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left = (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ D'.xK x` using `by show (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left = (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ (D'.c x).left`. Rewrite using `[← Category.assoc, morphismRestrict_ι, Category.assoc]`. Rewrite `v₁` using `[hmor]`. Conclude with `mul_left_cancel (v₁.symm.trans v₂)`.

Use `choose a ha hc using key`. Conclude with `⟨⟨a, ha, hc⟩⟩`.
-/
theorem nonempty_psiOn_pull {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    Nonempty (PsiOn D' (specOf φ ⁻¹ᵁ hD.W)) := by
  have hm : (specOf φ ∣_ hD.W) ≫ hD.W.ι = (specOf φ ⁻¹ᵁ hD.W).ι ≫ specOf φ := morphismRestrict_ι _ _
  have key : ∀ x : D'.X, ∃ a : LB.Gen (LB.LinComb D'.P.L (K := PUnit)
      (fun _ => (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left) (fun _ => -1)), a.IsGen ∧
      LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ a (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)))
        (LB.pullGen D'.P.L _ _ (D'.psi x) (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι) := by
    intro x
    have hψ : (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left ≫ proj hD =
        (specOf φ ∣_ hD.W) ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left := by
      show (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
        (specOf φ ∣_ hD.W) ≫ hD.W.ι ≫ (D.c (hD.xe x)).left
      rw [hD.c_pr x, ← Category.assoc, ← Category.assoc, hm]
    obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (K := PUnit)
      (ε := fun _ => -1) (specOf φ ∣_ hD.W) (fun _ => hψ) (hD.psiW.psi (hD.xe x)) (hD.psiW.psi_gen _)
    refine ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have hz : ((jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ∣_ hD.W)) ≫ hD.W.ι =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ specOf φ := by
      rw [Category.assoc, hm, ← Category.assoc, morphismRestrict_ι, Category.assoc]
    obtain ⟨hp, P⟩ := ArcSpecialise.pmaps_psiOn hD hD.psiW _ _ hz x
    have v₁ := DegPull.pmaps_val (fun _ => hψ) H (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) y hJ hJ'
    have v₂ := DegPull.pmaps_val (fun _ => hp) P (𝟙 _) y hJ hJ'
    rw [val_pull hJ', val_pull hJ']
    rw [val_pull hJ, val_pull hJ'] at v₂
    simp only [Category.id_comp] at v₁ v₂ ⊢
    have hmor : (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ D'.xK x := by
      show (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ (D'.c x).left
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    rw [hmor] at v₁
    exact mul_left_cancel (v₁.symm.trans v₂)
  choose a ha hc using key
  exact ⟨⟨a, ha, hc⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨(isPullback_morphismRestrict (specOf φ) hD.W).lift hD.g (jK R') hD.g_comm, (isPullback_morphismRestrict (specOf φ) hD.W).lift_snd _ _ _⟩`.
-/
theorem exists_generic_section {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    ∃ s : (TK R').left ⟶ (specOf φ ⁻¹ᵁ hD.W).toScheme, s ≫ (specOf φ ⁻¹ᵁ hD.W).ι = jK R' :=
  ⟨(isPullback_morphismRestrict (specOf φ) hD.W).lift hD.g (jK R') hD.g_comm,
    (isPullback_morphismRestrict (specOf φ) hD.W).lift_snd _ _ _⟩

/- English proof (translation)
Establish `p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁)` using `pull_grp h₁`. Establish `sc : spMap β ≫ spMap α = spMap (β.comp α)` using `(spMap_comp α β).symm`. Establish `p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h)` using `(pull_grp h).congr sc.symm rfl`. Take `⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β` from `⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _, p₁.1.lift_snd _ _ _⟩`. Establish `gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ` using `IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂`.

Take `⟨w, hw, hr, T⟩` from `FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁) (FieldPull.pmaps_rig h)`. Set `xe : D.X ≃+ D₁.X` to `h.xe.trans h₁.xe.symm`. Establish `hxe : ∀ x, h₁.xe (xe x) = h.xe x` using `fun x => h₁.xe.apply_symm_apply _`. Establish `hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left` using `fun x => by`. Apply `p₁.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]`. Conclude with `(h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))`. Rewrite using `[Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]`. Conclude with `(Category.id_comp _).trans (Category.comp_id _).symm`. Take `⟨ψW⟩` from `nonempty_psiOn_pull h₁`.

Take `⟨s, hs⟩` from `exists_generic_section h₁`. Take `⟨hD, -⟩` from `DvrDeg.exists_isPullDeg_of_val hβ D₁ D ψW s hs gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by`. Take `⟨J₀, hJ₀⟩` from `DegPull.exists_good' D₀.P.isLB z`. Establish `sβ : jK R₂ ≫ spMap β = genMap hβ ≫ jK R₁` using `(Category.id_comp _).symm.trans (fracMap_sq hβ)`. Establish `sα : jK R₁ ≫ spMap α = genMap hα ≫ jK R₀` using `(Category.id_comp _).symm.trans (fracMap_sq hα)`.

Establish `q₁ : genMap hβ ≫ jK R₁ ≫ spMap α = (genMap hβ ≫ genMap hα) ≫ jK R₀` using `(congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm`. Establish `q : 𝟙 (TK R₂).left ≫ jK R₂ ≫ spMap (β.comp α) = (genMap hβ ≫ genMap hα) ≫ jK R₀` using `(Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))`. Establish `v` using `psi_val h _ _ q hJ₀ hJ x`. Establish `v₁` using `psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)`. Establish `hx : D.xK x ≫ Φ = genMap hβ ≫ D₁.xK (xe x)` using `by show (jK R₂ ≫ (D.c x).left) ≫ Φ = genMap hβ ≫ jK R₁ ≫ (D₁.c (xe x)).left`.

Rewrite using `[Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]`. Rewrite `v₁` using `[hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc]`. Conclude with `(mul_left_cancel v₁).symm)`. Conclude with `⟨hD⟩`.
-/
theorem nonempty_isPullDeg_cancel {R₀ R₁ R₂ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁]
    [CommRing R₂] [IsDomain R₂] {α : R₀ →+* R₁} {β : R₁ →+* R₂} (hα : Function.Injective α)
    (hβ : Function.Injective β) {D₀ : DegPre R₀} {D₁ : DegPre R₁} {D : DegPre R₂} (h₁ : IsPullDeg α D₀ D₁)
    (h : IsPullDeg (β.comp α) D₀ D) : Nonempty (IsPullDeg β D₁ D) := by
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW⟩ := nonempty_psiOn_pull h₁
  obtain ⟨s, hs⟩ := exists_generic_section h₁
  obtain ⟨hD, -⟩ := DvrDeg.exists_isPullDeg_of_val hβ D₁ D ψW s hs gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK R₂ ≫ spMap β = genMap hβ ≫ jK R₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq hβ)
    have sα : jK R₁ ≫ spMap α = genMap hα ≫ jK R₀ :=
      (Category.id_comp _).symm.trans (fracMap_sq hα)
    have q₁ : genMap hβ ≫ jK R₁ ≫ spMap α = (genMap hβ ≫ genMap hα) ≫ jK R₀ :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK R₂).left ≫ jK R₂ ≫ spMap (β.comp α) = (genMap hβ ≫ genMap hα) ≫ jK R₀ :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap hβ ≫ D₁.xK (xe x) := by
      show (jK R₂ ≫ (D.c x).left) ≫ Φ = genMap hβ ≫ jK R₁ ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD⟩

end GlobalTheory.PullDegUniq

namespace GlobalTheory.Mum

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ R' _ _ _ _ ρ hρ _ _ _ ⟨p₁⟩ ⟨p₂⟩ => GlobalTheory.PullDegUniq.nonempty_isPullDeg_cancel (β := RingHom.id R') hρ Function.injective_id p₁ ((RingHom.id_comp ρ).symm ▸ p₂), fun _ _ _ _ _ _ _ _ _ _ _ hρ hρ' _ _ _ ⟨p⟩ ⟨q⟩ => GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hρ hρ' …`.
-/
theorem isPullDeg_unique_and_comp : (∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (D : DegPre R) (D₁ D₂ : DegPre R'), Nonempty (IsPullDeg ρ D D₁) → Nonempty (IsPullDeg ρ D D₂) → Nonempty (IsPullDeg (RingHom.id R') D₁ D₂)) ∧ ∀ (R R' R'' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] (ρ : R →+* R') (ρ' : R' →+* R''), Function.Injective ρ → Function.Injective ρ' → ∀ (D : DegPre R) (D' : DegPre R') (D'' : DegPre R''), Nonempty (IsPullDeg ρ D D') → Nonempty (IsPullDeg ρ' D' D'') → Nonempty (IsPullDeg (ρ'.comp ρ) D D'') :=
  ⟨fun _ R' _ _ _ _ ρ hρ _ _ _ ⟨p₁⟩ ⟨p₂⟩ =>
    GlobalTheory.PullDegUniq.nonempty_isPullDeg_cancel (β := RingHom.id R') hρ Function.injective_id p₁
      ((RingHom.id_comp ρ).symm ▸ p₂),
   fun _ _ _ _ _ _ _ _ _ _ _ hρ hρ' _ _ _ ⟨p⟩ ⟨q⟩ => GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hρ hρ' p q⟩

end GlobalTheory.Mum
