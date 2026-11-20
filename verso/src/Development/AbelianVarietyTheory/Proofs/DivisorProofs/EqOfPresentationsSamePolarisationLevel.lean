import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.LowSame

open GlobalTheory.SiegLev GlobalTheory.CechPic GlobalTheory.AmpleRigid GlobalTheory.SiegRigid

/- English proof (translation)
Take `⟨σ, hσ, e⟩` from `exists_aut g g'`. Establish `key : σ.hom = 𝟙 _`. Use `eq_id_of_forall_geometric_fibre laws_without_cohomology.1 A' hab' σ.hom (IsMonHom.one_hom σ.hom) fun t => ?_` and prove the remaining obligations. Set `K : Type` to `AlgebraicClosure (S'.residueField t)`. Set `j : Sp K ⟶ S'` to `Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t`.

Establish `hp` using `isGrpPullback_pullback A' j`. Use `hab'.smooth` as an intermediate fact. Use `hab'.proper` as an intermediate fact. Use `hab'.geomConnected` as an intermediate fact. Use `hab'.comm` as an intermediate fact.

Establish `hab : IsAbelianScheme ((Over.pullback j).obj A')` using `{ comm := Functor.isCommMonObj_obj smooth := by change Smooth (pullback.snd A'.hom j); infer_instance proper := by change IsProper (pullback.snd A'.hom j); infer_instance geomConnected := by change GeometricallyConnected (pullback.snd A'.hom j); infer_instance }`. Establish `hNK : (n : K) ≠ 0`. Establish `hu` using `hnB.map (Spec.preimage ((j ≫ f) ≫ s)).hom`. Rewrite `hu` using `[map_natCast]`. Conclude with `hu.ne_zero`.

Establish `e'` using `eq_of_field (pull_isLB c.isLB _) hc.1 hab (hp.comp g) (hp.comp g') (by rw [pull_comp, pull_comp]; exact congrArg _ hcl) hn hNK fun Ω _ _ x y hy => by`. Establish `hy₁ : pushHom hp (Over.mk x) y ^ n = 1` using `by rw [← map_pow, hy, map_one]`. Establish `e₁` using `eq_on_torsion hζ c g lv l l' Ω (x ≫ j) _ hy₁`. Rewrite using `[← Category.assoc, ← Category.assoc]`. Conclude with `e₁`.

Use `⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩` and prove the remaining obligations. Conclude with `(Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)`. Apply `g'.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, e]`. Conclude with `e'`.

Rewrite using `[Category.assoc, Over.w]`. Rewrite using `[← e, key, Over.id_left, Category.id_comp]`.
-/
theorem eq_of_cls_lev {h n : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B}
    (c : SiegPre h n ζ s) (hζ : IsUnit ζ) (hnB : IsUnit (n : B)) (hn : 3 ≤ n) (hc : c.Principal)
    {A' : Over S'} [GrpObj A'] (hab' : IsAbelianScheme A') (f : S' ⟶ S) (φ φ' : A'.left ⟶ c.A.left)
    (g : IsGrpPullback A' c.A f φ) (g' : IsGrpPullback A' c.A f φ')
    (hcl : pull φ (cls c.diag (pull_isLB c.isLB _)) = pull φ' (cls c.diag (pull_isLB c.isLB _)))
    (lv : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ A'))
    (l : ∀ a, (lv a).left ≫ φ = f ≫ (c.lev a).left) (l' : ∀ a, (lv a).left ≫ φ' = f ≫ (c.lev a).left) :
    φ = φ' := by
  obtain ⟨σ, hσ, e⟩ := exists_aut g g'
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 A' hab' σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t
    have hp := isGrpPullback_pullback A' j
    have := hab'.smooth
    have := hab'.proper
    have := hab'.geomConnected
    have := hab'.comm
    have hab : IsAbelianScheme ((Over.pullback j).obj A') :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd A'.hom j); infer_instance
        proper := by change IsProper (pullback.snd A'.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd A'.hom j); infer_instance }
    have hNK : (n : K) ≠ 0 := by
      have hu := hnB.map (Spec.preimage ((j ≫ f) ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have e' := eq_of_field (pull_isLB c.isLB _) hc.1 hab (hp.comp g) (hp.comp g')
      (by rw [pull_comp, pull_comp]; exact congrArg _ hcl) hn hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ n = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion hζ c g lv l l' Ω (x ≫ j) _ hy₁
        rw [← Category.assoc, ← Category.assoc]
        exact e₁
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · apply g'.1.hom_ext
      · rw [Category.assoc, e]
        exact e'
      · rw [Category.assoc, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

end GlobalTheory.LowSame

namespace GlobalTheory.LowSame

open GlobalTheory.SiegelPullComp

/- English proof (translation)
Introduce `o _ ζ h n F' hn hζ hno V _ _ _ A _ _ t₁ t₂ a₁ a₂ aa₁ aa₂ ha₁ ha₂ sq₁ sq₂ hP hs F _ _ hlev`. Set `c'` to `GlobalTheory.LowChart.siegPull F'.univ t₁ (t₁ ≫ F'.s) rfl`. Establish `m₁ : SiegPB c' F'.univ t₁` using `GlobalTheory.LowChart.siegPB_siegPull _ _ _ _`. Take `⟨pφ, pφ₂, gp, psq, pw, pl⟩` from `id m₁`. Set `F₀ : c'.A.left ⟶ A.left` to `ha₁.1.lift pφ c'.A.hom gp.1.w`.

Establish `hF : F₀ ≫ a₁ = pφ` using `ha₁.1.lift_fst _ _ _`. Establish `hFw : F₀ ≫ A.hom = c'.A.hom ≫ 𝟙 _` using `(ha₁.1.lift_snd _ _ _).trans (Category.comp_id _).symm`. Establish `hF₀ : IsGrpPullback c'.A A (𝟙 _) F₀` using `ha₁.cancel (gp.congr (Category.id_comp _).symm hF.symm) hFw`. Establish `gφ : IsGrpPullback c'.A F'.univ.A t₂ (F₀ ≫ a₂)` using `(hF₀.comp ha₂).congr (Category.id_comp _) rfl`. Set `U : Over.mk ((c'.A ⊗ c'.A).hom ≫ 𝟙 _) ⟶ A ⊗ A` to `lift (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A))`.

Set `F₂ : (c'.A ⊗ c'.A).left ⟶ (A ⊗ A).left` to `U.left`. Establish `h₁ : F₂ ≫ (fst A A).left = (fst c'.A c'.A).left ≫ F₀` using `congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A)))`. Establish `h₂ : F₂ ≫ (snd A A).left = (snd c'.A c'.A).left ≫ F₀` using `congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A)))`. Establish `h₃ : F₂ ≫ aa₁ = pφ₂`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Use `show (_ ≫ _) ≫ (fst F'.univ.A F'.univ.A).left = _ ≫ (fst F'.univ.A F'.univ.A).left`. Rewrite using `[Category.assoc, sq₁.1, ← Category.assoc, h₁, Category.assoc, hF, psq.1]`. Use `show (_ ≫ _) ≫ (snd F'.univ.A F'.univ.A).left = _ ≫ (snd F'.univ.A F'.univ.A).left`. Rewrite using `[Category.assoc, sq₁.2, ← Category.assoc, h₂, Category.assoc, hF, psq.2]`. Establish `sq : IsSquare (F₀ ≫ a₂) (F₂ ≫ aa₂)` using `⟨by rw [Category.assoc, sq₂.1, ← Category.assoc, h₁, Category.assoc], by rw [Category.assoc, sq₂.2, ← Category.assoc, h₂, Category.assoc]⟩`.

Establish `hU` using `F'.univ.isLB`. Establish `iso : LBIso c'.P (F'.univ.P.pull (F₂ ≫ aa₂))`. Rewrite `pw` using `[← h₃]`. Use `pw.trans c'.isLB (pull_isLB hU _) (pull_isLB hU _) ?_` and prove the remaining obligations. Use `(iso_pull_pull hU aa₁ F₂).symm.trans (pull_isLB hU _) (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) ?_` and prove the remaining obligations.

Use `(iso_pull F₂ hP).trans (pull_isLB (pull_isLB hU _) _) (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) ?_` and prove the remaining obligations. Conclude with `iso_pull_pull hU aa₂ F₂`. Establish `lev : ∀ a, (c'.lev a).left ≫ (F₀ ≫ a₂) = t₂ ≫ (F'.univ.lev a).left`. Introduce `a`. Establish `hσ : ((c'.lev a).left ≫ F₀) ≫ A.hom = 𝟙 _`.

Rewrite using `[Category.assoc, hFw, Category.comp_id]`. Conclude with `Over.w (c'.lev a)`. Establish `hσ₁ : ((c'.lev a).left ≫ F₀) ≫ a₁ = t₁ ≫ (F'.univ.lev a).left`. Rewrite using `[Category.assoc, hF]`. Conclude with `pl a`.

Take `⟨x, hx₁, hx₂⟩` from `hlev a`. Establish `hx : x.left = (TF (R` using `V) F).hom ≫ (c'.lev a).left ≫ F₀ := by`. Apply `ha₁.1.hom_ext` to reduce the goal to its premises. Rewrite using `[hx₁, Category.assoc, hσ₁]`. Rewrite using `[Over.w x, Category.assoc, hσ]`.

Conclude with `(Category.comp_id _).symm`. Use `F'.univ.ab.proper` as an intermediate fact. Establish `: IsReduced (𝟙_ (Over (Sp V))).left` using `(inferInstance : IsReduced (Sp V))`. Use `ReciprocityTheory.ChartRestriction.G.DVR.GC.isDominant_jFR (V := V) F` as an intermediate fact. Use `ext_of_isDominant_of_isSeparated F'.univ.A.hom ?_ (DegPre.jFR (R := V) F) ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, Category.assoc, ha₂.1.w, ← Category.assoc, ← Category.assoc, hσ, Category.id_comp, Category.assoc, Over.w (F'.univ.lev a)]`. Both sides reduce to the same expression. Rewrite using `[← Category.assoc] show ((TF (R := V) F).hom ≫ (c'.lev a).left ≫ F₀) ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (F'.univ.lev a).left`. Rewrite using `[← hx]`. Conclude with `hx₂`.

Establish `m₂ : SiegPB c' F'.univ t₂` using `⟨F₀ ≫ a₂, F₂ ≫ aa₂, gφ, sq, iso, lev⟩`. Establish `ht : t₁ = t₂` using `F'.inj V t₁ t₂ (t₁ ≫ F'.s) c' hs m₁ m₂`. Substitute `ht` using the available equality. Use `⟨rfl, ?_⟩` and prove the remaining obligations. Establish `hcl` using `(GlobalTheory.SiegRigid.pull_cls_diag psq pw).trans (GlobalTheory.SiegRigid.pull_cls_diag sq iso).symm`.

Establish `e` using `eq_of_cls_lev F'.univ hζ hno hn F'.princ c'.ab t₁ pφ (F₀ ≫ a₂) gp gφ hcl c'.lev pl lev`. Establish `: IsIso F₀` using `hF₀.1.isIso_fst_of_isIso`. Rewrite `e` using `[← hF]`. Conclude with `(cancel_epi F₀).1 e`.
-/
theorem eq_of_presentations : ∀ {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F' : SFam h n ζ), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (t₁ t₂ : Sp V ⟶ F'.X) (a₁ a₂ : A.left ⟶ F'.univ.A.left) (aa₁ aa₂ : (G2 A).left ⟶ (G2 F'.univ.A).left), IsGrpPullback A F'.univ.A t₁ a₁ → IsGrpPullback A F'.univ.A t₂ a₂ → IsSquare a₁ aa₁ → IsSquare a₂ aa₂ → LBIso (F'.univ.P.pull aa₁) (F'.univ.P.pull aa₂) → t₁ ≫ F'.s = t₂ ≫ F'.s → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F], (∀ l, ∃ x : TF (R := V) F ⟶ A, x.left ≫ a₁ = (TF (R := V) F).hom ≫ t₁ ≫ (F'.univ.lev l).left ∧ x.left ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (F'.univ.lev l).left) → t₁ = t₂ ∧ a₁ = a₂ := by
  intro o _ ζ h n F' hn hζ hno V _ _ _ A _ _ t₁ t₂ a₁ a₂ aa₁ aa₂ ha₁ ha₂ sq₁ sq₂ hP hs F _ _ hlev
  let c' := GlobalTheory.LowChart.siegPull F'.univ t₁ (t₁ ≫ F'.s) rfl
  have m₁ : SiegPB c' F'.univ t₁ := GlobalTheory.LowChart.siegPB_siegPull _ _ _ _
  obtain ⟨pφ, pφ₂, gp, psq, pw, pl⟩ := id m₁
  let F₀ : c'.A.left ⟶ A.left := ha₁.1.lift pφ c'.A.hom gp.1.w
  have hF : F₀ ≫ a₁ = pφ := ha₁.1.lift_fst _ _ _
  have hFw : F₀ ≫ A.hom = c'.A.hom ≫ 𝟙 _ := (ha₁.1.lift_snd _ _ _).trans (Category.comp_id _).symm
  have hF₀ : IsGrpPullback c'.A A (𝟙 _) F₀ :=
    ha₁.cancel (gp.congr (Category.id_comp _).symm hF.symm) hFw
  have gφ : IsGrpPullback c'.A F'.univ.A t₂ (F₀ ≫ a₂) := (hF₀.comp ha₂).congr (Category.id_comp _) rfl
  let U : Over.mk ((c'.A ⊗ c'.A).hom ≫ 𝟙 _) ⟶ A ⊗ A :=
    lift (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A))
  let F₂ : (c'.A ⊗ c'.A).left ⟶ (A ⊗ A).left := U.left
  have h₁ : F₂ ≫ (fst A A).left = (fst c'.A c'.A).left ≫ F₀ :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A)))
  have h₂ : F₂ ≫ (snd A A).left = (snd c'.A c'.A).left ≫ F₀ :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A)))
  have h₃ : F₂ ≫ aa₁ = pφ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst F'.univ.A F'.univ.A).left = _ ≫ (fst F'.univ.A F'.univ.A).left
      rw [Category.assoc, sq₁.1, ← Category.assoc, h₁, Category.assoc, hF, psq.1]
    · show (_ ≫ _) ≫ (snd F'.univ.A F'.univ.A).left = _ ≫ (snd F'.univ.A F'.univ.A).left
      rw [Category.assoc, sq₁.2, ← Category.assoc, h₂, Category.assoc, hF, psq.2]
  have sq : IsSquare (F₀ ≫ a₂) (F₂ ≫ aa₂) :=
    ⟨by rw [Category.assoc, sq₂.1, ← Category.assoc, h₁, Category.assoc],
     by rw [Category.assoc, sq₂.2, ← Category.assoc, h₂, Category.assoc]⟩
  have hU := F'.univ.isLB
  have iso : LBIso c'.P (F'.univ.P.pull (F₂ ≫ aa₂)) := by
    rw [← h₃] at pw
    refine pw.trans c'.isLB (pull_isLB hU _) (pull_isLB hU _) ?_
    refine (iso_pull_pull hU aa₁ F₂).symm.trans (pull_isLB hU _) (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) ?_
    refine (iso_pull F₂ hP).trans (pull_isLB (pull_isLB hU _) _) (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) ?_
    exact iso_pull_pull hU aa₂ F₂
  have lev : ∀ a, (c'.lev a).left ≫ (F₀ ≫ a₂) = t₂ ≫ (F'.univ.lev a).left := by
    intro a
    have hσ : ((c'.lev a).left ≫ F₀) ≫ A.hom = 𝟙 _ := by
      rw [Category.assoc, hFw, Category.comp_id]
      exact Over.w (c'.lev a)
    have hσ₁ : ((c'.lev a).left ≫ F₀) ≫ a₁ = t₁ ≫ (F'.univ.lev a).left := by
      rw [Category.assoc, hF]; exact pl a
    obtain ⟨x, hx₁, hx₂⟩ := hlev a
    have hx : x.left = (TF (R := V) F).hom ≫ (c'.lev a).left ≫ F₀ := by
      apply ha₁.1.hom_ext
      · rw [hx₁, Category.assoc, hσ₁]
      · rw [Over.w x, Category.assoc, hσ]
        exact (Category.comp_id _).symm
    have := F'.univ.ab.proper
    have : IsReduced (𝟙_ (Over (Sp V))).left := (inferInstance : IsReduced (Sp V))
    have := ReciprocityTheory.ChartRestriction.G.DVR.GC.isDominant_jFR (V := V) F
    refine ext_of_isDominant_of_isSeparated F'.univ.A.hom ?_ (DegPre.jFR (R := V) F) ?_
    · rw [Category.assoc, Category.assoc, ha₂.1.w, ← Category.assoc, ← Category.assoc, hσ, Category.id_comp,
        Category.assoc, Over.w (F'.univ.lev a)]
      rfl
    · rw [← Category.assoc]
      show ((TF (R := V) F).hom ≫ (c'.lev a).left ≫ F₀) ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (F'.univ.lev a).left
      rw [← hx]
      exact hx₂
  have m₂ : SiegPB c' F'.univ t₂ := ⟨F₀ ≫ a₂, F₂ ≫ aa₂, gφ, sq, iso, lev⟩
  have ht : t₁ = t₂ := F'.inj V t₁ t₂ (t₁ ≫ F'.s) c' hs m₁ m₂
  subst ht
  refine ⟨rfl, ?_⟩
  have hcl := (GlobalTheory.SiegRigid.pull_cls_diag psq pw).trans (GlobalTheory.SiegRigid.pull_cls_diag sq iso).symm
  have e := eq_of_cls_lev F'.univ hζ hno hn F'.princ c'.ab t₁ pφ (F₀ ≫ a₂) gp gφ hcl c'.lev pl lev
  have : IsIso F₀ := hF₀.1.isIso_fst_of_isIso
  rw [← hF] at e
  exact (cancel_epi F₀).1 e

end GlobalTheory.LowSame

end
