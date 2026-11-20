import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CorrOfValFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ArcPull PsiEvenPull

/- English proof (translation)
Introduce `hG K₀ K _ _ i D D' hD O _ _ _ _ oB oa' hx ho`. Establish `gp` using `pull_grp hD`. Establish `hφ : Function.Injective i` using `i.injective`. Use `FieldBaseChange.flat_spMap i` as an intermediate fact. Use `FieldBaseChange.surjective_spMap i` as an intermediate fact.

Establish `: Epi (spMap i)` using `Flat.epi_of_flat_of_surjective _`. Establish `cl : ∀ (a : O) y, D.c (a • y) = D.c y ≫ oB.act a` using `fun a y => by`. Take `⟨y, rfl⟩` from `hD.xe.surjective y`. Use `Over.OverMorphism.ext ((cancel_epi (spMap i)).1 ?_)` and prove the remaining obligations. Establish `e₁` using `hD.c_pr (a • y)`.

Establish `e₂` using `hD.c_pr y`. Rewrite `e₁` using `[oa'.c_lin, Over.comp_left, Category.assoc, hx]`. Use `e₁.symm.trans ((congrArg (_ ≫ ·) (ho a)).trans ?_)` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans (Category.assoc _ _ _))`. Use `⟨⟨oB, cl, fun a u hu u₀ y y' => ?_⟩, rfl⟩` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `hD.xe.surjective y`. Take `⟨y', rfl⟩` from `hD.xe.surjective y'`. Use `corr_of_val_field_extension _ _ (fracMap hφ) _ _ D.P.isLB _ _ _ _ _ _ _ _ fun z J hJ => ?_` and prove the remaining obligations. Take `⟨J', hJ'⟩` from `DegPull.exists_good' D'.P.isLB z`. Use `oa'.onB.hom a` as an intermediate fact.

Use `oa'.onB.hom (star a)` as an intermediate fact. Use `oB.hom a` as an intermediate fact. Use `oB.hom (star a)` as an intermediate fact. Take `⟨u', hu', h₀⟩` from `exists_ros hG D'.P.isAb D'.P.isLB _ _ (oa'.onB.rosati a)`. Establish `sq` using `fracMap_sq hφ`.

Establish `hh : (TK K).hom ≫ spMap i = genMap hφ ≫ (TK K₀).hom` using `(Category.id_comp _).symm.trans sq`. Establish `e` using `val_corr hJ' (oa'.tau_bal a u' hu' h₀ y y') (𝟙 (TK K).left)`. Establish `v` using `ros_val hG gp D'.P.isAb D.P.isLB D'.P.isLB hD.w_gen (ho a) (ho (star a)) ⟨hu, u₀⟩ ⟨hu', h₀⟩ (cP D' (TK K) y) (cP D' (TK K) y') (genMap hφ ≫ D.pt2 (hD.xe y) (hD.xe y')) ((cPoint_proj hD _ hh y).trans (by`. Rewrite using `[Category.assoc, DegPre.pt2, ← Over.comp_left, lift_fst]`. Use the proof step `rfl))`.

Use the proof step `((cPoint_proj hD _ hh y').trans (by`. Rewrite using `[Category.assoc, DegPre.pt2, ← Over.comp_left, lift_snd]`. Use the proof step `rfl)) hJ hJ'`. Establish `cs : ∀ (a : O) y, cP D' (TK K) y ≫ oa'.onB.act a = cP D' (TK K) (a • y)` using `fun a y => by`. Rewrite using `[cP, cP, oa'.c_lin, Category.assoc]`.

Rewrite `v` using `[cs, cs, ← cPoint_add, ← cPoint_add]`. Rewrite `e` using `[val_mul hJ', val_pull hJ']`. Use `erw [Category.id_comp] at e`. Use `beta_reduce at e`. Use `show val _ (genMap hφ) z J = val _ (genMap hφ) z J`.

Rewrite using `[val_mul hJ, val_pull hJ, v]`. Use `beta_reduce`. Rewrite using `[← hx, ← hx, tau_val hD _ _ sq hJ hJ', tau_val hD _ _ sq hJ hJ']`. Simplify using `only [Category.id_comp]`. Establish `e'` using `congrArg Additive.ofMul e`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `c₀ : ∀ x, (cP D' (TK K) x).left = D'.xK x` using `fun _ => rfl`. Establish `c₁ : val₂ u' z J' (cP D' (TK K) y) (cP D' (TK K) y') = val u' (D'.pt2 y y') z J'` using `rfl`. Simplify using `only [ofMul_mul, ofMul_inv, c₀, c₁] at e' ⊢`. Take the linear combination `(norm := abel) e'`.
-/
theorem exists_oAct_of_field_extension : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oB : D.P.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oB.act a).left) → ∃ oa : D.OAct O, oa.onB = oB := by
  intro hG K₀ K _ _ i D D' hD O _ _ _ _ oB oa' hx ho
  have gp := pull_grp hD
  have hφ : Function.Injective i := i.injective
  have := FieldBaseChange.flat_spMap i
  have := FieldBaseChange.surjective_spMap i
  have : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
  have cl : ∀ (a : O) y, D.c (a • y) = D.c y ≫ oB.act a := fun a y => by
    obtain ⟨y, rfl⟩ := hD.xe.surjective y
    refine Over.OverMorphism.ext ((cancel_epi (spMap i)).1 ?_)
    have e₁ := hD.c_pr (a • y)
    have e₂ := hD.c_pr y
    rw [oa'.c_lin, Over.comp_left, Category.assoc, hx] at e₁
    refine e₁.symm.trans ((congrArg (_ ≫ ·) (ho a)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans (Category.assoc _ _ _))
  refine ⟨⟨oB, cl, fun a u hu u₀ y y' => ?_⟩, rfl⟩
  obtain ⟨y, rfl⟩ := hD.xe.surjective y
  obtain ⟨y', rfl⟩ := hD.xe.surjective y'
  refine corr_of_val_field_extension _ _ (fracMap hφ) _ _ D.P.isLB _ _ _ _ _ _ _ _ fun z J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
  have := oa'.onB.hom a
  have := oa'.onB.hom (star a)
  have := oB.hom a
  have := oB.hom (star a)
  obtain ⟨u', hu', h₀⟩ := exists_ros hG D'.P.isAb D'.P.isLB _ _ (oa'.onB.rosati a)
  have sq := fracMap_sq hφ
  have hh : (TK K).hom ≫ spMap i = genMap hφ ≫ (TK K₀).hom := (Category.id_comp _).symm.trans sq
  have e := val_corr hJ' (oa'.tau_bal a u' hu' h₀ y y') (𝟙 (TK K).left)
  have v := ros_val hG gp D'.P.isAb D.P.isLB D'.P.isLB hD.w_gen (ho a) (ho (star a)) ⟨hu, u₀⟩ ⟨hu', h₀⟩
    (cP D' (TK K) y) (cP D' (TK K) y') (genMap hφ ≫ D.pt2 (hD.xe y) (hD.xe y'))
    ((cPoint_proj hD _ hh y).trans (by
      rw [Category.assoc, DegPre.pt2, ← Over.comp_left, lift_fst]; rfl))
    ((cPoint_proj hD _ hh y').trans (by
      rw [Category.assoc, DegPre.pt2, ← Over.comp_left, lift_snd]; rfl)) hJ hJ'
  have cs : ∀ (a : O) y, cP D' (TK K) y ≫ oa'.onB.act a = cP D' (TK K) (a • y) := fun a y => by
    rw [cP, cP, oa'.c_lin, Category.assoc]
  rw [cs, cs, ← cPoint_add, ← cPoint_add] at v
  rw [val_mul hJ', val_pull hJ'] at e
  erw [Category.id_comp] at e
  beta_reduce at e
  show val _ (genMap hφ) z J = val _ (genMap hφ) z J
  rw [val_mul hJ, val_pull hJ, v]
  beta_reduce
  rw [← hx, ← hx, tau_val hD _ _ sq hJ hJ', tau_val hD _ _ sq hJ hJ']
  simp only [Category.id_comp]
  have e' := congrArg Additive.ofMul e
  apply Additive.ofMul.injective
  have c₀ : ∀ x, (cP D' (TK K) x).left = D'.xK x := fun _ => rfl
  have c₁ : val₂ u' z J' (cP D' (TK K) y) (cP D' (TK K) y') = val u' (D'.pt2 y y') z J' := rfl
  simp only [ofMul_mul, ofMul_inv, c₀, c₁] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory
