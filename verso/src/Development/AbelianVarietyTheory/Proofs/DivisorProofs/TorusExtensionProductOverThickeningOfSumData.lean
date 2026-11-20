import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianTensorOverScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfTorusHomOfZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

noncomputable section

namespace GlobalTheory.ProdTorusExt

section Torus

variable {S : Scheme.{0}} {X X' X'' : Type} [AddCommGroup X] [AddCommGroup X'] [AddCommGroup X'']

/- English proof (translation)
Apply `(GlobalTheory.splitTorusPointsEquiv S X'' _).injective` to reduce the goal to its premises. Use `conv_rhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S (a.comp b))]`. Use `conv_lhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S a)]`. Rewrite using `[Category.assoc, ← Category.assoc (𝟙 _), GlobalTheory.SplitTorusPow.points_comp_torusMap, GlobalTheory.SplitTorusPow.points_comp_torusMap, GlobalTheory.SplitTorusPow.points_comp_torusMap]`. Both sides reduce to the same expression.
-/
theorem torusMap_comp' (a : X →+ X') (b : X'' →+ X) :
    GlobalTheory.SplitTorusPow.torusMap S a ≫ GlobalTheory.SplitTorusPow.torusMap S b = GlobalTheory.SplitTorusPow.torusMap S (a.comp b) := by
  apply (GlobalTheory.splitTorusPointsEquiv S X'' _).injective
  conv_rhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S (a.comp b))]
  conv_lhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S a)]
  rw [Category.assoc, ← Category.assoc (𝟙 _), GlobalTheory.SplitTorusPow.points_comp_torusMap,
    GlobalTheory.SplitTorusPow.points_comp_torusMap, GlobalTheory.SplitTorusPow.points_comp_torusMap]
  rfl

/- English proof (translation)
Apply `(GlobalTheory.splitTorusPointsEquiv S X _).injective` to reduce the goal to its premises. Use `conv_lhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.id X))]`. Rewrite using `[GlobalTheory.SplitTorusPow.points_comp_torusMap]`. Both sides reduce to the same expression.
-/
theorem torusMap_id' : GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.id X) = 𝟙 _ := by
  apply (GlobalTheory.splitTorusPointsEquiv S X _).injective
  conv_lhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.id X))]
  rw [GlobalTheory.SplitTorusPow.points_comp_torusMap]
  rfl

/- English proof (translation)
Use `haveI := GlobalTheory.SemiProd.torus_prod_iso S X₁ X₂`. Establish `e : lift (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inl X₁ X₂))) (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inr X₁ X₂))) = GlobalTheory.SplitTorusPow.torusMap S E.symm.toAddMonoidHom ≫ lift (GlobalTheory. …`. Rewrite using `[comp_lift, torusMap_comp', torusMap_comp']`. Use `haveI : IsIso (GlobalTheory.SplitTorusPow.torusMap S E.symm.toAddMonoidHom) := ⟨GlobalTheory.SplitTorusPow.torusMap S E.toAddMonoidHom, by`. Rewrite using `[torusMap_comp', show E.symm.toAddMonoidHom.comp E.toAddMonoidHom = AddMonoidHom.id X from by ext; simp, torusMap_id'], by`.

Rewrite using `[torusMap_comp', show E.toAddMonoidHom.comp E.symm.toAddMonoidHom = AddMonoidHom.id (X₁ × X₂) from by`. Apply the tactic sequence `ext <;> simp, torusMap_id']⟩`. Rewrite using `[e]`. Use `infer_instance`.
-/
theorem isIso_lift_torusMap {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂] (E : X ≃+ X₁ × X₂) :
    IsIso (lift (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inl X₁ X₂)))
      (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inr X₁ X₂)))) := by
  haveI := GlobalTheory.SemiProd.torus_prod_iso S X₁ X₂
  have e : lift (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inl X₁ X₂)))
      (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inr X₁ X₂))) =
      GlobalTheory.SplitTorusPow.torusMap S E.symm.toAddMonoidHom ≫
        lift (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
          (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) := by
    rw [comp_lift, torusMap_comp', torusMap_comp']
  haveI : IsIso (GlobalTheory.SplitTorusPow.torusMap S E.symm.toAddMonoidHom) :=
    ⟨GlobalTheory.SplitTorusPow.torusMap S E.toAddMonoidHom, by
      rw [torusMap_comp', show E.symm.toAddMonoidHom.comp E.toAddMonoidHom = AddMonoidHom.id X from by ext; simp,
        torusMap_id'], by
      rw [torusMap_comp', show E.toAddMonoidHom.comp E.symm.toAddMonoidHom = AddMonoidHom.id (X₁ × X₂) from by
        ext <;> simp, torusMap_id']⟩
  rw [e]
  infer_instance

end Torus

end GlobalTheory.ProdTorusExt

namespace GlobalTheory.ProdTorusExt

/- English proof (translation)
Introduce `R _ _ I e D D₁ D₂ p₁ p₂ q₁ q₂ G₁ G₂ _ _ _ _ g₁ g₂ hD`. Set `F` to `Over.pullback (thick R I e)`. Set `S₀` to `Sp (R ⧸ I ^ (e + 1))`. Use `haveI := hD.hom₁`. Use `haveI := hD.hom₂`.

Use `haveI := g₁.q_hom`. Use `haveI := g₂.q_hom`. Use `haveI := g₁.i_hom`. Use `haveI := g₂.i_hom`. Set `E : D.X ≃+ D₁.X × D₂.X` to `AddEquiv.ofBijective (q₁.prod q₂) hD.xsum`.

Set `j₁ : D₁.X →+ D.X` to `E.symm.toAddMonoidHom.comp (AddMonoidHom.inl D₁.X D₂.X)`. Set `j₂ : D₂.X →+ D.X` to `E.symm.toAddMonoidHom.comp (AddMonoidHom.inr D₁.X D₂.X)`. Set `τ₁` to `GlobalTheory.SplitTorusPow.torusMap S₀ j₁`. Set `τ₂` to `GlobalTheory.SplitTorusPow.torusMap S₀ j₂`. Use `haveI : IsMonHom τ₁ := GlobalTheory.SplitTorusPow.isMonHom_torusMap _`.

Use `haveI : IsMonHom τ₂ := GlobalTheory.SplitTorusPow.isMonHom_torusMap _`. Use `haveI hτ : IsIso (lift τ₁ τ₂) := isIso_lift_torusMap E`. Use `haveI hG : IsIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) := isIso_prodComparison_of_preservesLimit_pair F G₁ G₂`. Use `haveI := hD.lim`. Establish `eB : lift (F.map p₁) (F.map p₂) = F.map (lift p₁ p₂) ≫ Functor.OplaxMonoidal.δ F D₁.P.A D₂.P.A` using `(Functor.OplaxMonoidal.lift_δ F p₁ p₂).symm`.

Use `haveI hB : IsIso (lift (F.map p₁) (F.map p₂)) := by rw [eB]; infer_instance`. Use `haveI : IsMonHom (inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))) := inferInstanceAs (IsMonHom (asIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))).inv)`. Use `haveI : IsMonHom (inv (lift (F.map p₁) (F.map p₂))) := inferInstanceAs (IsMonHom (asIso (lift (F.map p₁) (F.map p₂))).inv)`. Set `q` to `lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)) ≫ (g₁.q ⊗ₘ g₂.q) ≫ inv (lift (F.map p₁) (F.map p₂))`. Set `i` to `lift τ₁ τ₂ ≫ (g₁.i ⊗ₘ g₂.i) ≫ inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))`.

Establish `hP : ∀ (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange], P g₁.q.left → P g₂.q.left → P q.left`. Introduce `P _ _ h₁ h₂`. Use `haveI : IsIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))).left := inferInstanceAs (IsIso ((Over.forget _).map (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))))`. Use `haveI : IsIso (inv (lift (F.map p₁) (F.map p₂))).left := inferInstanceAs (IsIso ((Over.forget _).map (inv (lift (F.map p₁) (F.map p₂)))))`. Rewrite using `[Over.comp_left, Over.comp_left]`.

Conclude with `P.comp_mem _ _ (P.of_isIso _) (P.comp_mem _ _ (GlobalTheory.SemiProd.tensorHom_prop _ P _ _ _ _ _ _ h₁ h₂) (P.of_isIso _))`. Establish `hq₁ : q ≫ F.map p₁ = F.map (fst G₁ G₂) ≫ g₁.q`. Establish `: inv (lift (F.map p₁) (F.map p₂)) ≫ F.map p₁ = fst _ _`. Rewrite using `[IsIso.inv_comp_eq, lift_fst]`. Rewrite using `[Category.assoc, Category.assoc, this, tensorHom_fst, lift_fst_assoc]`.

Establish `hq₂ : q ≫ F.map p₂ = F.map (snd G₁ G₂) ≫ g₂.q`. Establish `: inv (lift (F.map p₁) (F.map p₂)) ≫ F.map p₂ = snd _ _`. Rewrite using `[IsIso.inv_comp_eq, lift_snd]`. Rewrite using `[Category.assoc, Category.assoc, this, tensorHom_snd, lift_snd_assoc]`. Establish `hi₁ : i ≫ F.map (fst G₁ G₂) = τ₁ ≫ g₁.i`.

Establish `: inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) ≫ F.map (fst G₁ G₂) = fst _ _`. Rewrite using `[IsIso.inv_comp_eq, lift_fst]`. Rewrite using `[Category.assoc, Category.assoc, this, tensorHom_fst, lift_fst_assoc]`. Establish `hi₂ : i ≫ F.map (snd G₁ G₂) = τ₂ ≫ g₂.i`. Establish `: inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) ≫ F.map (snd G₁ G₂) = snd _ _`.

Rewrite using `[IsIso.inv_comp_eq, lift_snd]`. Rewrite using `[Category.assoc, Category.assoc, this, tensorHom_snd, lift_snd_assoc]`. Establish `key` using `GlobalTheory.SemiProd.kernel_tensor _ _ _ _ _ _ _ g₁.i g₂.i g₁.q g₂.q g₁.isKernel g₂.isKernel`. Establish `hK : IsPullback i (toUnit _) q (η[thickObj R I e D.P.A])`. Use `IsPullback.of_iso key (asIso (lift τ₁ τ₂)).symm (asIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))).symm (Iso.refl _) (asIso (lift (F.map p₁) (F.map p₂))).symm ?_ ?_ ?_ ?_` and prove the remaining obligations.

Simplify using `only [i, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]`. Conclude with `toUnit_unique _ _`. Simplify using `only [q, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]`. Simplify using `only [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv]`. Rewrite using `[IsIso.comp_inv_eq, IsMonHom.one_hom]`.

Establish `hE₁ : ∀ h : D₁.X → D.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) → h = j₁`. Introduce `h h₁ h₂`. Use function extensionality and compare the values at `y`. Apply `E.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(q₁.prod q₂) (h y) = E (E.symm (y, 0))`.

Rewrite using `[AddEquiv.apply_symm_apply]`. Conclude with `Prod.ext (h₁ y) (h₂ y)`. Establish `hE₂ : ∀ h : D₂.X → D.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) → h = j₂`. Introduce `h h₁ h₂`. Use function extensionality and compare the values at `y`.

Apply `E.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(q₁.prod q₂) (h y) = E (E.symm (0, y))`. Rewrite using `[AddEquiv.apply_symm_apply]`. Conclude with `Prod.ext (h₁ y) (h₂ y)`. Use `⟨q, i, inferInstance, hP @Flat g₁.q_flat g₂.q_flat, hP @Surjective g₁.q_surj g₂.q_surj, hP @IsAffineHom g₁.q_affine g₂.q_affine, inferInstance, hK, hq₁, hq₂, fun h h₁ h₂ => ?_, fun h h₁ h₂ => ?_⟩` and prove the remaining obligations.

Use `⟨τ₁, ?_, hi₁⟩` and prove the remaining obligations. Rewrite using `[hE₁ h h₁ h₂]`. Conclude with `GlobalTheory.MumProd.torusHomOf_torusMap j₁`. Use `⟨τ₂, ?_, hi₂⟩` and prove the remaining obligations. Rewrite using `[hE₂ h h₁ h₂]`.

Conclude with `GlobalTheory.MumProd.torusHomOf_torusMap j₂`.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∃ (q : thickObj R I e (G₁ ⊗ G₂) ⟶ thickObj R I e D.P.A) (i : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ thickObj R I e (G₁ ⊗ G₂)), IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsMonHom i ∧ IsPullback i (toUnit _) q (η[thickObj R I e D.P.A]) ∧ q ≫ (Over.pullback (thick R I e)).map p₁ = ((Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ g₁.q ∧ q ≫ (Over.pullback (thick R I e)).map p₂ = ((Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ g₂.q ∧ (∀ h : D₁.X → D.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (fst G₁ G₂)) = τ ≫ g₁.i) ∧ (∀ h : D₂.X → D.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (snd G₁ G₂)) = τ ≫ g₂.i) := by
  intro R _ _ I e D D₁ D₂ p₁ p₂ q₁ q₂ G₁ G₂ _ _ _ _ g₁ g₂ hD
  let F := Over.pullback (thick R I e)
  let S₀ := Sp (R ⧸ I ^ (e + 1))
  haveI := hD.hom₁
  haveI := hD.hom₂
  haveI := g₁.q_hom
  haveI := g₂.q_hom
  haveI := g₁.i_hom
  haveI := g₂.i_hom
  let E : D.X ≃+ D₁.X × D₂.X := AddEquiv.ofBijective (q₁.prod q₂) hD.xsum
  let j₁ : D₁.X →+ D.X := E.symm.toAddMonoidHom.comp (AddMonoidHom.inl D₁.X D₂.X)
  let j₂ : D₂.X →+ D.X := E.symm.toAddMonoidHom.comp (AddMonoidHom.inr D₁.X D₂.X)
  let τ₁ := GlobalTheory.SplitTorusPow.torusMap S₀ j₁
  let τ₂ := GlobalTheory.SplitTorusPow.torusMap S₀ j₂
  haveI : IsMonHom τ₁ := GlobalTheory.SplitTorusPow.isMonHom_torusMap _
  haveI : IsMonHom τ₂ := GlobalTheory.SplitTorusPow.isMonHom_torusMap _
  haveI hτ : IsIso (lift τ₁ τ₂) := isIso_lift_torusMap E

  haveI hG : IsIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) :=
    isIso_prodComparison_of_preservesLimit_pair F G₁ G₂
  haveI := hD.lim
  have eB : lift (F.map p₁) (F.map p₂) = F.map (lift p₁ p₂) ≫ Functor.OplaxMonoidal.δ F D₁.P.A D₂.P.A :=
    (Functor.OplaxMonoidal.lift_δ F p₁ p₂).symm
  haveI hB : IsIso (lift (F.map p₁) (F.map p₂)) := by rw [eB]; infer_instance
  haveI : IsMonHom (inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))) :=
    inferInstanceAs (IsMonHom (asIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))).inv)
  haveI : IsMonHom (inv (lift (F.map p₁) (F.map p₂))) :=
    inferInstanceAs (IsMonHom (asIso (lift (F.map p₁) (F.map p₂))).inv)
  let q := lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)) ≫ (g₁.q ⊗ₘ g₂.q) ≫ inv (lift (F.map p₁) (F.map p₂))
  let i := lift τ₁ τ₂ ≫ (g₁.i ⊗ₘ g₂.i) ≫ inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))
  have hP : ∀ (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange],
      P g₁.q.left → P g₂.q.left → P q.left := by
    intro P _ _ h₁ h₂
    haveI : IsIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))))
    haveI : IsIso (inv (lift (F.map p₁) (F.map p₂))).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (inv (lift (F.map p₁) (F.map p₂)))))
    rw [Over.comp_left, Over.comp_left]
    exact P.comp_mem _ _ (P.of_isIso _)
      (P.comp_mem _ _ (GlobalTheory.SemiProd.tensorHom_prop _ P _ _ _ _ _ _ h₁ h₂) (P.of_isIso _))
  have hq₁ : q ≫ F.map p₁ = F.map (fst G₁ G₂) ≫ g₁.q := by
    have : inv (lift (F.map p₁) (F.map p₂)) ≫ F.map p₁ = fst _ _ := by
      rw [IsIso.inv_comp_eq, lift_fst]
    rw [Category.assoc, Category.assoc, this, tensorHom_fst, lift_fst_assoc]
  have hq₂ : q ≫ F.map p₂ = F.map (snd G₁ G₂) ≫ g₂.q := by
    have : inv (lift (F.map p₁) (F.map p₂)) ≫ F.map p₂ = snd _ _ := by
      rw [IsIso.inv_comp_eq, lift_snd]
    rw [Category.assoc, Category.assoc, this, tensorHom_snd, lift_snd_assoc]
  have hi₁ : i ≫ F.map (fst G₁ G₂) = τ₁ ≫ g₁.i := by
    have : inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) ≫ F.map (fst G₁ G₂) = fst _ _ := by
      rw [IsIso.inv_comp_eq, lift_fst]
    rw [Category.assoc, Category.assoc, this, tensorHom_fst, lift_fst_assoc]
  have hi₂ : i ≫ F.map (snd G₁ G₂) = τ₂ ≫ g₂.i := by
    have : inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) ≫ F.map (snd G₁ G₂) = snd _ _ := by
      rw [IsIso.inv_comp_eq, lift_snd]
    rw [Category.assoc, Category.assoc, this, tensorHom_snd, lift_snd_assoc]

  have key := GlobalTheory.SemiProd.kernel_tensor _ _ _ _ _ _ _ g₁.i g₂.i g₁.q g₂.q g₁.isKernel g₂.isKernel
  have hK : IsPullback i (toUnit _) q (η[thickObj R I e D.P.A]) := by
    refine IsPullback.of_iso key (asIso (lift τ₁ τ₂)).symm
      (asIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))).symm (Iso.refl _)
      (asIso (lift (F.map p₁) (F.map p₂))).symm ?_ ?_ ?_ ?_
    · simp only [i, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
    · exact toUnit_unique _ _
    · simp only [q, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
    · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv]
      rw [IsIso.comp_inv_eq, IsMonHom.one_hom]

  have hE₁ : ∀ h : D₁.X → D.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) → h = j₁ := by
    intro h h₁ h₂
    funext y
    apply E.injective
    change (q₁.prod q₂) (h y) = E (E.symm (y, 0))
    rw [AddEquiv.apply_symm_apply]
    exact Prod.ext (h₁ y) (h₂ y)
  have hE₂ : ∀ h : D₂.X → D.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) → h = j₂ := by
    intro h h₁ h₂
    funext y
    apply E.injective
    change (q₁.prod q₂) (h y) = E (E.symm (0, y))
    rw [AddEquiv.apply_symm_apply]
    exact Prod.ext (h₁ y) (h₂ y)
  refine ⟨q, i, inferInstance, hP @Flat g₁.q_flat g₂.q_flat, hP @Surjective g₁.q_surj g₂.q_surj,
    hP @IsAffineHom g₁.q_affine g₂.q_affine, inferInstance, hK, hq₁, hq₂, fun h h₁ h₂ => ?_, fun h h₁ h₂ => ?_⟩
  · refine ⟨τ₁, ?_, hi₁⟩
    rw [hE₁ h h₁ h₂]
    exact GlobalTheory.MumProd.torusHomOf_torusMap j₁
  · refine ⟨τ₂, ?_, hi₂⟩
    rw [hE₂ h h₁ h₂]
    exact GlobalTheory.MumProd.torusHomOf_torusMap j₂

end GlobalTheory.ProdTorusExt
