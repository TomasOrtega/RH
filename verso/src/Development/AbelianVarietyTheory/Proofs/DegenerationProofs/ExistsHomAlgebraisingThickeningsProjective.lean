import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MorAlgIdeal

open GlobalTheory.MorAlg

/- English proof (translation)
Take `⟨H, hH, n, s, hs⟩` from `hP`. Establish `hL : ∀ e, (H.pull (j e)).IsLB` using `fun e => LB.isLB_pull hH _`. Use `choose t ht using fun e => exists_isPull (j e) hH s`. Establish `hv : ∀ e, IsPull (thickMap R I e Y) (t (e + 1)) (t e)` using `fun e => IsPull.cancel hH (hL _) (hL _) (ht (e + 1)) (by rw [hj]; exact ht e)`. Use `choose v hv cv using hv`.

Establish `hjR : ∀ e, j e ≫ P.hom = (thickObj R I e Y).hom ≫ thick R I e` using `fun e => by`. Rewrite using `[← Over.w q, ← Category.assoc, hq]`. Conclude with `pullback.condition`. Establish `hci : ∀ e, IsClosedImmersion (thick R I e)` using `fun e => IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `hva : VeryAmpleBy (thickObj R I 0 Y).hom (H.pull (j 0)) (t 0)`.

Take `⟨w, hw, c⟩` from `ht 0`. Use `GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R P.left P.hom H n s hH hs _ (Ideal.Quotient.mk (I ^ (0 + 1))) _ _ (j 0) (hjR 0) ?_ _ w _ (hL 0) hw c` and prove the remaining obligations. Establish `h₁ : IsClosedImmersion (j 0 ≫ q.left)`. Rewrite using `[hq]`. Use `hci 0` as an intermediate fact.

Use `infer_instance`. Establish `h₂ : IsClosedImmersion (j 0)` using `IsClosedImmersion.of_comp _ q.left`. Establish `h₃ : IsClosedImmersion (pullback.lift (j 0) (thickObj R I 0 Y).hom (hjR 0) ≫ pullback.fst P.hom (thick R I 0))`. Rewrite using `[pullback.lift_fst]`. Conclude with `h₂`.

Conclude with `IsClosedImmersion.of_comp _ (pullback.fst P.hom (thick R I 0))`. Establish `hpb : ∀ e, IsPullback (thickMap R I e Y) (thickObj R I e Y).hom (thickObj R I (e + 1) Y).hom (thickTrans R I e)` using `fun e => by`. Use `IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick R I (e + 1))) (h₂₂ := thick R I (e + 1)) (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)` and prove the remaining obligations. Rewrite using `[thickTrans_comp, pullback.lift_fst, Category.comp_id]`. Conclude with `IsPullback.of_hasPullback _ _`.

Take `⟨B, H', s', b, w, hH', hs', hb, -, hw, heq⟩` from `GlobalTheory.Degen.exists_projective_of_formal_embedding_local R I hI hc (fun e => thickObj R I e Y) (fun e => thickMap R I e Y) hpb (fun e => inferInstanceAs (Flat (pullback.snd Y.hom (thick R I e)))) (fun e => H.pull (j e)) v (fun e => ⟨hL e, hv e⟩) n t cv hva`. Take `⟨φ, u, hφ, hu, cu⟩` from `GlobalTheory.exists_hom_of_veryAmpleBy R P.left P.hom H n s hH hs B.left B.hom H' s' hH' hs'.1 fun d F hF h0 => heq d F hF fun e k => by`. Rewrite using `[← hjR]`. Conclude with `(ht e).eqn P.hom hH hF h0 k`. Establish `hbφ : ∀ e, b e ≫ φ = j e` using `fun e => by`.

Take `⟨w₁, hw₁, c₁⟩` from `IsPull.comp hH hH' (hL e) ⟨u, hu, cu⟩ ⟨w e, (hw e).1, (hw e).2⟩`. Take `⟨w₂, hw₂, c₂⟩` from `ht e`. Use `GlobalTheory.MapUniq.hom_eq_of_pull_sections R P.left P.hom H n s hH hs _ _ (t e) _ _ w₁ w₂ (hL e) ?_ hw₁ hw₂ c₁ c₂` and prove the remaining obligations. Rewrite using `[Category.assoc, hφ, hjR]`. Conclude with `(hb e).w`.

Set `φ' : B ⟶ P` to `Over.homMk φ hφ`. Establish `hbp : ∀ e, b e ≫ (φ' ≫ q).left = pullback.fst Y.hom (thick R I e)` using `fun e => by`. Rewrite using `[← hq, ← hbφ]`. Conclude with `(Category.assoc _ _ _).symm`. Establish `hB : IsProper ((φ' ≫ q).left ≫ Y.hom)`.

Rewrite using `[Over.w]`. Conclude with `GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ ⟨H', hH', n, s', hs'⟩`. Establish `hp : IsProper (φ' ≫ q).left` using `IsProper.of_comp _ Y.hom`. Establish `hiso : IsIso (φ' ≫ q)` using `GlobalTheory.IsoLimitIdeal.main R I hI B Y (φ' ≫ q) fun e => by`. Establish `h₁ : (hb e).isoPullback.hom ≫ ((Over.pullback (thick R I e)).map (φ' ≫ q)).left = 𝟙 _`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Over.pullback_map_left, Category.assoc, pullback.lift_fst, Category.id_comp]`. Rewrite using `[← hbp e, IsPullback.isoPullback_hom_fst_assoc]`. Simplify using `only [Over.pullback_map_left, Category.assoc, pullback.lift_snd, Category.id_comp]`. Conclude with `(hb e).isoPullback_hom_snd`.

Establish `h₂ : IsIso ((Over.forget _).map ((Over.pullback (thick R I e)).map (φ' ≫ q)))` using `@IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ (Iso.isIso_hom _) (IsIso.id _) h₁`. Conclude with `isIso_of_reflects_iso _ (Over.forget _)`. Use `⟨inv (φ' ≫ q) ≫ φ', fun e => ?_⟩` and prove the remaining obligations. Rewrite using `[← hbp, Category.assoc, ← Over.comp_left, IsIso.hom_inv_id_assoc]`. Conclude with `hbφ e`.
-/
theorem exists_section (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    (hI : I ≠ ⊤) (hc : IsAdicComplete I R) (Y P : Over (Spec (CommRingCat.of R))) (q : P ⟶ Y)
    [IsSeparated q.left] [IsProper Y.hom] [Flat Y.hom] (hP : IsProjBy P.hom)
    (j : ∀ e, (thickObj R I e Y).left ⟶ P.left)
    (hq : ∀ e, j e ≫ q.left = pullback.fst Y.hom (thick R I e))
    (hj : ∀ e, thickMap R I e Y ≫ j (e + 1) = j e) :
    ∃ g : Y ⟶ P, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = j e := by
  obtain ⟨H, hH, n, s, hs⟩ := hP
  have hL : ∀ e, (H.pull (j e)).IsLB := fun e => LB.isLB_pull hH _
  choose t ht using fun e => exists_isPull (j e) hH s
  have hv : ∀ e, IsPull (thickMap R I e Y) (t (e + 1)) (t e) := fun e =>
    IsPull.cancel hH (hL _) (hL _) (ht (e + 1)) (by rw [hj]; exact ht e)
  choose v hv cv using hv
  have hjR : ∀ e, j e ≫ P.hom = (thickObj R I e Y).hom ≫ thick R I e := fun e => by
    rw [← Over.w q, ← Category.assoc, hq]
    exact pullback.condition
  have hci : ∀ e, IsClosedImmersion (thick R I e) := fun e =>
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hva : VeryAmpleBy (thickObj R I 0 Y).hom (H.pull (j 0)) (t 0) := by
    obtain ⟨w, hw, c⟩ := ht 0
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R P.left P.hom H n s hH hs _ (Ideal.Quotient.mk (I ^ (0 + 1))) _ _ (j 0) (hjR 0) ?_ _ w _
      (hL 0) hw c
    have h₁ : IsClosedImmersion (j 0 ≫ q.left) := by
      rw [hq]
      have := hci 0
      infer_instance
    have h₂ : IsClosedImmersion (j 0) := IsClosedImmersion.of_comp _ q.left
    have h₃ : IsClosedImmersion (pullback.lift (j 0) (thickObj R I 0 Y).hom (hjR 0) ≫
        pullback.fst P.hom (thick R I 0)) := by
      rw [pullback.lift_fst]
      exact h₂
    exact IsClosedImmersion.of_comp _ (pullback.fst P.hom (thick R I 0))
  have hpb : ∀ e, IsPullback (thickMap R I e Y) (thickObj R I e Y).hom (thickObj R I (e + 1) Y).hom
      (thickTrans R I e) := fun e => by
    refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick R I (e + 1))) (h₂₂ := thick R I (e + 1))
      (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [thickTrans_comp, pullback.lift_fst, Category.comp_id]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨B, H', s', b, w, hH', hs', hb, -, hw, heq⟩ := GlobalTheory.Degen.exists_projective_of_formal_embedding_local R I hI hc (fun e => thickObj R I e Y)
    (fun e => thickMap R I e Y) hpb (fun e => inferInstanceAs (Flat (pullback.snd Y.hom (thick R I e))))
    (fun e => H.pull (j e)) v (fun e => ⟨hL e, hv e⟩) n t cv hva
  obtain ⟨φ, u, hφ, hu, cu⟩ := GlobalTheory.exists_hom_of_veryAmpleBy R P.left P.hom H n s hH hs B.left B.hom H' s' hH' hs'.1
    fun d F hF h0 => heq d F hF fun e k => by
      rw [← hjR]
      exact (ht e).eqn P.hom hH hF h0 k
  have hbφ : ∀ e, b e ≫ φ = j e := fun e => by
    obtain ⟨w₁, hw₁, c₁⟩ := IsPull.comp hH hH' (hL e) ⟨u, hu, cu⟩ ⟨w e, (hw e).1, (hw e).2⟩
    obtain ⟨w₂, hw₂, c₂⟩ := ht e
    refine GlobalTheory.MapUniq.hom_eq_of_pull_sections R P.left P.hom H n s hH hs _ _ (t e) _ _ w₁ w₂ (hL e) ?_ hw₁ hw₂ c₁ c₂
    rw [Category.assoc, hφ, hjR]
    exact (hb e).w
  let φ' : B ⟶ P := Over.homMk φ hφ
  have hbp : ∀ e, b e ≫ (φ' ≫ q).left = pullback.fst Y.hom (thick R I e) := fun e => by
    rw [← hq, ← hbφ]
    exact (Category.assoc _ _ _).symm
  have hB : IsProper ((φ' ≫ q).left ≫ Y.hom) := by
    rw [Over.w]
    exact GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ ⟨H', hH', n, s', hs'⟩
  have hp : IsProper (φ' ≫ q).left := IsProper.of_comp _ Y.hom
  have hiso : IsIso (φ' ≫ q) := GlobalTheory.IsoLimitIdeal.main R I hI B Y (φ' ≫ q) fun e => by
    have h₁ : (hb e).isoPullback.hom ≫ ((Over.pullback (thick R I e)).map (φ' ≫ q)).left = 𝟙 _ := by
      apply pullback.hom_ext
      · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst, Category.id_comp]
        rw [← hbp e, IsPullback.isoPullback_hom_fst_assoc]
      · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_snd, Category.id_comp]
        exact (hb e).isoPullback_hom_snd
    have h₂ : IsIso ((Over.forget _).map ((Over.pullback (thick R I e)).map (φ' ≫ q))) :=
      @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ (Iso.isIso_hom _) (IsIso.id _) h₁
    exact isIso_of_reflects_iso _ (Over.forget _)
  refine ⟨inv (φ' ≫ q) ≫ φ', fun e => ?_⟩
  rw [← hbp, Category.assoc, ← Over.comp_left, IsIso.hom_inv_id_assoc]
  exact hbφ e

/- English proof (translation)
Introduce `R _ _ _ I hI hcI Y Z hY hZ hfl f hf hc`. Establish `pY` using `GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hY`. Establish `pZ` using `GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hZ`. Establish `hsep : IsSeparated (fst Y Z).left` using `inferInstanceAs (IsSeparated (pullback.fst Y.hom Z.hom))`. Take `⟨g, hg⟩` from `exists_section R I hI hcI Y (Y ⊗ Z) (fst Y Z) (GlobalTheory.AbLaw.isProjBy_tensor R Y Z hY hZ) (fun e => pullback.lift (pullback.fst Y.hom (thick R I e)) (f e) (hf e).symm) (fun e => pullback.lift_fst _ _ _) (fun e => by`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Use `erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst, Category.comp_id]`. Use `erw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hc])`. Use `⟨g ≫ snd Y Z, fun e => ?_⟩` and prove the remaining obligations. Use `congrArg (· ≫ pullback.snd Y.hom Z.hom) (hg e)` as an intermediate fact.

Conclude with `((Category.assoc _ _ _).symm.trans this).trans (pullback.lift_snd _ _ _)`.
-/
theorem exists_hom_of_thickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y Z : Over (Spec (CommRingCat.of R))), IsProjBy Y.hom → IsProjBy Z.hom → Flat Y.hom → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Z.left, (∀ e, f e ≫ Z.hom = pullback.fst Y.hom (thick R I e) ≫ Y.hom) → (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃ g : Y ⟶ Z, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = f e := by
  intro R _ _ _ I hI hcI Y Z hY hZ hfl f hf hc
  have pY := GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hY
  have pZ := GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hZ
  have hsep : IsSeparated (fst Y Z).left := inferInstanceAs (IsSeparated (pullback.fst Y.hom Z.hom))
  obtain ⟨g, hg⟩ := exists_section R I hI hcI Y (Y ⊗ Z) (fst Y Z) (GlobalTheory.AbLaw.isProjBy_tensor R Y Z hY hZ)
    (fun e => pullback.lift (pullback.fst Y.hom (thick R I e)) (f e) (hf e).symm)
    (fun e => pullback.lift_fst _ _ _) (fun e => by
      apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst, Category.comp_id]
      · erw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hc])
  refine ⟨g ≫ snd Y Z, fun e => ?_⟩
  have := congrArg (· ≫ pullback.snd Y.hom Z.hom) (hg e)
  exact ((Category.assoc _ _ _).symm.trans this).trans (pullback.lift_snd _ _ _)

end GlobalTheory.MorAlgIdeal
