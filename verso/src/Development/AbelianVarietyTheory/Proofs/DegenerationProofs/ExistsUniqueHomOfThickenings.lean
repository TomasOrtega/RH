import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfIsClosedImmersionOfThickeningsOfIsProper
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveOfFormalEmbedding

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.LocalMorAlg

open GlobalTheory.MorAlg

/- English proof (translation)
Take `⟨H, hH, n, s, hs⟩` from `hP`. Establish `hL : ∀ e, (H.pull (j e)).IsLB` using `fun e => LB.isLB_pull hH _`. Use `choose t ht using fun e => exists_isPull (j e) hH s`. Establish `hv : ∀ e, IsPull (thickMap V (IsLocalRing.maximalIdeal V) e Y) (t (e + 1)) (t e)` using `fun e => IsPull.cancel hH (hL _) (hL _) (ht (e + 1)) (by rw [hj]; exact ht e)`. Use `choose v hv cv using hv`.

Establish `hjV : ∀ e, j e ≫ P.hom = (thickObj V (IsLocalRing.maximalIdeal V) e Y).hom ≫ thick V (IsLocalRing.maximalIdeal V) e` using `fun e => by`. Rewrite using `[← Over.w q, ← Category.assoc, hq]`. Conclude with `pullback.condition`. Establish `hci : ∀ e, IsClosedImmersion (thick V (IsLocalRing.maximalIdeal V) e)` using `fun e => IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `hva : VeryAmpleBy (thickObj V (IsLocalRing.maximalIdeal V) 0 Y).hom (H.pull (j 0)) (t 0)`.

Take `⟨w, hw, c⟩` from `ht 0`. Use `GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull V P.left P.hom H n s hH hs _ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1))) _ _ (j 0) (hjV 0) ?_ _ w _ (hL 0) hw c` and prove the remaining obligations. Establish `h₁ : IsClosedImmersion (j 0 ≫ q.left)`. Rewrite using `[hq]`. Use `hci 0` as an intermediate fact.

Use `infer_instance`. Establish `h₂ : IsClosedImmersion (j 0)` using `IsClosedImmersion.of_comp _ q.left`. Establish `h₃ : IsClosedImmersion (pullback.lift (j 0) (thickObj V (IsLocalRing.maximalIdeal V) 0 Y).hom (hjV 0) ≫ pullback.fst P.hom (thick V (IsLocalRing.maximalIdeal V) 0))`. Rewrite using `[pullback.lift_fst]`. Conclude with `h₂`.

Conclude with `IsClosedImmersion.of_comp _ (pullback.fst P.hom (thick V (IsLocalRing.maximalIdeal V) 0))`. Establish `hpb : ∀ e, IsPullback (thickMap V (IsLocalRing.maximalIdeal V) e Y) (thickObj V (IsLocalRing.maximalIdeal V) e Y).hom (thickObj V (IsLocalRing.maximalIdeal V) (e + 1) Y).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)` using `fun e => by`. Use `IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) (e + 1))) (h₂₂ := thick V (IsLocalRing.maximalIdeal V) (e + 1)) (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)` and prove the remaining obligations. Rewrite using `[thickTrans_comp, pullback.lift_fst, Category.comp_id]`. Conclude with `IsPullback.of_hasPullback _ _`.

Take `⟨B, H', s', b, w, hH', hs', hb, -, hw, heq⟩` from `GlobalTheory.LocalEmb.exists_projective_of_formal_embedding V (fun e => thickObj V (IsLocalRing.maximalIdeal V) e Y) (fun e => thickMap V (IsLocalRing.maximalIdeal V) e Y) hpb (fun e => inferInstanceAs (Flat (pullback.snd Y.hom (thick V (IsLocalRing.maximalIdeal V) e)))) (fun e = …`. Take `⟨φ, u, hφ, hu, cu⟩` from `GlobalTheory.exists_hom_of_veryAmpleBy V P.left P.hom H n s hH hs B.left B.hom H' s' hH' hs'.1 fun d F hF h0 => heq d F hF fun e k => by`. Rewrite using `[← hjV]`. Conclude with `(ht e).eqn P.hom hH hF h0 k`. Establish `hbφ : ∀ e, b e ≫ φ = j e` using `fun e => by`.

Take `⟨w₁, hw₁, c₁⟩` from `IsPull.comp hH hH' (hL e) ⟨u, hu, cu⟩ ⟨w e, (hw e).1, (hw e).2⟩`. Take `⟨w₂, hw₂, c₂⟩` from `ht e`. Use `GlobalTheory.MapUniq.hom_eq_of_pull_sections V P.left P.hom H n s hH hs _ _ (t e) _ _ w₁ w₂ (hL e) ?_ hw₁ hw₂ c₁ c₂` and prove the remaining obligations. Rewrite using `[Category.assoc, hφ, hjV]`. Conclude with `(hb e).w`.

Set `φ' : B ⟶ P` to `Over.homMk φ hφ`. Establish `hbp : ∀ e, b e ≫ (φ' ≫ q).left = pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) e)` using `fun e => by`. Rewrite using `[← hq, ← hbφ]`. Conclude with `(Category.assoc _ _ _).symm`. Establish `hB : IsProper ((φ' ≫ q).left ≫ Y.hom)`.

Rewrite using `[Over.w]`. Conclude with `GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ ⟨H', hH', n, s', hs'⟩`. Establish `hp : IsProper (φ' ≫ q).left` using `IsProper.of_comp _ Y.hom`. Establish `hiso : IsIso (φ' ≫ q)` using `GlobalTheory.IsoLimit.main V B Y (φ' ≫ q) fun e => by`. Establish `h₁ : (hb e).isoPullback.hom ≫ ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map (φ' ≫ q)).left = 𝟙 _`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Over.pullback_map_left, Category.assoc, pullback.lift_fst, Category.id_comp]`. Rewrite using `[← hbp e, IsPullback.isoPullback_hom_fst_assoc]`. Simplify using `only [Over.pullback_map_left, Category.assoc, pullback.lift_snd, Category.id_comp]`. Conclude with `(hb e).isoPullback_hom_snd`.

Establish `h₂ : IsIso ((Over.forget _).map ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map (φ' ≫ q)))` using `@IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ (Iso.isIso_hom _) (IsIso.id _) h₁`. Conclude with `isIso_of_reflects_iso _ (Over.forget _)`. Use `⟨inv (φ' ≫ q) ≫ φ', fun e => ?_⟩` and prove the remaining obligations. Rewrite using `[← hbp, Category.assoc, ← Over.comp_left, IsIso.hom_inv_id_assoc]`. Conclude with `hbφ e`.
-/
theorem exists_section_local (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y P : Over (Spec (CommRingCat.of V))) (q : P ⟶ Y)
    [IsSeparated q.left] [IsProper Y.hom] [Flat Y.hom] (hP : IsProjBy P.hom)
    (j : ∀ e, (thickObj V (IsLocalRing.maximalIdeal V) e Y).left ⟶ P.left)
    (hq : ∀ e, j e ≫ q.left = pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) e))
    (hj : ∀ e, thickMap V (IsLocalRing.maximalIdeal V) e Y ≫ j (e + 1) = j e) :
    ∃ g : Y ⟶ P, ∀ e, pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) e) ≫ g.left = j e := by
  obtain ⟨H, hH, n, s, hs⟩ := hP
  have hL : ∀ e, (H.pull (j e)).IsLB := fun e => LB.isLB_pull hH _
  choose t ht using fun e => exists_isPull (j e) hH s
  have hv : ∀ e, IsPull (thickMap V (IsLocalRing.maximalIdeal V) e Y) (t (e + 1)) (t e) := fun e =>
    IsPull.cancel hH (hL _) (hL _) (ht (e + 1)) (by rw [hj]; exact ht e)
  choose v hv cv using hv
  have hjV : ∀ e, j e ≫ P.hom = (thickObj V (IsLocalRing.maximalIdeal V) e Y).hom ≫ thick V (IsLocalRing.maximalIdeal V) e := fun e => by
    rw [← Over.w q, ← Category.assoc, hq]
    exact pullback.condition
  have hci : ∀ e, IsClosedImmersion (thick V (IsLocalRing.maximalIdeal V) e) := fun e =>
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hva : VeryAmpleBy (thickObj V (IsLocalRing.maximalIdeal V) 0 Y).hom (H.pull (j 0)) (t 0) := by
    obtain ⟨w, hw, c⟩ := ht 0
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull V P.left P.hom H n s hH hs _ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1))) _ _ (j 0) (hjV 0) ?_ _ w _
      (hL 0) hw c
    have h₁ : IsClosedImmersion (j 0 ≫ q.left) := by
      rw [hq]
      have := hci 0
      infer_instance
    have h₂ : IsClosedImmersion (j 0) := IsClosedImmersion.of_comp _ q.left
    have h₃ : IsClosedImmersion (pullback.lift (j 0) (thickObj V (IsLocalRing.maximalIdeal V) 0 Y).hom (hjV 0) ≫
        pullback.fst P.hom (thick V (IsLocalRing.maximalIdeal V) 0)) := by
      rw [pullback.lift_fst]
      exact h₂
    exact IsClosedImmersion.of_comp _ (pullback.fst P.hom (thick V (IsLocalRing.maximalIdeal V) 0))
  have hpb : ∀ e, IsPullback (thickMap V (IsLocalRing.maximalIdeal V) e Y) (thickObj V (IsLocalRing.maximalIdeal V) e Y).hom (thickObj V (IsLocalRing.maximalIdeal V) (e + 1) Y).hom
      (thickTrans V (IsLocalRing.maximalIdeal V) e) := fun e => by
    refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) (e + 1))) (h₂₂ := thick V (IsLocalRing.maximalIdeal V) (e + 1))
      (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [thickTrans_comp, pullback.lift_fst, Category.comp_id]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨B, H', s', b, w, hH', hs', hb, -, hw, heq⟩ := GlobalTheory.LocalEmb.exists_projective_of_formal_embedding V (fun e => thickObj V (IsLocalRing.maximalIdeal V) e Y)
    (fun e => thickMap V (IsLocalRing.maximalIdeal V) e Y) hpb (fun e => inferInstanceAs (Flat (pullback.snd Y.hom (thick V (IsLocalRing.maximalIdeal V) e))))
    (fun e => H.pull (j e)) v (fun e => ⟨hL e, hv e⟩) n t cv hva
  obtain ⟨φ, u, hφ, hu, cu⟩ := GlobalTheory.exists_hom_of_veryAmpleBy V P.left P.hom H n s hH hs B.left B.hom H' s' hH' hs'.1
    fun d F hF h0 => heq d F hF fun e k => by
      rw [← hjV]
      exact (ht e).eqn P.hom hH hF h0 k
  have hbφ : ∀ e, b e ≫ φ = j e := fun e => by
    obtain ⟨w₁, hw₁, c₁⟩ := IsPull.comp hH hH' (hL e) ⟨u, hu, cu⟩ ⟨w e, (hw e).1, (hw e).2⟩
    obtain ⟨w₂, hw₂, c₂⟩ := ht e
    refine GlobalTheory.MapUniq.hom_eq_of_pull_sections V P.left P.hom H n s hH hs _ _ (t e) _ _ w₁ w₂ (hL e) ?_ hw₁ hw₂ c₁ c₂
    rw [Category.assoc, hφ, hjV]
    exact (hb e).w
  let φ' : B ⟶ P := Over.homMk φ hφ
  have hbp : ∀ e, b e ≫ (φ' ≫ q).left = pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) e) := fun e => by
    rw [← hq, ← hbφ]
    exact (Category.assoc _ _ _).symm
  have hB : IsProper ((φ' ≫ q).left ≫ Y.hom) := by
    rw [Over.w]
    exact GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ ⟨H', hH', n, s', hs'⟩
  have hp : IsProper (φ' ≫ q).left := IsProper.of_comp _ Y.hom
  have hiso : IsIso (φ' ≫ q) := GlobalTheory.IsoLimit.main V B Y (φ' ≫ q) fun e => by
    have h₁ : (hb e).isoPullback.hom ≫ ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map (φ' ≫ q)).left = 𝟙 _ := by
      apply pullback.hom_ext
      · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst, Category.id_comp]
        rw [← hbp e, IsPullback.isoPullback_hom_fst_assoc]
      · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_snd, Category.id_comp]
        exact (hb e).isoPullback_hom_snd
    have h₂ : IsIso ((Over.forget _).map ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map (φ' ≫ q))) :=
      @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ (Iso.isIso_hom _) (IsIso.id _) h₁
    exact isIso_of_reflects_iso _ (Over.forget _)
  refine ⟨inv (φ' ≫ q) ≫ φ', fun e => ?_⟩
  rw [← hbp, Category.assoc, ← Over.comp_left, IsIso.hom_inv_id_assoc]
  exact hbφ e

/- English proof (translation)
Introduce `V _ _ _ _ _ Y Z hY hZ hfl f hf hc`. Establish `pY` using `GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ hY`. Establish `pZ` using `GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ hZ`. Establish `hsep : IsSeparated (fst Y Z).left` using `inferInstanceAs (IsSeparated (pullback.fst Y.hom Z.hom))`. Take `⟨g, hg⟩` from `exists_section_local V Y (Y ⊗ Z) (fst Y Z) (GlobalTheory.AbLaw.isProjBy_tensor V Y Z hY hZ) (fun e => pullback.lift (pullback.fst Y.hom (thick V _ e)) (f e) (hf e).symm) (fun e => pullback.lift_fst _ _ _) (fun e => by`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Use `erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst, Category.comp_id]`. Use `erw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hc])`. Use `⟨g ≫ snd Y Z, fun e => ?_⟩` and prove the remaining obligations. Use `congrArg (· ≫ pullback.snd Y.hom Z.hom) (hg e)` as an intermediate fact.

Conclude with `((Category.assoc _ _ _).symm.trans this).trans (pullback.lift_snd _ _ _)`.
-/
theorem exists_hom_local : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y Z : Over (Spec (CommRingCat.of V))), IsProjBy Y.hom → IsProjBy Z.hom → Flat Y.hom → ∀ f : ∀ e, (thickObj V (IsLocalRing.maximalIdeal V) e Y).left ⟶ Z.left, (∀ e, f e ≫ Z.hom = (fstG (IsLocalRing.maximalIdeal V) e Y).left ≫ Y.hom) → (∀ e, thickMap V (IsLocalRing.maximalIdeal V) e Y ≫ f (e + 1) = f e) → ∃ g : Y ⟶ Z, ∀ e, (fstG (IsLocalRing.maximalIdeal V) e Y).left ≫ g.left = f e := by
  intro V _ _ _ _ _ Y Z hY hZ hfl f hf hc
  have pY := GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ hY
  have pZ := GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ hZ
  have hsep : IsSeparated (fst Y Z).left := inferInstanceAs (IsSeparated (pullback.fst Y.hom Z.hom))
  obtain ⟨g, hg⟩ := exists_section_local V Y (Y ⊗ Z) (fst Y Z) (GlobalTheory.AbLaw.isProjBy_tensor V Y Z hY hZ)
    (fun e => pullback.lift (pullback.fst Y.hom (thick V _ e)) (f e) (hf e).symm)
    (fun e => pullback.lift_fst _ _ _) (fun e => by
      apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst, Category.comp_id]
      · erw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hc])
  refine ⟨g ≫ snd Y Z, fun e => ?_⟩
  have := congrArg (· ≫ pullback.snd Y.hom Z.hom) (hg e)
  exact ((Category.assoc _ _ _).symm.trans this).trans (pullback.lift_snd _ _ _)

/- English proof (translation)
Establish `up : ∀ (e : ℕ) (a : T ⟶ (thickObj R I e Y).left) (k : ℕ), e ≤ k → ∃ a' : T ⟶ (thickObj R I k Y).left, a' ≫ pullback.fst Y.hom (thick R I k) = a ≫ pullback.fst Y.hom (thick R I e) ∧ a' ≫ f k = a ≫ f e`. Introduce `e a k hk`. Proceed by induction on `k, hk using Nat.le_induction with`. Consider the case `base => exact ⟨a, rfl, rfl⟩`. Consider the case `succ k _ ih`.

Take `⟨a', h₁, h₂⟩` from `ih`. Establish `t : thickMap R I k Y ≫ pullback.fst Y.hom (thick R I (k + 1)) = pullback.fst Y.hom (thick R I k)` using `(pullback.lift_fst _ _ _).trans (Category.comp_id _)`. Conclude with `⟨a' ≫ thickMap R I k Y, (Category.assoc _ _ _).trans ((congrArg (a' ≫ ·) t).trans h₁), (Category.assoc _ _ _).trans ((congrArg (a' ≫ ·) (hc k)).trans h₂)⟩`. Take `⟨a', ha, ha'⟩` from `up e a (e + n) (by omega)`. Take `⟨b', hb, hb'⟩` from `up n b (e + n) (by omega)`.

Establish `: IsClosedImmersion (thick R I (e + n))` using `IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `hm : Mono (pullback.fst Y.hom (thick R I (e + n)))` using `inferInstance`. Establish `e' : a' = b'` using `hm.right_cancellation _ _ (ha.trans (h.trans hb.symm))`. Rewrite using `[← ha', ← hb', e']`.
-/
theorem comp_eq_of_compatible {R : Type} [CommRing R] (I : Ideal R) (Y : Over (Spec (CommRingCat.of R)))
    {Z T : Scheme.{0}} (f : ∀ e, (thickObj R I e Y).left ⟶ Z) (hc : ∀ e, thickMap R I e Y ≫ f (e + 1) = f e)
    {e n : ℕ} (a : T ⟶ (thickObj R I e Y).left) (b : T ⟶ (thickObj R I n Y).left)
    (h : a ≫ pullback.fst Y.hom (thick R I e) = b ≫ pullback.fst Y.hom (thick R I n)) : a ≫ f e = b ≫ f n := by
  have up : ∀ (e : ℕ) (a : T ⟶ (thickObj R I e Y).left) (k : ℕ), e ≤ k → ∃ a' : T ⟶ (thickObj R I k Y).left,
      a' ≫ pullback.fst Y.hom (thick R I k) = a ≫ pullback.fst Y.hom (thick R I e) ∧ a' ≫ f k = a ≫ f e := by
    intro e a k hk
    induction k, hk using Nat.le_induction with
    | base => exact ⟨a, rfl, rfl⟩
    | succ k _ ih =>
      obtain ⟨a', h₁, h₂⟩ := ih
      have t : thickMap R I k Y ≫ pullback.fst Y.hom (thick R I (k + 1)) = pullback.fst Y.hom (thick R I k) :=
        (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      exact ⟨a' ≫ thickMap R I k Y, (Category.assoc _ _ _).trans ((congrArg (a' ≫ ·) t).trans h₁),
        (Category.assoc _ _ _).trans ((congrArg (a' ≫ ·) (hc k)).trans h₂)⟩
  obtain ⟨a', ha, ha'⟩ := up e a (e + n) (by omega)
  obtain ⟨b', hb, hb'⟩ := up n b (e + n) (by omega)
  have : IsClosedImmersion (thick R I (e + n)) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hm : Mono (pullback.fst Y.hom (thick R I (e + n))) := inferInstance
  have e' : a' = b' := hm.right_cancellation _ _ (ha.trans (h.trans hb.symm))
  rw [← ha', ← hb', e']

/- English proof (translation)
Introduce `_ _ R _ _ _ _ I hI _ _ Y Z hY hZ hsm f hf hc`. Establish `pY` using `GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hY`. Establish `pZ` using `GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hZ`. Establish `hIm : I ≤ IsLocalRing.maximalIdeal R` using `IsLocalRing.le_maximalIdeal hI`. Establish `hJ : IsLocalRing.maximalIdeal R ≤ Ideal.jacobson ⊥` using `IsLocalRing.maximalIdeal_le_jacobson _`.

Establish `hρ : ∀ e, ∃ ρ : (thickObj R (IsLocalRing.maximalIdeal R) e Y).left ⟶ (thickObj R I e Y).left, ρ ≫ pullback.fst Y.hom (thick R I e) = pullback.fst Y.hom (thick R (IsLocalRing.maximalIdeal R) e)` using `fun e => ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ GlobalTheory.LocalEmb.fac (Ideal.pow_right_mono hIm (e + 1))) (by rw [Category.assoc, GlobalTheory.LocalEmb.fac_quo]; exact pullback.condition), pullback.lift_fst _ _ _⟩`. Use `choose ρ hρ using hρ`. Take `⟨g, hg⟩` from `exists_hom_local R Y Z hY hZ inferInstance (fun e => ρ e ≫ f e) (fun e => (Category.assoc _ _ _).trans ((congrArg (ρ e ≫ ·) (hf e)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Y.hom) (hρ e))))) (fun e => (Category.assoc _ _ _).symm.trans (comp_eq_of_compatible I Y f h …`. Establish `key : ∀ e, (fstG I e Y).left ≫ g.left = f e` using `fun e => by`. Establish `: IsClosedImmersion (thick R I e)` using `IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`.

Set `Y' : Over (Spec (CommRingCat.of R))` to `Over.mk (pullback.fst Y.hom (thick R I e) ≫ Y.hom)`. Establish `pY' : IsProper Y'.hom` using `inferInstanceAs (IsProper (pullback.fst Y.hom (thick R I e) ≫ Y.hom))`. Set `u : Y' ⟶ Z` to `Over.homMk (pullback.fst Y.hom (thick R I e) ≫ g.left) ((Category.assoc _ _ _).trans (congrArg (pullback.fst Y.hom (thick R I e) ≫ ·) (Over.w g)))`. Set `u' : Y' ⟶ Z` to `Over.homMk (f e) (hf e)`. Use `congrArg CommaMorphism.left (GlobalTheory.hom_eq_of_thickenings_of_isProper R _ hJ Y' Z u u' fun n => ?_)` and prove the remaining obligations.

Take `⟨l, hl⟩ : ∃ l : pullback Y'.hom (thick R (IsLocalRing.maximalIdeal R) n) ⟶ (thickObj R (IsLocalRing.maximalIdeal R) n Y).left, l ≫ pullback.fst Y.hom (thick R (IsLocalRing.maximalIdeal R) n) = pullback.fst Y'.hom (thick R (IsLocalRing.maximalIdeal R) n) ≫ pullback.fst Y.hom (thic …` from `⟨pullback.lift _ (pullback.snd _ _) ((Category.assoc _ _ _).trans pullback.condition), pullback.lift_fst _ _ _⟩`. Establish `h₁` using `comp_eq_of_compatible I Y f hc (l ≫ ρ n) (pullback.fst Y'.hom (thick R (IsLocalRing.maximalIdeal R) n)) ((Category.assoc _ _ _).trans ((congrArg (l ≫ ·) (hρ n)).trans hl))`. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g.left) hl.symm).trans ((Category.assoc _ _ _).trans ((congrArg (l ≫ ·) (hg n)).trans ((Category.assoc _ _ _).symm.trans h₁))))`. Conclude with `⟨g, key, fun g' hg' => GlobalTheory.hom_eq_of_thickenings_of_isProper R I (hIm.trans hJ) Y Z g' g fun e => (hg' e).trans (key e).symm⟩`.
-/
theorem existsUnique_hom_of_thickenings : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y Z : Over (Spec (CommRingCat.of R))), GlobalTheory.AbLaw.IsProjBy Y.hom → GlobalTheory.AbLaw.IsProjBy Z.hom → Smooth Y.hom → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Z.left, (∀ e, f e ≫ Z.hom = (fstG I e Y).left ≫ Y.hom) → (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃! g : Y ⟶ Z, ∀ e, (fstG I e Y).left ≫ g.left = f e := by
  intro _ _ R _ _ _ _ I hI _ _ Y Z hY hZ hsm f hf hc
  have pY := GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hY
  have pZ := GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hZ
  have hIm : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  have hJ : IsLocalRing.maximalIdeal R ≤ Ideal.jacobson ⊥ := IsLocalRing.maximalIdeal_le_jacobson _
  have hρ : ∀ e, ∃ ρ : (thickObj R (IsLocalRing.maximalIdeal R) e Y).left ⟶ (thickObj R I e Y).left,
      ρ ≫ pullback.fst Y.hom (thick R I e) = pullback.fst Y.hom (thick R (IsLocalRing.maximalIdeal R) e) := fun e =>
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ GlobalTheory.LocalEmb.fac (Ideal.pow_right_mono hIm (e + 1)))
      (by rw [Category.assoc, GlobalTheory.LocalEmb.fac_quo]; exact pullback.condition), pullback.lift_fst _ _ _⟩
  choose ρ hρ using hρ
  obtain ⟨g, hg⟩ := exists_hom_local R Y Z hY hZ inferInstance (fun e => ρ e ≫ f e)
    (fun e => (Category.assoc _ _ _).trans ((congrArg (ρ e ≫ ·) (hf e)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Y.hom) (hρ e)))))
    (fun e => (Category.assoc _ _ _).symm.trans (comp_eq_of_compatible I Y f hc _ _
      ((Category.assoc _ _ _).trans ((congrArg (thickMap R _ e Y ≫ ·) (hρ (e + 1))).trans
        (((pullback.lift_fst _ _ _).trans (Category.comp_id _)).trans (hρ e).symm)))))
  have key : ∀ e, (fstG I e Y).left ≫ g.left = f e := fun e => by
    have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (pullback.fst Y.hom (thick R I e) ≫ Y.hom)
    have pY' : IsProper Y'.hom := inferInstanceAs (IsProper (pullback.fst Y.hom (thick R I e) ≫ Y.hom))
    let u : Y' ⟶ Z := Over.homMk (pullback.fst Y.hom (thick R I e) ≫ g.left)
      ((Category.assoc _ _ _).trans (congrArg (pullback.fst Y.hom (thick R I e) ≫ ·) (Over.w g)))
    let u' : Y' ⟶ Z := Over.homMk (f e) (hf e)
    refine congrArg CommaMorphism.left (GlobalTheory.hom_eq_of_thickenings_of_isProper R _ hJ Y' Z u u' fun n => ?_)
    obtain ⟨l, hl⟩ : ∃ l : pullback Y'.hom (thick R (IsLocalRing.maximalIdeal R) n) ⟶
        (thickObj R (IsLocalRing.maximalIdeal R) n Y).left,
        l ≫ pullback.fst Y.hom (thick R (IsLocalRing.maximalIdeal R) n) =
          pullback.fst Y'.hom (thick R (IsLocalRing.maximalIdeal R) n) ≫ pullback.fst Y.hom (thick R I e) :=
      ⟨pullback.lift _ (pullback.snd _ _) ((Category.assoc _ _ _).trans pullback.condition), pullback.lift_fst _ _ _⟩
    have h₁ := comp_eq_of_compatible I Y f hc (l ≫ ρ n) (pullback.fst Y'.hom (thick R (IsLocalRing.maximalIdeal R) n))
      ((Category.assoc _ _ _).trans ((congrArg (l ≫ ·) (hρ n)).trans hl))
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g.left) hl.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (l ≫ ·) (hg n)).trans ((Category.assoc _ _ _).symm.trans h₁))))
  exact ⟨g, key, fun g' hg' => GlobalTheory.hom_eq_of_thickenings_of_isProper R I (hIm.trans hJ) Y Z g' g
    fun e => (hg' e).trans (key e).symm⟩

end GlobalTheory.LocalMorAlg
