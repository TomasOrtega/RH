import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

/- English proof (translation)
Establish `: IsClosedImmersion (thick R I e)` using `IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Use `infer_instance`.
-/
theorem mono_fst_thick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) :
    Mono (pullback.fst G.hom (thick R I e)) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

/- English proof (translation)
Substitute `hF` using the available equality. Use `corr_of_val hL fun z J hJ => ?_` and prove the remaining obligations. Establish `hk : ∀ k, (𝟙 Y' ≫ h) ≫ φ k = 𝟙 Y' ≫ φ' k` using `fun k => by`. Rewrite using `[Category.assoc, ← hψ k, Category.comp_id]`. Establish `hmem : ∀ k, (𝟙 Y' ≫ φ' k) z ∈ L.U (J (𝟙 Y' ≫ φ' k))` using `fun k => hJ _`.

Establish `key` using `hm _ (𝟙 Y') z (fun k => J (𝟙 Y' ≫ φ' k)) (fun k => J (𝟙 Y' ≫ φ' k)) hmem hmem`. Rewrite using `[Finset.prod_eq_one (fun k _ => by`. Rewrite `key` using `[hw _ _ z _ _ (hmem k) (hmem k), gm_self hL _ z (hmem k), one_zpow]), _root_.one_mul]`. Rewrite using `[val_pull hJ, val_of t _ z J _ (fun k => congrArg J (hk k))]`. Conclude with `key.symm`.
-/
theorem corr_pullGen_of_pmaps {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {F : X ⟶ X} (hF : F = 𝟙 X)
    (w : LB.Iso L (L.pull F))
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j k : L.ι), f z ∈ L.U j → f z ∈ L.U k →
      gw w f z j k = gm f z _ (L.g j k))
    {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X)} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {a : LB.Gen (LB.LinComb L φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) (hm : PMaps w φ' φ ε a t h) :
    LB.Gen.Corr L _ _ _ _ a (LB.pullGen L _ _ t h) := by
  subst hF
  refine corr_of_val hL fun z J hJ => ?_
  have hk : ∀ k, (𝟙 Y' ≫ h) ≫ φ k = 𝟙 Y' ≫ φ' k := fun k => by
    rw [Category.assoc, ← hψ k, Category.comp_id]
  have hmem : ∀ k, (𝟙 Y' ≫ φ' k) z ∈ L.U (J (𝟙 Y' ≫ φ' k)) := fun k => hJ _
  have key := hm _ (𝟙 Y') z (fun k => J (𝟙 Y' ≫ φ' k)) (fun k => J (𝟙 Y' ≫ φ' k)) hmem hmem
  rw [Finset.prod_eq_one (fun k _ => by
    rw [hw _ _ z _ _ (hmem k) (hmem k), gm_self hL _ z (hmem k), one_zpow]), _root_.one_mul] at key
  rw [val_pull hJ, val_of t _ z J _ (fun k => congrArg J (hk k))]
  exact key.symm

/- English proof (translation)
Introduce `R _ _ I D A G G' _ _ _ _ ε hD hid bc U U' hF hgen H`. Take `⟨hx, hΦ, hw₀⟩` from `hid`. Take `⟨wL, hg, he, hr, H⟩` from `(isPullUnif_iff_stalks R R I I _ D D hD A A G G' bc U U').1 H`. Establish `hr'` using `(maps_iff wL _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf (RingHom.id R)) _ (rigPull_le _ _ he U.LG.L) (fun _ => rfl)).1 hr`. Use `clear hr he`.

Generalize the expression as in `bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = F at wL hg hr' H hF`. Substitute `hF` using the available equality. Use `⟨hgen, wL, ⟨hg, ?_⟩, fun e => ?_⟩` and prove the remaining obligations. Establish `hs` using `specOf_id R`. Rewrite `hr'` using `[hs]`.

Conclude with `hr'`. Take `⟨h, hf, ⟨hp, ht⟩, hw⟩` from `H e`. Establish `hh : h = ((Over.pullback (thick R I e)).map ε.hom).left`. Use `mono_fst_thick I e G` as an intermediate fact. Rewrite using `[← cancel_mono (pullback.fst G.hom (thick R I e))]`.

Use `hf.trans ?_` and prove the remaining obligations. Conclude with `(pullback.lift_fst _ _ _).symm`. Substitute `hh` using the available equality. Rewrite `hp` using `[hΦ, Category.comp_id]`. Establish `hpt : ∀ y, (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) y = y` using `fun y => by`.

Rewrite using `[hΦ]`. Both sides reduce to the same expression. Use `⟨?_, fun χ => ?_, ?_⟩` and prove the remaining obligations. Use `ext1`. Use `mono_fst_thick I e D.toPre.P.A` as an intermediate fact.

Rewrite using `[← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e))]`. Conclude with `hp`. Take `⟨hψ, hm⟩` from `ht χ`. Rewrite `hψ`, `hm` using `[hx χ]`. Conclude with `corr_pullGen_of_pmaps D.toPre.P.isLB hΦ hD.w hw₀ hψ hm`.

Introduce `Z r z jM jL jL' h₁ h₂ h₃`. Establish `key` using `hw Z r z jM jM jL jL' (by rw [hpt]; exact h₁) h₁ h₂ h₃`. Rewrite `key` using `[hw₀ _ (r ≫ (U'.gt e).pG.left) z jM jM h₁ h₁, gm_self D.toPre.P.isLB (r ≫ (U'.gt e).pG.left) z h₁, _root_.one_mul]`. Conclude with `key`.
-/
theorem sameUnif_of_isPullUnif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (ε : G' ≅ G) (hD : IsPullDeg (RingHom.id R) D.toPre D.toPre), IsIdPull hD → ∀ (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (U : Unif I D A G) (U' : Unif I D A G'), bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ε.hom.left → U'.gen.hom = (Over.pullback (jK R)).map ε.hom ≫ U.gen.hom → IsPullUnif (RingHom.id R) hD bc U U' → SameUnif ε U.toUnifPre U'.toUnifPre := by
  intro R _ _ I D A G G' _ _ _ _ ε hD hid bc U U' hF hgen H
  obtain ⟨hx, hΦ, hw₀⟩ := hid
  obtain ⟨wL, hg, he, hr, H⟩ := (isPullUnif_iff_stalks R R I I _ D D hD A A G G' bc U U').1 H
  have hr' := (maps_iff wL _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf (RingHom.id R)) _
    (rigPull_le _ _ he U.LG.L) (fun _ => rfl)).1 hr
  clear hr he
  generalize bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = F at wL hg hr' H hF
  subst hF
  refine ⟨hgen, wL, ⟨hg, ?_⟩, fun e => ?_⟩
  · have hs := specOf_id R
    rw [hs] at hr'
    exact hr'
  obtain ⟨h, hf, ⟨hp, ht⟩, hw⟩ := H e
  have hh : h = ((Over.pullback (thick R I e)).map ε.hom).left := by
    have := mono_fst_thick I e G
    rw [← cancel_mono (pullback.fst G.hom (thick R I e))]
    refine hf.trans ?_
    exact (pullback.lift_fst _ _ _).symm
  subst hh
  rw [hΦ, Category.comp_id] at hp
  have hpt : ∀ y, (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) y = y := fun y => by
    rw [hΦ]; rfl
  refine ⟨?_, fun χ => ?_, ?_⟩
  · ext1
    have := mono_fst_thick I e D.toPre.P.A
    rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e))]
    exact hp
  · obtain ⟨hψ, hm⟩ := ht χ
    rw [hx χ] at hψ hm
    exact corr_pullGen_of_pmaps D.toPre.P.isLB hΦ hD.w hw₀ hψ hm
  · intro Z r z jM jL jL' h₁ h₂ h₃
    have key := hw Z r z jM jM jL jL' (by rw [hpt]; exact h₁) h₁ h₂ h₃
    rw [hw₀ _ (r ≫ (U'.gt e).pG.left) z jM jM h₁ h₁, gm_self D.toPre.P.isLB (r ≫ (U'.gt e).pG.left) z h₁,
      _root_.one_mul] at key
    exact key

end GlobalTheory.TorsionFormCompare
