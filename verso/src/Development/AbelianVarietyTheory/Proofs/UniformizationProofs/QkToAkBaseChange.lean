import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PhiRelTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaBaseChange

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

/- English proof (translation)
Establish `inj : Function.Injective ((algebraMap R' (FractionRing R')).comp φ)` using `(injective_iff_map_eq_zero _).2 fun r hr => by`. Establish `e` using `hF r`. Rewrite `e` using `[show algebraMap R' (FractionRing R') (φ r) = 0 from hr, map_zero]`. Conclude with `(IsFractionRing.injective R (FractionRing R)) (((algebraMap (FractionRing R) F).injective (e.trans (map_zero _).symm)).trans (map_zero _).symm)`. Take `⟨ψ, h₁⟩ : ∃ ψ : FractionRing R →+* FractionRing R', ψ.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp φ` from `⟨IsFractionRing.lift (K := FractionRing R) inj, RingHom.ext fun r => by`.

Rewrite using `[RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩`. Establish `h₂ : (algebraMap (FractionRing R') F).comp ψ = algebraMap (FractionRing R) F` using `IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (congrArg (algebraMap (FractionRing R') F) (RingHom.congr_fun h₁ r)).trans (hF r).symm)`. Use `⟨Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Spec.map_comp _ _).symm.trans ((congrArg (fun q => Spec.map (CommRingCat.ofHom q)) h₁).trans (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R' (FractionRing R')))))`. Conclude with `(Spec.map_comp _ _).symm.trans (congrArg (fun q => Spec.map (CommRingCat.ofHom q)) h₂)`.
-/
theorem exists_fraction_map {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R')
    (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
    (hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) :
    ∃ g : Spec (CommRingCat.of (FractionRing R')) ⟶ Spec (CommRingCat.of (FractionRing R)),
      g ≫ jK R = jK R' ≫ specOf φ ∧ jFK (R := R') F ≫ g = jFK (R := R) F := by
  have inj : Function.Injective ((algebraMap R' (FractionRing R')).comp φ) :=
    (injective_iff_map_eq_zero _).2 fun r hr => by
      have e := hF r
      rw [show algebraMap R' (FractionRing R') (φ r) = 0 from hr, map_zero] at e
      exact (IsFractionRing.injective R (FractionRing R))
        (((algebraMap (FractionRing R) F).injective (e.trans (map_zero _).symm)).trans (map_zero _).symm)
  obtain ⟨ψ, h₁⟩ : ∃ ψ : FractionRing R →+* FractionRing R',
      ψ.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp φ :=
    ⟨IsFractionRing.lift (K := FractionRing R) inj, RingHom.ext fun r => by
      rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩
  have h₂ : (algebraMap (FractionRing R') F).comp ψ = algebraMap (FractionRing R) F :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r =>
      (congrArg (algebraMap (FractionRing R') F) (RingHom.congr_fun h₁ r)).trans (hF r).symm)
  refine ⟨Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩
  · exact (Spec.map_comp _ _).symm.trans ((congrArg (fun q => Spec.map (CommRingCat.ofHom q)) h₁).trans
      (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R' (FractionRing R')))))
  · exact (Spec.map_comp _ _).symm.trans (congrArg (fun q => Spec.map (CommRingCat.ofHom q)) h₂)

/- English proof (translation)
Use `U.gen_hom` as an intermediate fact. Establish `: IsMonHom U.gen.symm.hom` using `inferInstanceAs (IsMonHom U.gen.inv)`. Conclude with `((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl`.
-/
theorem grp_generic {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) :
    IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) := by
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl

end GlobalTheory.ThetaBaseChange

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaBaseChange in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `hG _ R R' _ _ _ _ I I' _ _ φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU F _ _ _ hF k hk p x p' x' hy hg hx H w' hw'`. Take `⟨wL, hwL, -, -, hlev⟩` from `(isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU`. Take `⟨w, hw⟩` from `U.ext`. Take `⟨hx1, H⟩` from `H w hw`. Take `⟨g, hg₁, hg₂⟩` from `exists_fraction_map φ F hF`.

Establish `gA` using `grp_generic U.toUnifPre`. Establish `gΨ : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ))` using `((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl`. Establish `hΘF : (jFK (R` using `R') F ≫ jK R') ≫ specOf φ = jFK (R := R) F ≫ jK R := by`. Rewrite using `[Category.assoc, ← hg₁, ← Category.assoc, hg₂]`. Take `⟨Θ, hΘ₁, hΘ₂⟩` from `exists_cmp hΘF (pull_grp hD).1.w`.

Establish `gA'` using `(grp_generic U'.toUnifPre).comp gΨ`. Take `⟨Φ, hΦ₁, hΦ₂⟩ : ∃ Φ : A'.A.left ⟶ A.A.left, Φ ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) ∧ Φ ≫ A.A.hom = A'.A.hom ≫ g` from `⟨gA.1.lift _ (A'.A.hom ≫ g) (by rw [gA'.1.w, Category.assoc, hg₁]), gA.1.lift_fst _ _ _, gA.1.lift_snd _ _ _⟩`. Establish `gΦ : IsGrpPullback A'.A A.A g Φ` using `gA.cancel (gA'.congr hg₁.symm hΦ₁.symm) hΦ₂`. Establish `hxΦ : x'.left ≫ Φ = x.left` using `gA.1.hom_ext (by`. Rewrite using `[Category.assoc, hΦ₁, ← hx]; simp only [Category.assoc]) (by`.

Rewrite using `[Category.assoc, hΦ₂, ← Category.assoc, Over.w x', Over.w x]`. Conclude with `hg₂)`. Use `⟨pow_eq_one_of_push hg₂ gΦ hxΦ hx1, fun θ' hθ' => ?_⟩` and prove the remaining obligations. Establish `n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _` using `by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]`. Establish `n₂ : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _` using `by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]`.

Establish `n₃ : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _` using `by rw [← Over.comp_left, U'.gen.hom_inv_id, Over.id_left]`. Establish `hΦ₃ : (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ)`. Rewrite using `[Category.assoc, hΦ₁, ← Category.assoc, ← Category.assoc U'.gen.hom.left, n₃]`. Conclude with `congrArg (· ≫ _) (Category.id_comp _)`. Take `⟨v₂, hv₂, hsq⟩` from `exists_side A.isLB A'.isLB U.LG.isLB U'.LG.isLB hw _ n₁ hw' hwL _ hΦ₃`.

Take `⟨v, hv, hvv⟩` from `exists_unpull hv₂ _ n₂ (P := Φ) (by rw [← Category.assoc, n₂, Category.id_comp])`. Take `⟨Ω, hΩ₁, hΩ₂⟩` from `exists_cmp hg₂ hΦ₂`. Take `⟨ω, hω₁, hω₂⟩` from `exists_cmp_inv hg₂ gΦ.1`. Establish `hΩω : Ω ≫ ω = 𝟙 _` using `cmp_ext gΦ.1 (by rw [Category.assoc, hω₁, hΩ₁, Category.id_comp]) (by rw [Category.assoc, hω₂, hΩ₂, Category.id_comp])`. Set `n : TFK (R` to `R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)`.

Establish `hn : n.left ≫ (U.toUnifPre.genF F).left = 𝟙 _` using `congrArg (fun q => q.left) (show n ≫ U.toUnifPre.genF F = 𝟙 _ by`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp [n])`. Establish `hn₁ : n.left ≫ (fst (TFK (R` using `R) F) ((Over.pullback (jK R)).obj G)).left = (fst (TFK (R := R) F) A.A).left := congrArg (fun q => q.left) (lift_fst _ _ : n ≫ fst _ _ = _)`. Establish `hn₂ : n.left ≫ (snd (TFK (R` using `R) F) ((Over.pullback (jK R)).obj G)).left = (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left := congrArg (fun q => q.left) (lift_snd _ _ : n ≫ snd _ _ = _)`. Establish `hh₁ : (U'.toUnifPre.genF F).left ≫ (fst (TFK (R` using `R') F) A'.A).left = (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left := congrArg (fun q => q.left) (lift_fst _ _ : U'.toUnifPre.genF F ≫ fst _ _ = _)`.

Establish `hh₂ : (U'.toUnifPre.genF F).left ≫ (snd (TFK (R` using `R') F) A'.A).left = (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ U'.gen.hom.left := congrArg (fun q => q.left) (lift_snd _ _ : U'.toUnifPre.genF F ≫ snd _ _ = _)`. Take `⟨Ξ, hΞ⟩ : ∃ Ξ : (UnifPre.GF (G` from `G') F).left ⟶ (UnifPre.GF (G := G) F).left, Ξ = (U'.toUnifPre.genF F).left ≫ Ω ≫ n.left := ⟨_, rfl⟩`. Establish `x₁ : (Ξ ≫ (U.toUnifPre.genF F).left) ≫ ω = (U'.toUnifPre.genF F).left`. Rewrite using `[hΞ, Category.assoc _ (Ω ≫ n.left), Category.assoc Ω, hn, Category.comp_id, Category.assoc, hΩω, Category.comp_id]`. Establish `x₂ : Ξ ≫ (snd (TFK (R` using `R) F) ((Over.pullback (jK R)).obj G)).left = (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left := by`.

Rewrite using `[hΞ, Category.assoc, Category.assoc, hn₂, ← Category.assoc Ω]`. Use `(congrArg (fun a => _ ≫ a ≫ _) hΩ₂).trans ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Category.assoc, hh₂]`. Simplify using `only [Category.assoc]`. Establish `hΞ₁ : Ξ ≫ (fst (TFK (R` using `R) F) ((Over.pullback (jK R)).obj G)).left = (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left := by`.

Rewrite using `[hΞ, Category.assoc, Category.assoc, hn₁]`. Conclude with `(congrArg (_ ≫ ·) hΩ₁).trans hh₁`. Establish `hΞ₂ : Ξ ≫ UnifPre.gFK (G` using `G) F = UnifPre.gFK (G := G') F ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) := by`. Use `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) x₂).trans ?_)` and prove the remaining obligations. Use `Eq.trans ?_ ((congrArg (_ ≫ ·) hΦ₃).trans (Category.assoc _ _ _).symm)` and prove the remaining obligations.

Simplify using `only [Category.assoc]`. Take `⟨θ, hθ, hact⟩` from `exists_theta_moved A.isLB A'.isLB hg₂ gΦ hv hω₁ hω₂ θ' (x := x) (by rw [hθ']; exact hxΦ)`. Take `⟨ν, hν, Hν⟩` from `H θ hθ`. Take `⟨ν', hν', Hν'⟩` from `GlobalTheory.phiRel_transport hG R R' φ D.toPre D'.toPre hD F hF Θ hΘ₁ hΘ₂ k p p' hy hg ν hν`. Use `⟨ν', hν', fun t' t₂' s' s₂' E E₂ hA => ?_⟩` and prove the remaining obligations.

Establish `bij` using `(expandsF_bijective U.toUnifPre F hG hk (U.expand k hk) hw).1`. Establish `bij'` using `(expandsF_bijective U'.toUnifPre F hG hk (U'.expand k hk) hw').1`. Use `choose pl hpl using exists_fam_field_pull hG R R' φ D.toPre D'.toPre hD F hF Θ hΘ₁ hΘ₂ k`. Establish `key : ∀ a' b', U'.toUnifPre.ExpandsF F k w' a' b' → ∃ a b, Moved v ω a' a ∧ U.toUnifPre.ExpandsF F k w a b ∧ pl b = b'` using `fun a' b' E => by`. Take `⟨a, ha⟩` from `exists_moved A.isLB A'.isLB hω₂ n₂ hv₂ hvv a'`.

Take `⟨b, σ, h₁, h₂⟩` from `(bij a).exists`. Use `⟨a, b, ha, ⟨σ, h₁, h₂⟩, (bij' a').unique ?_ E⟩` and prove the remaining obligations. Take `⟨σ', h₁', -⟩` from `E`. Conclude with `⟨σ', h₁', expandsG_transport R R' I I' φ D D' hD A A' G G' bc hbc U.toUnifPre U'.toUnifPre wL hwL hlev F hF Θ hΘ₁ hΘ₂ Ξ hΞ₁ hΞ₂ k σ σ' b (pl b) (moved_sec A.isLB A'.isLB n₃ n₁ hΦ₃ hsq hvv x₁ x₂ ha h₁ h₁') (hpl b) h₂⟩`. Take `⟨t, s, m, e, rfl⟩` from `key t' s' E`.

Take `⟨t₂, s₂, m₂, e₂, rfl⟩` from `key t₂' s₂' E₂`. Conclude with `Hν' s s₂ _ _ (hpl s) (hpl s₂) (Hν t t₂ s s₂ e e₂ (hact t' t₂' t t₂ m m₂ hA))`.
-/
theorem qkToAk_baseChange : GlobalFnsSt → SecBaseChangeSt → QkBaseChangeSt := by
  intro hG _ R R' _ _ _ _ I I' _ _ φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU F _ _ _ hF k hk p x p' x' hy hg hx H w' hw'
  obtain ⟨wL, hwL, -, -, hlev⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨hx1, H⟩ := H w hw
  obtain ⟨g, hg₁, hg₂⟩ := exists_fraction_map φ F hF
  have gA := grp_generic U.toUnifPre
  have gΨ : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have hΘF : (jFK (R := R') F ≫ jK R') ≫ specOf φ = jFK (R := R) F ≫ jK R := by
    rw [Category.assoc, ← hg₁, ← Category.assoc, hg₂]
  obtain ⟨Θ, hΘ₁, hΘ₂⟩ := exists_cmp hΘF (pull_grp hD).1.w
  have gA' := (grp_generic U'.toUnifPre).comp gΨ
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ : ∃ Φ : A'.A.left ⟶ A.A.left, Φ ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) ∧
      Φ ≫ A.A.hom = A'.A.hom ≫ g :=
    ⟨gA.1.lift _ (A'.A.hom ≫ g) (by rw [gA'.1.w, Category.assoc, hg₁]), gA.1.lift_fst _ _ _, gA.1.lift_snd _ _ _⟩
  have gΦ : IsGrpPullback A'.A A.A g Φ := gA.cancel (gA'.congr hg₁.symm hΦ₁.symm) hΦ₂
  have hxΦ : x'.left ≫ Φ = x.left := gA.1.hom_ext (by
    rw [Category.assoc, hΦ₁, ← hx]; simp only [Category.assoc]) (by
    rw [Category.assoc, hΦ₂, ← Category.assoc, Over.w x', Over.w x]; exact hg₂)
  refine ⟨pow_eq_one_of_push hg₂ gΦ hxΦ hx1, fun θ' hθ' => ?_⟩
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have n₂ : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  have n₃ : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.hom_inv_id, Over.id_left]
  have hΦ₃ : (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) := by
    rw [Category.assoc, hΦ₁, ← Category.assoc, ← Category.assoc U'.gen.hom.left, n₃]
    exact congrArg (· ≫ _) (Category.id_comp _)
  obtain ⟨v₂, hv₂, hsq⟩ := exists_side A.isLB A'.isLB U.LG.isLB U'.LG.isLB hw _ n₁ hw' hwL _ hΦ₃
  obtain ⟨v, hv, hvv⟩ := exists_unpull hv₂ _ n₂ (P := Φ) (by rw [← Category.assoc, n₂, Category.id_comp])
  obtain ⟨Ω, hΩ₁, hΩ₂⟩ := exists_cmp hg₂ hΦ₂
  obtain ⟨ω, hω₁, hω₂⟩ := exists_cmp_inv hg₂ gΦ.1
  have hΩω : Ω ≫ ω = 𝟙 _ := cmp_ext gΦ.1 (by rw [Category.assoc, hω₁, hΩ₁, Category.id_comp])
    (by rw [Category.assoc, hω₂, hΩ₂, Category.id_comp])
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n.left ≫ (U.toUnifPre.genF F).left = 𝟙 _ := congrArg (fun q => q.left) (show n ≫ U.toUnifPre.genF F = 𝟙 _ by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n])
  have hn₁ : n.left ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = (fst (TFK (R := R) F) A.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : n ≫ fst _ _ = _)
  have hn₂ : n.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : n ≫ snd _ _ = _)
  have hh₁ : (U'.toUnifPre.genF F).left ≫ (fst (TFK (R := R') F) A'.A).left =
      (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : U'.toUnifPre.genF F ≫ fst _ _ = _)
  have hh₂ : (U'.toUnifPre.genF F).left ≫ (snd (TFK (R := R') F) A'.A).left =
      (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ U'.gen.hom.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : U'.toUnifPre.genF F ≫ snd _ _ = _)
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : (UnifPre.GF (G := G') F).left ⟶ (UnifPre.GF (G := G) F).left,
      Ξ = (U'.toUnifPre.genF F).left ≫ Ω ≫ n.left := ⟨_, rfl⟩
  have x₁ : (Ξ ≫ (U.toUnifPre.genF F).left) ≫ ω = (U'.toUnifPre.genF F).left := by
    rw [hΞ, Category.assoc _ (Ω ≫ n.left), Category.assoc Ω, hn, Category.comp_id, Category.assoc, hΩω,
      Category.comp_id]
  have x₂ : Ξ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left := by
    rw [hΞ, Category.assoc, Category.assoc, hn₂, ← Category.assoc Ω]
    refine (congrArg (fun a => _ ≫ a ≫ _) hΩ₂).trans ?_
    rw [← Category.assoc, ← Category.assoc, hh₂]
    simp only [Category.assoc]
  have hΞ₁ : Ξ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left := by
    rw [hΞ, Category.assoc, Category.assoc, hn₁]
    exact (congrArg (_ ≫ ·) hΩ₁).trans hh₁
  have hΞ₂ : Ξ ≫ UnifPre.gFK (G := G) F = UnifPre.gFK (G := G') F ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) x₂).trans ?_)
    refine Eq.trans ?_ ((congrArg (_ ≫ ·) hΦ₃).trans (Category.assoc _ _ _).symm)
    simp only [Category.assoc]
  obtain ⟨θ, hθ, hact⟩ := exists_theta_moved A.isLB A'.isLB hg₂ gΦ hv hω₁ hω₂ θ' (x := x) (by rw [hθ']; exact hxΦ)
  obtain ⟨ν, hν, Hν⟩ := H θ hθ
  obtain ⟨ν', hν', Hν'⟩ := GlobalTheory.phiRel_transport hG R R' φ D.toPre D'.toPre hD F hF Θ hΘ₁ hΘ₂ k p p' hy hg ν hν
  refine ⟨ν', hν', fun t' t₂' s' s₂' E E₂ hA => ?_⟩
  have bij := (expandsF_bijective U.toUnifPre F hG hk (U.expand k hk) hw).1
  have bij' := (expandsF_bijective U'.toUnifPre F hG hk (U'.expand k hk) hw').1
  choose pl hpl using exists_fam_field_pull hG R R' φ D.toPre D'.toPre hD F hF Θ hΘ₁ hΘ₂ k
  have key : ∀ a' b', U'.toUnifPre.ExpandsF F k w' a' b' → ∃ a b, Moved v ω a' a ∧
      U.toUnifPre.ExpandsF F k w a b ∧ pl b = b' := fun a' b' E => by
    obtain ⟨a, ha⟩ := exists_moved A.isLB A'.isLB hω₂ n₂ hv₂ hvv a'
    obtain ⟨b, σ, h₁, h₂⟩ := (bij a).exists
    refine ⟨a, b, ha, ⟨σ, h₁, h₂⟩, (bij' a').unique ?_ E⟩
    obtain ⟨σ', h₁', -⟩ := E
    exact ⟨σ', h₁', expandsG_transport R R' I I' φ D D' hD A A' G G' bc hbc U.toUnifPre U'.toUnifPre wL hwL hlev F hF
      Θ hΘ₁ hΘ₂ Ξ hΞ₁ hΞ₂ k σ σ' b (pl b)
      (moved_sec A.isLB A'.isLB n₃ n₁ hΦ₃ hsq hvv x₁ x₂ ha h₁ h₁') (hpl b) h₂⟩
  obtain ⟨t, s, m, e, rfl⟩ := key t' s' E
  obtain ⟨t₂, s₂, m₂, e₂, rfl⟩ := key t₂' s₂' E₂
  exact Hν' s s₂ _ _ (hpl s) (hpl s₂) (Hν t t₂ s s₂ e e₂ (hact t' t₂' t t₂ m m₂ hA))

end GlobalTheory
