import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfRelativeDimensionSpreadFromGenericStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricallyConnectedAwayOfGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGroupLawSmoothProperModelOfGenericStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSpreadsOutFromGenericFibreProperStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationSpreadFromGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricSpreadOutLineBundleAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedImmersionGenericUnitLocusStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsKernelPolarisationTrivialSpreadLocalisatioStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetryHypothesisSpreadFromGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointIndependenceSpreadToGeometricFibresStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLevelStructureOfGenericOfFibrewiseIndepStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.GenSpread

section Rings

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

/- English proof (translation)
Use `IsFractionRing.of_field R Ω fun x => ?_` and prove the remaining obligations. Take `⟨a, ha, b, hb, rfl⟩` from `h x`. Conclude with `⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩`.
-/
theorem isFractionRing_of_forall_div {R : Subalgebra o Ω} (h : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) :
    IsFractionRing R Ω := by
  refine IsFractionRing.of_field R Ω fun x => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := h x
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

/- English proof (translation)
The claim follows from `have : Algebra.FiniteType o R := (Subalgebra.fg_iff_finiteType _).1 h Algebra.FiniteType.isNoetherianRing o R`.
-/
theorem isNoetherianRing_of_fg [IsNoetherianRing o] {R : Subalgebra o Ω} (h : R.FG) : IsNoetherianRing R :=
  have : Algebra.FiniteType o R := (Subalgebra.fg_iff_finiteType _).1 h
  Algebra.FiniteType.isNoetherianRing o R

/- English proof (translation)
Set `R' : Subalgebra o Ω` to `R ⊔ Algebra.adjoin o (Set.range fun i => (a i : Ω)⁻¹)`. Establish `hle : R ≤ R'` using `le_sup_left`. Set `g : R →+* R'` to `(Subalgebra.inclusion hle).toRingHom`. Establish `e : spMap (algebraMap R' Ω) ≫ spMap g = spMap (algebraMap R Ω)`. Rewrite using `[← Spec.map_comp]`.

Both sides reduce to the same expression. Use `⟨R', g, hle, hR.sup ?_, rfl, fun i => ?_, pullback.lift φ (f₀ ≫ spMap (algebraMap R' Ω)) (by rw [Category.assoc, e, h.w]), pullback.lift_fst _ _ _, ?_⟩` and prove the remaining obligations. Conclude with `(Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)`. Establish `hm : (a i : Ω)⁻¹ ∈ R'` using `(le_sup_right : _ ≤ R') (Algebra.subset_adjoin ⟨i, rfl⟩)`. Use `IsUnit.of_mul_eq_one ⟨_, hm⟩ (Subtype.ext ?_)` and prove the remaining obligations.

Conclude with `mul_inv_cancel₀ (fun h0 => ha i (Subtype.ext h0))`. Use `IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (spMap g))` and prove the remaining obligations. Rewrite using `[pullback.lift_fst, e]` and apply the resulting hypothesis.
-/
theorem exists_shrink {R : Subalgebra o Ω} (hR : R.FG) {J : Type} [Finite J] (a : J → R) (ha : ∀ i, a i ≠ 0)
    {X X₀ : Scheme.{0}} {f : X ⟶ Sp R} {f₀ : X₀ ⟶ Sp Ω} {φ : X₀ ⟶ X}
    (h : IsPullback φ f₀ f (spMap (algebraMap R Ω))) :
    ∃ (R' : Subalgebra o Ω) (g : R →+* R'), R ≤ R' ∧ R'.FG ∧ (algebraMap R' Ω).comp g = algebraMap R Ω ∧
      (∀ i, IsUnit (g (a i))) ∧ ∃ φ' : X₀ ⟶ pullback f (spMap g), φ' ≫ pullback.fst _ _ = φ ∧
        IsPullback φ' f₀ (pullback.snd f (spMap g)) (spMap (algebraMap R' Ω)) := by
  let R' : Subalgebra o Ω := R ⊔ Algebra.adjoin o (Set.range fun i => (a i : Ω)⁻¹)
  have hle : R ≤ R' := le_sup_left
  let g : R →+* R' := (Subalgebra.inclusion hle).toRingHom
  have e : spMap (algebraMap R' Ω) ≫ spMap g = spMap (algebraMap R Ω) := by
    rw [← Spec.map_comp]; rfl
  refine ⟨R', g, hle, hR.sup ?_, rfl, fun i => ?_,
    pullback.lift φ (f₀ ≫ spMap (algebraMap R' Ω)) (by rw [Category.assoc, e, h.w]), pullback.lift_fst _ _ _, ?_⟩
  · exact (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  · have hm : (a i : Ω)⁻¹ ∈ R' := (le_sup_right : _ ≤ R') (Algebra.subset_adjoin ⟨i, rfl⟩)
    refine IsUnit.of_mul_eq_one ⟨_, hm⟩ (Subtype.ext ?_)
    exact mul_inv_cancel₀ (fun h0 => ha i (Subtype.ext h0))
  · refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (spMap g))
    rwa [pullback.lift_fst, e]

end Rings

/- English proof (translation)
Use `map_list_prod (preHom (G := A) t) (List.ofFn fun i => y i ^ c i)` as an intermediate fact. Simplify using `only [List.map_ofFn, Function.comp_def, map_pow] at this`. Conclude with `this`.
-/
theorem comp_linComb {S : Scheme.{0}} {A : Over S} [GrpObj A] {T T' : Over S} (t : T' ⟶ T) {n : ℕ}
    (y : Fin n → (T ⟶ A)) (c : Fin n → ℕ) : t ≫ linComb y c = linComb (fun i => t ≫ y i) c := by
  have := map_list_prod (preHom (G := A) t) (List.ofFn fun i => y i ^ c i)
  simp only [List.map_ofFn, Function.comp_def, map_pow] at this
  exact this

/- English proof (translation)
Introduce `o Ω _ _ _ hB R₀ hR₀ hfr P M ze hM hS lev hL`. Use `hB.ded` as an intermediate fact. Take `⟨w₀, wd₀, hw₀, hwd₀, hww, hS₁, hS₂⟩` from `hS`. Use `P.isAb.proper` as an intermediate fact. Use `P.isAb.smooth` as an intermediate fact.

Use `isFractionRing_of_forall_div hfr` as an intermediate fact. Use `isNoetherianRing_of_fg hR₀` as an intermediate fact. Take `⟨X₀, f₀, φ₀, H₀, N, hf₀, p₀, hH₀, aH₀, hN, eH₀⟩` from `exists_projective_model (R := R₀) P.A.hom (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample) P.isLB`. Take `⟨a₀, ha₀, Hsm⟩` from `GlobalTheory.T.exists_smoothOfRelativeDimension_spread_from_genericFibre R₀ Ω P.g X₀ _ f₀ _ φ₀ p₀ hf₀ P.smoothDim`. Take `⟨R₁, g₁, le₁, hR₁, c₁, u₁, φ₁, e₁, p₁⟩` from `exists_shrink hR₀ (fun _ : PUnit => a₀) (fun _ => ha₀) p₀`.

Establish `hsm₁` using `Hsm R₁ g₁ (u₁ ⟨⟩) _ _ _ (IsPullback.of_hasPullback f₀ (spMap g₁))`. Establish `hH₁` using `pull_isLB hH₀ (pullback.fst f₀ (spMap g₁))`. Establish `aH₁` using `@IsAmpleLB.pull_of_isAffineHom _ _ _ aH₀ (pullback.fst f₀ (spMap g₁)) (MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback f₀ (spMap g₁)).flip inferInstance)`. Establish `eH₁` using `LBIso.trans (isLB_lbPow P.isLB N) (pull_isLB hH₀ _) (pull_isLB hH₁ _) eH₀ (lbIso_pull_pull hH₀ φ₁ e₁.symm)`. Establish `hf₁ : IsProper (pullback.snd f₀ (spMap g₁))` using `inferInstance`.

Generalize the expression as in `H₀.pull (pullback.fst f₀ (spMap g₁)) = H₁ at hH₁ aH₁ eH₁`. Use `clear e₁`. Generalize the expression as in `pullback.snd f₀ (spMap g₁) = f₁ at hsm₁ hf₁ p₁`. Generalize the expression as in `pullback f₀ (spMap g₁) = X₁ at f₁ φ₁ H₁ hsm₁ hf₁ p₁ hH₁ aH₁ eH₁`. Establish `hfr₁ : ∀ x : Ω, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b` using `fun x => by`.

Take `⟨a, ha, b, hb, e⟩` from `hfr x`. Conclude with `⟨a, le₁ ha, b, le₁ hb, e⟩`. Use `clear Hsm u₁ c₁ eH₀ aH₀ hH₀ p₀ ha₀`. Use `isFractionRing_of_forall_div hfr₁` as an intermediate fact. Use `isNoetherianRing_of_fg hR₁` as an intermediate fact.

Establish `hs₁ : Smooth f₁` using `SmoothOfRelativeDimension.smooth P.g f₁`. Establish `: LocallyOfFinitePresentation f₁` using `inferInstance`. Take `⟨a₁, ha₁, Hconn⟩` from `GlobalTheory.T.exists_geometricallyConnected_away_of_genericFibre R₁ Ω X₁ _ f₁ _ φ₁ p₁ hs₁ ((ProjSpace.isProjBy_iff_isProjOver f₁).2 (aH₁.isProjOver f₁)) P.isAb.geomConnected`. Take `⟨a₂, ha₂, Hgrp⟩` from `GlobalTheory.T.exists_group_law_smooth_proper_model_of_generic R₁ Ω X₁ f₁ P.A φ₁ p₁ hs₁ hf₁`. Take `⟨a₃, ha₃, Hlb⟩` from `GlobalTheory.T.lineBundle_spreads_out_from_genericFibre_proper R₁ Ω X₁ _ f₁ _ φ₁ p₁ inferInstance hf₁ P.L P.isLB`.

Take `⟨a₄, ha₄, Hw⟩` from `exists_hom f₁ f₁ p₁ (w₀.left ≫ φ₁) (by rw [Category.assoc, p₁.w, Over.w_assoc])`. Take `⟨a₅, ha₅, Hwd⟩` from `exists_hom f₁ f₁ p₁ (wd₀.left ≫ φ₁) (by rw [Category.assoc, p₁.w, Over.w_assoc])`. Use `choose b hb Hpt using fun i => exists_hom (𝟙 (Sp R₁)) f₁ (φ := spMap (algebraMap R₁ Ω)) (p₀ := 𝟙 (Sp Ω)) (IsPullback.of_vert_isIso ⟨by simp⟩) ((lev.pt i).left ≫ φ₁) (by`. Rewrite using `[Category.assoc, p₁.w, Over.w_assoc]`. Use the proof step `simp)`.

Apply the tactic sequence `obtain ⟨R₂, g₂, le₂, hR₂, c₂, u₂, φ₂, e₂, p₂⟩ := exists_shrink hR₁ (Sum.elim ![a₁, a₂, a₃, a₄, a₅] b) (by rintro (i | i); · fin_cases i <;> assumption`. Conclude with `hb i) p₁`. Establish `es₂ : spMap (algebraMap R₂ Ω) ≫ spMap g₂ = spMap (algebraMap R₁ Ω)`. Rewrite using `[← c₂, ← Spec.map_comp]`. Both sides reduce to the same expression.

Establish `q₂` using `IsPullback.of_hasPullback f₁ (spMap g₂)`. Set `G : Over (Sp R₂)` to `Over.mk (pullback.snd f₁ (spMap g₂))`. Take `⟨_, hcomm, hG⟩` from `Hgrp R₂ g₂ (u₂ (.inl 1)) (algebraMap R₂ Ω) Subtype.val_injective c₂ G (pullback.fst _ _) φ₂ q₂ e₂ p₂.w`. Take `⟨L₂, hL₂, eL₂⟩` from `Hlb R₂ g₂ (u₂ (.inl 2)) _ _ _ q₂.w`. Use `replace eL₂ := eL₂ φ₂ e₂`.

Establish `endo : ∀ v₀ : P.A ⟶ P.A, (∃ u : G.left ⟶ X₁, u ≫ f₁ = pullback.fst f₁ (spMap g₂) ≫ f₁ ∧ ∀ φ' : P.A.left ⟶ G.left, φ' ≫ pullback.fst f₁ (spMap g₂) = φ₁ → φ' ≫ u = v₀.left ≫ φ₁) → ∃ v : G ⟶ G, φ₂ ≫ v.left = v₀.left ≫ φ₂`. Introduce and unpack `v₀ ⟨u, hu, hu'⟩`. Use `⟨Over.homMk (q₂.lift u G.hom (hu.trans q₂.w)) (q₂.lift_snd _ _ _), q₂.hom_ext ?_ ?_⟩` and prove the remaining obligations. Simplify using `only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, e₂]`. Conclude with `hu' φ₂ e₂`.

Simplify using `only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, p₂.w, Over.w_assoc]`. Conclude with `p₂.w`. Take `⟨w, hw⟩` from `endo w₀ (Hw R₂ g₂ (u₂ (.inl 3)) _ _ _ q₂.w)`. Take `⟨wd, hwd⟩` from `endo wd₀ (Hwd R₂ g₂ (u₂ (.inl 4)) _ _ _ q₂.w)`. Establish `pts : ∀ i, ∃ y : baseOver (Sp R₂) ⟶ G, (lev.pt i).left ≫ φ₂ = spMap (algebraMap R₂ Ω) ≫ y.left` using `fun i => by`.

Take `⟨u, hu, hu'⟩` from `Hpt i R₂ g₂ (u₂ (.inr i)) (Sp R₂) (spMap g₂) (𝟙 _) (by simp)`. Use `⟨Over.homMk (q₂.lift u (𝟙 _) (by simpa using hu)) (q₂.lift_snd _ _ _), q₂.hom_ext ?_ ?_⟩` and prove the remaining obligations. Simplify using `only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, e₂]`. Conclude with `(hu' _ es₂).symm`. Simplify using `only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, p₂.w, Over.w_assoc]`.

Simplify using the standard rewrite rules. Use `choose y hy using pts`. Establish `hsm₂ : SmoothOfRelativeDimension P.g G.hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback q₂ hsm₁`. Establish `hab : IsAbelianScheme G` using `{ comm := hcomm smooth := SmoothOfRelativeDimension.smooth P.g G.hom proper := inferInstanceAs (IsProper (pullback.snd f₁ (spMap g₂))) geomConnected := Hconn R₂ g₂ (u₂ (.inl 0)) _ _ _ q₂ }`. Establish `hH₂` using `pull_isLB hH₁ (pullback.fst f₁ (spMap g₂))`.

Establish `aH₂` using `@IsAmpleLB.pull_of_isAffineHom _ _ _ aH₁ (pullback.fst f₁ (spMap g₂)) (MorphismProperty.of_isPullback (P := @IsAffineHom) q₂.flip inferInstance)`. Establish `eH₂` using `LBIso.trans (isLB_lbPow P.isLB N) (pull_isLB hH₁ _) (pull_isLB hH₂ _) eH₁ (lbIso_pull_pull hH₁ φ₂ e₂.symm)`. Establish `hfr₂ : ∀ x : Ω, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b` using `fun x => by`. Take `⟨a, ha, b, hb, e⟩` from `hfr₁ x`. Conclude with `⟨a, le₂ ha, b, le₂ hb, e⟩`.

Use `isFractionRing_of_forall_div hfr₂` as an intermediate fact. Use `isNoetherianRing_of_fg hR₂` as an intermediate fact. Use `hab.proper` as an intermediate fact. Take `⟨d₀, hd₀, Hrig⟩` from `GlobalTheory.T.exists_rigidification_spread_from_genericFibre R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ P.rigid`. Take `⟨d₁, hd₁, Hsym⟩` from `GlobalTheory.T.exists_symmetric_spread_out_lineBundle_abelian_scheme R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ P.sym`.

Take `⟨d₂, hd₂, Hk⟩` from `GlobalTheory.T.exists_kernelPolarisation_trivial_spread_localisation hL.globalFns R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ ((ProjSpace.isProjBy_iff_isProjOver G.hom).2 (aH₂.isProjOver G.hom)) P.ktriv`. Take `⟨d₃, hd₃, Hs⟩` from `GlobalTheory.T.exists_symmetryHypothesis_spread_from_genericFibre R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ w wd w₀ wd₀ hw hwd hw₀ hwd₀ hww hS₁ hS₂`. Take `⟨d₄, hd₄, Hi⟩` from `GlobalTheory.T.exists_pointIndependence_spread_to_geometricFibres R₂ Ω G P.A φ₂ inferInstance hG _ M y lev.pt hy fun c c' h => by`. Use `lev.indep (AlgebraicClosure Ω) (spMap (algebraMap Ω _)) c c' ?_` and prove the remaining obligations. Rewrite using `[← comp_linComb, ← comp_linComb, h]`.

Take `⟨d₅, hd₅, Ha⟩` from `exists_isAmpleLB G.hom hG.1 hL₂ hH₂ P.isLB aH₂ hN eL₂ eH₂`. Apply the tactic sequence `obtain ⟨R₃, g₃, le₃, hR₃, c₃, u₃, φ₃, e₃, p₃⟩ := exists_shrink hR₂ ![d₀, d₁, d₂, d₃, d₄, d₅] (by intro i; fin_cases i <;> assumption) hG.1`. Establish `es₃ : spMap (algebraMap R₃ Ω) ≫ spMap g₃ = spMap (algebraMap R₂ Ω)`. Rewrite using `[← c₃, ← Spec.map_comp]`. Both sides reduce to the same expression.

Establish `q₃` using `isGrpPullback_pullback G (spMap g₃)`. Establish `hL₃` using `pull_isLB hL₂ (pullback.fst G.hom (spMap g₃))`. Establish `hab₃` using `PolPull.isAbelianScheme_of_isGrpPullback hab q₃`. Use `hab₃.comm` as an intermediate fact. Use `hab₃.proper` as an intermediate fact.

Set `P' : PolAV (Sp R₃)` to `{ A := (Over.pullback (spMap g₃)).obj G isAb := hab₃ g := P.g smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback q₃.1 hsm₂ L := L₂.pull (pullback.fst G.hom (spMap g₃)) isLB := hL₃ rigid := Hrig R₃ g₃ (u₃ 0) _ _ _ q₃ hL₃ (lbIso_refl hL₃) sym := Hsym …`. Establish `hG₃ : IsGrpPullback P.A P'.A (spMap (algebraMap R₃ Ω)) φ₃` using `IsGrpPullback.cancel q₃ (hG.congr es₃.symm e₃.symm) p₃.w`. Establish `eL₃ : LBIso P.L (P'.L.pull φ₃)` using `LBIso.trans P.isLB (pull_isLB hL₂ _) (pull_isLB hL₃ _) eL₂ (lbIso_pull_pull hL₂ φ₃ e₃.symm)`. Set `y' : Fin (2 * P.g) → (baseOver (Sp R₃) ⟶ P'.A)` to `fun i => Over.homMk (q₃.1.lift (spMap g₃ ≫ (y i).left) (𝟙 _) (by simp)) (q₃.1.lift_snd _ _ _)`. Establish `hy' : ∀ i, (y' i).left ≫ pullback.fst G.hom (spMap g₃) = spMap g₃ ≫ (y i).left` using `fun i => q₃.1.lift_fst _ _ _`.

Establish `hy₃ : ∀ (i₀ : Fin (2 * P.g)) (i : Fin (2 * P'.g)), (i₀ : ℕ) = i → (lev.pt i₀).left ≫ φ₃ = spMap (algebraMap R₃ Ω) ≫ (y' i).left`. Introduce `i₀ i hi`. Take `rfl : i₀ = i` from `Fin.ext hi`. Use `q₃.1.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hy', e₃, hy, reassoc_of% es₃]`.

Rewrite using `[Category.assoc, Category.assoc, hG₃.1.w, Over.w_assoc, Over.w]`. Simplify using the standard rewrite rules. Establish `hfr₃ : ∀ x : Ω, ∃ a ∈ R₃, ∃ b ∈ R₃, x = a / b` using `fun x => by`. Take `⟨a, ha, b, hb, e⟩` from `hfr₂ x`. Conclude with `⟨a, le₃ ha, b, le₃ hb, e⟩`.

Use `isFractionRing_of_forall_div hfr₃` as an intermediate fact. Use `isNoetherianRing_of_fg hR₃` as an intermediate fact. Take `⟨lev', hlev⟩` from `GlobalTheory.T.isLevelStructure_of_generic_of_fibrewise_indep hL R₃ Ω P' P φ₃ hG₃ eL₃ rfl M (Units.map (algebraMap o R₃).toMonoidHom ze) _ (by simpa using hM.map (algebraMap o R₃)) rfl lev y' hy₃ (Hi R₃ g₃ (u₃ 4) _ _ y' q₃ hy')`. Use `⟨R₃, P', φ₃, lev', le₁.trans (le₂.trans le₃), hR₃, rfl, Hs R₃ g₃ (u₃ 3) _ _ _ q₃ hL₃ (lbIso_refl hL₃), hG₃, eL₃, ?_⟩` and prove the remaining obligations. Rewrite using `[hlev]`.

Conclude with `hy₃`.
-/
theorem polAV_spreads_out : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R₀ : Subalgebra o Ω), R₀.FG → (∀ x : Ω, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) → ∀ (P : PolAV (Sp Ω)) (M : ℕ) (ze : oˣ), IsUnit (M : o) → HypS P.A P.L → ∀ lev : Out.Level P M (unitOn (Units.map (algebraMap o Ω).toMonoidHom ze)), Laws → ∃ (R : Subalgebra o Ω) (P' : PolAV (Sp R)) (φ : P.A.left ⟶ P'.A.left) (lev' : Out.Level P' M (unitOn (Units.map (algebraMap o R).toMonoidHom ze))), R₀ ≤ R ∧ R.FG ∧ P'.g = P.g ∧ HypS P'.A P'.L ∧ IsGrpPullback P.A P'.A (spMap R.val.toRingHom) φ ∧ LBIso P.L (P'.L.pull φ) ∧ ∀ (i : Fin (2 * P.g)) (i' : Fin (2 * P'.g)), (i : ℕ) = i' → (lev.pt i).left ≫ φ = spMap R.val.toRingHom ≫ (lev'.pt i').left := by
  intro o Ω _ _ _ hB R₀ hR₀ hfr P M ze hM hS lev hL
  have := hB.ded
  obtain ⟨w₀, wd₀, hw₀, hwd₀, hww, hS₁, hS₂⟩ := hS
  have := P.isAb.proper
  have := P.isAb.smooth

  have := isFractionRing_of_forall_div hfr
  have := isNoetherianRing_of_fg hR₀
  obtain ⟨X₀, f₀, φ₀, H₀, N, hf₀, p₀, hH₀, aH₀, hN, eH₀⟩ := exists_projective_model (R := R₀) P.A.hom
    (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample) P.isLB
  obtain ⟨a₀, ha₀, Hsm⟩ := GlobalTheory.T.exists_smoothOfRelativeDimension_spread_from_genericFibre R₀ Ω P.g X₀ _ f₀ _ φ₀ p₀ hf₀ P.smoothDim
  obtain ⟨R₁, g₁, le₁, hR₁, c₁, u₁, φ₁, e₁, p₁⟩ := exists_shrink hR₀ (fun _ : PUnit => a₀) (fun _ => ha₀) p₀
  have hsm₁ := Hsm R₁ g₁ (u₁ ⟨⟩) _ _ _ (IsPullback.of_hasPullback f₀ (spMap g₁))
  have hH₁ := pull_isLB hH₀ (pullback.fst f₀ (spMap g₁))
  have aH₁ := @IsAmpleLB.pull_of_isAffineHom _ _ _ aH₀ (pullback.fst f₀ (spMap g₁))
    (MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback f₀ (spMap g₁)).flip inferInstance)
  have eH₁ := LBIso.trans (isLB_lbPow P.isLB N) (pull_isLB hH₀ _) (pull_isLB hH₁ _) eH₀
    (lbIso_pull_pull hH₀ φ₁ e₁.symm)
  have hf₁ : IsProper (pullback.snd f₀ (spMap g₁)) := inferInstance
  generalize H₀.pull (pullback.fst f₀ (spMap g₁)) = H₁ at hH₁ aH₁ eH₁
  clear e₁
  generalize pullback.snd f₀ (spMap g₁) = f₁ at hsm₁ hf₁ p₁
  generalize pullback f₀ (spMap g₁) = X₁ at f₁ φ₁ H₁ hsm₁ hf₁ p₁ hH₁ aH₁ eH₁
  have hfr₁ : ∀ x : Ω, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr x
    exact ⟨a, le₁ ha, b, le₁ hb, e⟩
  clear Hsm u₁ c₁ eH₀ aH₀ hH₀ p₀ ha₀

  have := isFractionRing_of_forall_div hfr₁
  have := isNoetherianRing_of_fg hR₁
  have hs₁ : Smooth f₁ := SmoothOfRelativeDimension.smooth P.g f₁
  have : LocallyOfFinitePresentation f₁ := inferInstance
  obtain ⟨a₁, ha₁, Hconn⟩ := GlobalTheory.T.exists_geometricallyConnected_away_of_genericFibre R₁ Ω X₁ _ f₁ _ φ₁ p₁ hs₁
    ((ProjSpace.isProjBy_iff_isProjOver f₁).2 (aH₁.isProjOver f₁)) P.isAb.geomConnected
  obtain ⟨a₂, ha₂, Hgrp⟩ := GlobalTheory.T.exists_group_law_smooth_proper_model_of_generic R₁ Ω X₁ f₁ P.A φ₁ p₁ hs₁ hf₁
  obtain ⟨a₃, ha₃, Hlb⟩ := GlobalTheory.T.lineBundle_spreads_out_from_genericFibre_proper R₁ Ω X₁ _ f₁ _ φ₁ p₁ inferInstance hf₁ P.L P.isLB
  obtain ⟨a₄, ha₄, Hw⟩ := exists_hom f₁ f₁ p₁ (w₀.left ≫ φ₁) (by rw [Category.assoc, p₁.w, Over.w_assoc])
  obtain ⟨a₅, ha₅, Hwd⟩ := exists_hom f₁ f₁ p₁ (wd₀.left ≫ φ₁) (by rw [Category.assoc, p₁.w, Over.w_assoc])
  choose b hb Hpt using fun i => exists_hom (𝟙 (Sp R₁)) f₁ (φ := spMap (algebraMap R₁ Ω)) (p₀ := 𝟙 (Sp Ω))
    (IsPullback.of_vert_isIso ⟨by simp⟩) ((lev.pt i).left ≫ φ₁) (by
      rw [Category.assoc, p₁.w, Over.w_assoc]; simp)
  obtain ⟨R₂, g₂, le₂, hR₂, c₂, u₂, φ₂, e₂, p₂⟩ := exists_shrink hR₁ (Sum.elim ![a₁, a₂, a₃, a₄, a₅] b)
    (by rintro (i | i); · fin_cases i <;> assumption
        · exact hb i) p₁
  have es₂ : spMap (algebraMap R₂ Ω) ≫ spMap g₂ = spMap (algebraMap R₁ Ω) := by
    rw [← c₂, ← Spec.map_comp]; rfl
  have q₂ := IsPullback.of_hasPullback f₁ (spMap g₂)
  let G : Over (Sp R₂) := Over.mk (pullback.snd f₁ (spMap g₂))
  obtain ⟨_, hcomm, hG⟩ := Hgrp R₂ g₂ (u₂ (.inl 1)) (algebraMap R₂ Ω) Subtype.val_injective c₂ G
    (pullback.fst _ _) φ₂ q₂ e₂ p₂.w
  obtain ⟨L₂, hL₂, eL₂⟩ := Hlb R₂ g₂ (u₂ (.inl 2)) _ _ _ q₂.w
  replace eL₂ := eL₂ φ₂ e₂
  have endo : ∀ v₀ : P.A ⟶ P.A, (∃ u : G.left ⟶ X₁, u ≫ f₁ = pullback.fst f₁ (spMap g₂) ≫ f₁ ∧
      ∀ φ' : P.A.left ⟶ G.left, φ' ≫ pullback.fst f₁ (spMap g₂) = φ₁ → φ' ≫ u = v₀.left ≫ φ₁) →
      ∃ v : G ⟶ G, φ₂ ≫ v.left = v₀.left ≫ φ₂ := by
    rintro v₀ ⟨u, hu, hu'⟩
    refine ⟨Over.homMk (q₂.lift u G.hom (hu.trans q₂.w)) (q₂.lift_snd _ _ _), q₂.hom_ext ?_ ?_⟩
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, e₂]
      exact hu' φ₂ e₂
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, p₂.w, Over.w_assoc]
      exact p₂.w
  obtain ⟨w, hw⟩ := endo w₀ (Hw R₂ g₂ (u₂ (.inl 3)) _ _ _ q₂.w)
  obtain ⟨wd, hwd⟩ := endo wd₀ (Hwd R₂ g₂ (u₂ (.inl 4)) _ _ _ q₂.w)
  have pts : ∀ i, ∃ y : baseOver (Sp R₂) ⟶ G, (lev.pt i).left ≫ φ₂ = spMap (algebraMap R₂ Ω) ≫ y.left := fun i => by
    obtain ⟨u, hu, hu'⟩ := Hpt i R₂ g₂ (u₂ (.inr i)) (Sp R₂) (spMap g₂) (𝟙 _) (by simp)
    refine ⟨Over.homMk (q₂.lift u (𝟙 _) (by simpa using hu)) (q₂.lift_snd _ _ _), q₂.hom_ext ?_ ?_⟩
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, e₂]
      exact (hu' _ es₂).symm
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, p₂.w, Over.w_assoc]
      simp
  choose y hy using pts
  have hsm₂ : SmoothOfRelativeDimension P.g G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback q₂ hsm₁
  have hab : IsAbelianScheme G :=
    { comm := hcomm
      smooth := SmoothOfRelativeDimension.smooth P.g G.hom
      proper := inferInstanceAs (IsProper (pullback.snd f₁ (spMap g₂)))
      geomConnected := Hconn R₂ g₂ (u₂ (.inl 0)) _ _ _ q₂ }
  have hH₂ := pull_isLB hH₁ (pullback.fst f₁ (spMap g₂))
  have aH₂ := @IsAmpleLB.pull_of_isAffineHom _ _ _ aH₁ (pullback.fst f₁ (spMap g₂))
    (MorphismProperty.of_isPullback (P := @IsAffineHom) q₂.flip inferInstance)
  have eH₂ := LBIso.trans (isLB_lbPow P.isLB N) (pull_isLB hH₁ _) (pull_isLB hH₂ _) eH₁
    (lbIso_pull_pull hH₁ φ₂ e₂.symm)
  have hfr₂ : ∀ x : Ω, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr₁ x
    exact ⟨a, le₂ ha, b, le₂ hb, e⟩

  have := isFractionRing_of_forall_div hfr₂
  have := isNoetherianRing_of_fg hR₂
  have := hab.proper
  obtain ⟨d₀, hd₀, Hrig⟩ := GlobalTheory.T.exists_rigidification_spread_from_genericFibre R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ P.rigid
  obtain ⟨d₁, hd₁, Hsym⟩ := GlobalTheory.T.exists_symmetric_spread_out_lineBundle_abelian_scheme R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ P.sym
  obtain ⟨d₂, hd₂, Hk⟩ := GlobalTheory.T.exists_kernelPolarisation_trivial_spread_localisation hL.globalFns R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂
    ((ProjSpace.isProjBy_iff_isProjOver G.hom).2 (aH₂.isProjOver G.hom)) P.ktriv
  obtain ⟨d₃, hd₃, Hs⟩ := GlobalTheory.T.exists_symmetryHypothesis_spread_from_genericFibre R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ w wd w₀ wd₀ hw hwd hw₀ hwd₀ hww hS₁ hS₂
  obtain ⟨d₄, hd₄, Hi⟩ := GlobalTheory.T.exists_pointIndependence_spread_to_geometricFibres R₂ Ω G P.A φ₂ inferInstance hG _ M y lev.pt hy fun c c' h => by
    refine lev.indep (AlgebraicClosure Ω) (spMap (algebraMap Ω _)) c c' ?_
    rw [← comp_linComb, ← comp_linComb, h]
  obtain ⟨d₅, hd₅, Ha⟩ := exists_isAmpleLB G.hom hG.1 hL₂ hH₂ P.isLB aH₂ hN eL₂ eH₂
  obtain ⟨R₃, g₃, le₃, hR₃, c₃, u₃, φ₃, e₃, p₃⟩ := exists_shrink hR₂ ![d₀, d₁, d₂, d₃, d₄, d₅]
    (by intro i; fin_cases i <;> assumption) hG.1
  have es₃ : spMap (algebraMap R₃ Ω) ≫ spMap g₃ = spMap (algebraMap R₂ Ω) := by
    rw [← c₃, ← Spec.map_comp]; rfl
  have q₃ := isGrpPullback_pullback G (spMap g₃)
  have hL₃ := pull_isLB hL₂ (pullback.fst G.hom (spMap g₃))
  have hab₃ := PolPull.isAbelianScheme_of_isGrpPullback hab q₃
  have := hab₃.comm
  have := hab₃.proper
  let P' : PolAV (Sp R₃) :=
    { A := (Over.pullback (spMap g₃)).obj G
      isAb := hab₃
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback q₃.1 hsm₂
      L := L₂.pull (pullback.fst G.hom (spMap g₃))
      isLB := hL₃
      rigid := Hrig R₃ g₃ (u₃ 0) _ _ _ q₃ hL₃ (lbIso_refl hL₃)
      sym := Hsym R₃ g₃ (u₃ 1) _ _ _ q₃ hL₃ (lbIso_refl hL₃)
      ample := (relAmple_iff_isAmpleLB_of_isAffine _ hL₃).2 (Ha R₃ g₃ (u₃ 5) _ _ _ q₃.1)
      ktriv := Hk R₃ g₃ (u₃ 2) _ _ _ q₃ hL₃ (lbIso_refl hL₃) }
  have hG₃ : IsGrpPullback P.A P'.A (spMap (algebraMap R₃ Ω)) φ₃ :=
    IsGrpPullback.cancel q₃ (hG.congr es₃.symm e₃.symm) p₃.w
  have eL₃ : LBIso P.L (P'.L.pull φ₃) := LBIso.trans P.isLB (pull_isLB hL₂ _) (pull_isLB hL₃ _) eL₂
    (lbIso_pull_pull hL₂ φ₃ e₃.symm)
  let y' : Fin (2 * P.g) → (baseOver (Sp R₃) ⟶ P'.A) := fun i =>
    Over.homMk (q₃.1.lift (spMap g₃ ≫ (y i).left) (𝟙 _) (by simp)) (q₃.1.lift_snd _ _ _)
  have hy' : ∀ i, (y' i).left ≫ pullback.fst G.hom (spMap g₃) = spMap g₃ ≫ (y i).left := fun i =>
    q₃.1.lift_fst _ _ _
  have hy₃ : ∀ (i₀ : Fin (2 * P.g)) (i : Fin (2 * P'.g)), (i₀ : ℕ) = i →
      (lev.pt i₀).left ≫ φ₃ = spMap (algebraMap R₃ Ω) ≫ (y' i).left := by
    intro i₀ i hi
    obtain rfl : i₀ = i := Fin.ext hi
    refine q₃.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hy', e₃, hy, reassoc_of% es₃]
    · rw [Category.assoc, Category.assoc, hG₃.1.w, Over.w_assoc, Over.w]
      simp
  have hfr₃ : ∀ x : Ω, ∃ a ∈ R₃, ∃ b ∈ R₃, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr₂ x
    exact ⟨a, le₃ ha, b, le₃ hb, e⟩
  have := isFractionRing_of_forall_div hfr₃
  have := isNoetherianRing_of_fg hR₃
  obtain ⟨lev', hlev⟩ := GlobalTheory.T.isLevelStructure_of_generic_of_fibrewise_indep hL R₃ Ω P' P φ₃ hG₃ eL₃ rfl M (Units.map (algebraMap o R₃).toMonoidHom ze) _
    (by simpa using hM.map (algebraMap o R₃)) rfl lev y' hy₃ (Hi R₃ g₃ (u₃ 4) _ _ y' q₃ hy')
  refine ⟨R₃, P', φ₃, lev', le₁.trans (le₂.trans le₃), hR₃, rfl, Hs R₃ g₃ (u₃ 3) _ _ _ q₃ hL₃ (lbIso_refl hL₃),
    hG₃, eL₃, ?_⟩
  rw [hlev]
  exact hy₃

end GlobalTheory.GenSpread
