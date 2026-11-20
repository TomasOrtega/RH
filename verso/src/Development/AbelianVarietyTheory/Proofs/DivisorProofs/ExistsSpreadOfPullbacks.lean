import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayInjectiveAtPrimeOfDvdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsetMemRangeLocalizationAwayOfDvdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayRangeLeOfDvdOfCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackSpreadsToIntermediateSubringStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelSpreadLocal

/- English proof (translation)
Introduce `g n B _ ζ R _ _ β 𝔭 _ d Y sY _ u r₀ ι₀ h e hr₀ hι₀ hh hed heu`. Take `⟨t₁, ht₁, hinj⟩` from `GlobalTheory.T.localization_away_injective_atPrime_of_dvd R 𝔭`. Establish `hrange` using `GlobalTheory.T.finset_mem_range_localization_away_of_dvd R 𝔭`. Establish `hmono` using `GlobalTheory.T.localization_away_range_le_of_dvd_of_comp R (Localization.AtPrime 𝔭) (algebraMap R (Localization.AtPrime 𝔭))`. Establish `spc : ∀ {A₁ A₂ A₃ : Type} [CommRing A₁] [CommRing A₂] [CommRing A₃] (a : A₁ →+* A₂) (b : A₂ →+* A₃), spMap (b.comp a) = spMap b ≫ spMap a`.

Introduce `A₁ A₂ A₃ _ _ _ a b`. Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression. Establish `unit : ∀ x : R, x ∉ 𝔭 → IsUnit (algebraMap R (Localization.AtPrime 𝔭) x)` using `fun x hx => IsLocalization.map_units (M := 𝔭.primeCompl) (Localization.AtPrime 𝔭) ⟨x, hx⟩`. Establish `nmul : ∀ x y : R, x ∉ 𝔭 → y ∉ 𝔭 → x * y ∉ 𝔭` using `fun x y hx hy hm => ((inferInstance : 𝔭.IsPrime).mem_or_mem hm).elim hx hy`.

Set `lam : ∀ c : R, c ∉ 𝔭 → Localization.Away c →+* Localization.AtPrime 𝔭` to `fun c hc => IsLocalization.Away.lift c (unit c hc)`. Establish `lamc : ∀ (c : R) (hc : c ∉ 𝔭), (lam c hc).comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭)` using `fun c hc => IsLocalization.Away.lift_comp _ _`. Establish `ht : r₀ * t₁ ∉ 𝔭` using `nmul _ _ hr₀ ht₁`. Set `R₀ : Subring (Localization.AtPrime 𝔭)` to `(lam _ ht).range`. Establish `memR₀ : ∀ x : R, algebraMap R (Localization.AtPrime 𝔭) x ∈ R₀` using `fun x => ⟨algebraMap R _ x, by rw [← RingHom.comp_apply, lamc _ ht]⟩`.

Set `a₀ : R →+* R₀` to `(algebraMap R (Localization.AtPrime 𝔭)).codRestrict R₀ memR₀`. Take `⟨⟨d₀, hd₀⟩, -⟩` from `GlobalTheory.siegPre_pullback g n B ζ (Sp R) (Sp R₀) (spMap β) (spMap a₀ ≫ spMap β) (spMap a₀) d rfl`. Establish `hsub : R₀.subtype.comp a₀ = algebraMap R (Localization.AtPrime 𝔭)` using `RingHom.ext fun _ => rfl`. Establish `hed₀ : SiegPB e d₀ (spMap R₀.subtype)` using `GlobalTheory.SiegelPullComp.pb_cancel hd₀ (by rw [← spc, hsub]; exact hed)`. Establish `memι₀ : ∀ x, ι₀ x ∈ R₀` using `fun x => hmono r₀ (r₀ * t₁) (dvd_mul_right _ _) ι₀ (lam _ ht) hι₀ (lamc _ ht) ⟨x, rfl⟩`.

Set `j₀ : Localization.Away r₀ →+* R₀` to `ι₀.codRestrict R₀ memι₀`. Establish `hj₀ : R₀.subtype.comp j₀ = ι₀` using `RingHom.ext fun _ => rfl`. Establish `heu₀ : SiegPB e u (spMap R₀.subtype ≫ (spMap j₀ ≫ h))`. Rewrite using `[← Category.assoc, ← spc, hj₀]`. Conclude with `heu`.

Take `⟨F, hF⟩` from `GlobalTheory.T.siegelPullback_spreads_to_intermediate_subring g n B ζ (Localization.AtPrime 𝔭) R₀ _ d₀ Y sY u (spMap j₀ ≫ h) _ e hed₀ heu₀`. Take `⟨s, hs, hsF⟩` from `hrange F`. Establish `hr : r₀ * t₁ * s ∉ 𝔭` using `nmul _ _ ht hs`. Set `lr` to `lam _ hr`. Set `R₁ : Subring (Localization.AtPrime 𝔭)` to `lr.range`.

Establish `hle : R₀ ≤ R₁` using `hmono _ _ (dvd_mul_right _ _) _ _ (lamc _ ht) (lamc _ hr)`. Establish `hFR : (F : Set (Localization.AtPrime 𝔭)) ⊆ R₁` using `fun x hx => hsF _ (dvd_mul_left _ _) lr (lamc _ hr) x hx`. Establish `hlinj : Function.Injective lr` using `hinj _ ⟨r₀ * s, by ring⟩ lr (lamc _ hr)`. Set `er : Localization.Away (r₀ * t₁ * s) ≃+* R₁` to `RingEquiv.ofBijective lr.rangeRestrict ⟨fun x y hxy => hlinj (congrArg Subtype.val hxy), lr.rangeRestrict_surjective⟩`. Establish `erv : ∀ x, (er x : Localization.AtPrime 𝔭) = lr x` using `fun _ => rfl`.

Take `⟨⟨d', hd'⟩, -⟩` from `GlobalTheory.siegPre_pullback g n B ζ (Sp R) (Sp (Localization.Away (r₀ * t₁ * s))) (spMap β) (spMap ((algebraMap R (Localization.Away (r₀ * t₁ * s))).comp β)) (spMap (algebraMap R (Localization.Away (r₀ * t₁ * s)))) d (spc _ _).symm`. Take `⟨⟨d₁, hd₁⟩, -⟩` from `GlobalTheory.siegPre_pullback g n B ζ _ (Sp R₁) _ _ (spMap er.toRingHom) d' rfl`. Establish `hd₁₀ : SiegPB d₁ d₀ (spMap (Subring.inclusion hle))`. Use `GlobalTheory.SiegelPullComp.pb_cancel hd₀ ?_` and prove the remaining obligations. Establish `e₁ : spMap (Subring.inclusion hle) ≫ spMap a₀ = spMap er.toRingHom ≫ spMap (algebraMap R (Localization.Away (r₀ * t₁ * s)))`.

Rewrite using `[← spc, ← spc]`. Use `congr 1`. Use `RingHom.ext fun x => Subtype.ext ?_` and prove the remaining obligations. Use `show algebraMap R (Localization.AtPrime 𝔭) x = lr (algebraMap R _ x)`. Rewrite using `[← RingHom.comp_apply, lamc _ hr]`.

Rewrite using `[e₁]`. Conclude with `GlobalTheory.SiegelPullComp.pb_comp hd' hd₁`. Establish `hd₁u` using `hF R₁ hle hFR _ d₁ hd₁₀`. Establish `hd'd₁ : SiegPB d' d₁ (spMap er.symm.toRingHom)`. Use `GlobalTheory.SiegelPullComp.pb_cancel hd₁ ?_` and prove the remaining obligations.

Establish `e₂ : spMap er.symm.toRingHom ≫ spMap er.toRingHom = 𝟙 _`. Rewrite using `[← spc]`. Establish `: er.symm.toRingHom.comp er.toRingHom = RingHom.id _` using `RingHom.ext fun x => er.symm_apply_apply x`. Rewrite using `[this]`. Simplify using `[spMap]`.

Rewrite using `[e₂]`. Conclude with `GlobalTheory.SiegelPullComp.pb_id d'`. Set `κ : Localization.Away r₀ →+* Localization.Away (r₀ * t₁ * s)` to `er.symm.toRingHom.comp ((Subring.inclusion hle).comp j₀)`. Use `⟨r₀ * t₁ * s, hr, κ, d', ?_, hd', ?_⟩` and prove the remaining obligations. Use `RingHom.ext fun x => hlinj ?_` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply, RingHom.comp_apply]`. Establish `hk : er (κ (algebraMap R _ x)) = (Subring.inclusion hle) (j₀ (algebraMap R _ x))` using `er.apply_symm_apply _`. Combine the equalities or inequalities in the displayed calculation. Establish `e₃ : spMap κ ≫ h = spMap er.symm.toRingHom ≫ (spMap (Subring.inclusion hle) ≫ (spMap j₀ ≫ h))`. Simplify using `only [κ, spc, Category.assoc]`.

Rewrite using `[e₃]`. Conclude with `GlobalTheory.SiegelPullComp.pb_comp hd₁u hd'd₁`.
-/
theorem exists_spread_of_pullbacks : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (d : SiegPre g n ζ (spMap β)) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) [LocallyOfFinitePresentation sY] (u : SiegPre g n ζ sY) (r₀ : R) (ι₀ : Localization.Away r₀ →+* Localization.AtPrime 𝔭) (h : Sp (Localization.Away r₀) ⟶ Y) (e : SiegPre g n ζ (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))), r₀ ∉ 𝔭 → ι₀.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.AtPrime 𝔭) → h ≫ sY = spMap ((algebraMap R (Localization.Away r₀)).comp β) → SiegPB e d (spMap (algebraMap R (Localization.AtPrime 𝔭))) → SiegPB e u (spMap ι₀ ≫ h) → ∃ r ∉ 𝔭, ∃ (κ : Localization.Away r₀ →+* Localization.Away r) (d' : SiegPre g n ζ (spMap ((algebraMap R (Localization.Away r)).comp β))), κ.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.Away r) ∧ SiegPB d' d (spMap (algebraMap R (Localization.Away r))) ∧ SiegPB d' u (spMap κ ≫ h) := by
  intro g n B _ ζ R _ _ β 𝔭 _ d Y sY _ u r₀ ι₀ h e hr₀ hι₀ hh hed heu
  obtain ⟨t₁, ht₁, hinj⟩ := GlobalTheory.T.localization_away_injective_atPrime_of_dvd R 𝔭
  have hrange := GlobalTheory.T.finset_mem_range_localization_away_of_dvd R 𝔭
  have hmono := GlobalTheory.T.localization_away_range_le_of_dvd_of_comp R (Localization.AtPrime 𝔭) (algebraMap R (Localization.AtPrime 𝔭))
  have spc : ∀ {A₁ A₂ A₃ : Type} [CommRing A₁] [CommRing A₂] [CommRing A₃] (a : A₁ →+* A₂) (b : A₂ →+* A₃),
      spMap (b.comp a) = spMap b ≫ spMap a := by
    intro A₁ A₂ A₃ _ _ _ a b
    simp only [spMap, ← Spec.map_comp]
    rfl
  have unit : ∀ x : R, x ∉ 𝔭 → IsUnit (algebraMap R (Localization.AtPrime 𝔭) x) := fun x hx =>
    IsLocalization.map_units (M := 𝔭.primeCompl) (Localization.AtPrime 𝔭) ⟨x, hx⟩
  have nmul : ∀ x y : R, x ∉ 𝔭 → y ∉ 𝔭 → x * y ∉ 𝔭 := fun x y hx hy hm =>
    ((inferInstance : 𝔭.IsPrime).mem_or_mem hm).elim hx hy
  let lam : ∀ c : R, c ∉ 𝔭 → Localization.Away c →+* Localization.AtPrime 𝔭 := fun c hc =>
    IsLocalization.Away.lift c (unit c hc)
  have lamc : ∀ (c : R) (hc : c ∉ 𝔭), (lam c hc).comp (algebraMap R (Localization.Away c)) =
      algebraMap R (Localization.AtPrime 𝔭) := fun c hc => IsLocalization.Away.lift_comp _ _

  have ht : r₀ * t₁ ∉ 𝔭 := nmul _ _ hr₀ ht₁
  let R₀ : Subring (Localization.AtPrime 𝔭) := (lam _ ht).range
  have memR₀ : ∀ x : R, algebraMap R (Localization.AtPrime 𝔭) x ∈ R₀ := fun x =>
    ⟨algebraMap R _ x, by rw [← RingHom.comp_apply, lamc _ ht]⟩
  let a₀ : R →+* R₀ := (algebraMap R (Localization.AtPrime 𝔭)).codRestrict R₀ memR₀
  obtain ⟨⟨d₀, hd₀⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R) (Sp R₀) (spMap β) (spMap a₀ ≫ spMap β)
    (spMap a₀) d rfl
  have hsub : R₀.subtype.comp a₀ = algebraMap R (Localization.AtPrime 𝔭) := RingHom.ext fun _ => rfl
  have hed₀ : SiegPB e d₀ (spMap R₀.subtype) :=
    GlobalTheory.SiegelPullComp.pb_cancel hd₀ (by rw [← spc, hsub]; exact hed)
  have memι₀ : ∀ x, ι₀ x ∈ R₀ := fun x =>
    hmono r₀ (r₀ * t₁) (dvd_mul_right _ _) ι₀ (lam _ ht) hι₀ (lamc _ ht) ⟨x, rfl⟩
  let j₀ : Localization.Away r₀ →+* R₀ := ι₀.codRestrict R₀ memι₀
  have hj₀ : R₀.subtype.comp j₀ = ι₀ := RingHom.ext fun _ => rfl
  have heu₀ : SiegPB e u (spMap R₀.subtype ≫ (spMap j₀ ≫ h)) := by
    rw [← Category.assoc, ← spc, hj₀]; exact heu
  obtain ⟨F, hF⟩ := GlobalTheory.T.siegelPullback_spreads_to_intermediate_subring g n B ζ (Localization.AtPrime 𝔭) R₀ _ d₀ Y sY u (spMap j₀ ≫ h) _ e hed₀ heu₀
  obtain ⟨s, hs, hsF⟩ := hrange F

  have hr : r₀ * t₁ * s ∉ 𝔭 := nmul _ _ ht hs
  let lr := lam _ hr
  let R₁ : Subring (Localization.AtPrime 𝔭) := lr.range
  have hle : R₀ ≤ R₁ := hmono _ _ (dvd_mul_right _ _) _ _ (lamc _ ht) (lamc _ hr)
  have hFR : (F : Set (Localization.AtPrime 𝔭)) ⊆ R₁ := fun x hx =>
    hsF _ (dvd_mul_left _ _) lr (lamc _ hr) x hx
  have hlinj : Function.Injective lr :=
    hinj _ ⟨r₀ * s, by ring⟩ lr (lamc _ hr)
  let er : Localization.Away (r₀ * t₁ * s) ≃+* R₁ :=
    RingEquiv.ofBijective lr.rangeRestrict ⟨fun x y hxy => hlinj (congrArg Subtype.val hxy), lr.rangeRestrict_surjective⟩
  have erv : ∀ x, (er x : Localization.AtPrime 𝔭) = lr x := fun _ => rfl
  obtain ⟨⟨d', hd'⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R) (Sp (Localization.Away (r₀ * t₁ * s)))
    (spMap β) (spMap ((algebraMap R (Localization.Away (r₀ * t₁ * s))).comp β))
    (spMap (algebraMap R (Localization.Away (r₀ * t₁ * s)))) d (spc _ _).symm
  obtain ⟨⟨d₁, hd₁⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ _ (Sp R₁) _ _ (spMap er.toRingHom) d' rfl
  have hd₁₀ : SiegPB d₁ d₀ (spMap (Subring.inclusion hle)) := by
    refine GlobalTheory.SiegelPullComp.pb_cancel hd₀ ?_
    have e₁ : spMap (Subring.inclusion hle) ≫ spMap a₀ = spMap er.toRingHom ≫ spMap (algebraMap R (Localization.Away (r₀ * t₁ * s))) := by
      rw [← spc, ← spc]
      congr 1
      refine RingHom.ext fun x => Subtype.ext ?_
      show algebraMap R (Localization.AtPrime 𝔭) x = lr (algebraMap R _ x)
      rw [← RingHom.comp_apply, lamc _ hr]
    rw [e₁]
    exact GlobalTheory.SiegelPullComp.pb_comp hd' hd₁
  have hd₁u := hF R₁ hle hFR _ d₁ hd₁₀
  have hd'd₁ : SiegPB d' d₁ (spMap er.symm.toRingHom) := by
    refine GlobalTheory.SiegelPullComp.pb_cancel hd₁ ?_
    have e₂ : spMap er.symm.toRingHom ≫ spMap er.toRingHom = 𝟙 _ := by
      rw [← spc]
      have : er.symm.toRingHom.comp er.toRingHom = RingHom.id _ := RingHom.ext fun x => er.symm_apply_apply x
      rw [this]
      simp [spMap]
    rw [e₂]
    exact GlobalTheory.SiegelPullComp.pb_id d'
  let κ : Localization.Away r₀ →+* Localization.Away (r₀ * t₁ * s) :=
    er.symm.toRingHom.comp ((Subring.inclusion hle).comp j₀)
  refine ⟨r₀ * t₁ * s, hr, κ, d', ?_, hd', ?_⟩
  · refine RingHom.ext fun x => hlinj ?_
    rw [RingHom.comp_apply, RingHom.comp_apply]
    have hk : er (κ (algebraMap R _ x)) = (Subring.inclusion hle) (j₀ (algebraMap R _ x)) := er.apply_symm_apply _
    calc lr (κ (algebraMap R _ x)) = (er (κ (algebraMap R _ x)) : Localization.AtPrime 𝔭) := rfl
      _ = ((Subring.inclusion hle) (j₀ (algebraMap R _ x)) : Localization.AtPrime 𝔭) := congrArg Subtype.val hk
      _ = ι₀ (algebraMap R _ x) := rfl
      _ = algebraMap R (Localization.AtPrime 𝔭) x := by rw [← RingHom.comp_apply, hι₀]
      _ = lr (algebraMap R _ x) := by rw [← RingHom.comp_apply, lamc _ hr]
  · have e₃ : spMap κ ≫ h = spMap er.symm.toRingHom ≫ (spMap (Subring.inclusion hle) ≫ (spMap j₀ ≫ h)) := by
      simp only [κ, spc, Category.assoc]
    rw [e₃]
    exact GlobalTheory.SiegelPullComp.pb_comp hd₁u hd'd₁

end GlobalTheory.SiegelSpreadLocal
