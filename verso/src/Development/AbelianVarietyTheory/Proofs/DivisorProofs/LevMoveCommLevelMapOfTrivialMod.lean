import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open OverMove in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c n d _ hLev hA2 hover ρ₂ ν₂ g gA _ hmv hg`. Establish `hL : Out.Laws` using `GlobalTheory.T.abelianScheme_laws_unconditional.1`. Take `⟨hd, hM, -, -, -, hE, -⟩` from `hLev`. Establish `hA : l.A = 1` using `Nat.eq_one_of_dvd_one (hA2 ▸ hd.2.2)`. Establish `hK : KA l ≤ KA d.l₂` using `by show IntermediateField.adjoin ℚ {H.rt0, zeta l.A} ≤ IntermediateField.adjoin ℚ {H.rt0, zeta d.l₂.A}`.

Rewrite using `[hA, hA2]`. Establish `hb` using `hover hK`. Establish `hred : IsReduced d.Xo₂.X` using `by haveI := d.Xo₂.smooth`. Conclude with `(isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ d.Xo₂.s (SmoothOfRelativeDimension.smooth Dw.dim _)).1`. Establish `hpd : d.pd = d.l₂.M / l.M`.

Rewrite using `[hM, Nat.mul_div_cancel_left _ (lt_of_lt_of_le (by norm_num) l.three_le)]`. Establish `L₁ : Lev d.m` using `⟨hpd ▸ hE.1, hE.2⟩`. Take `⟨o, ⟨p⟩⟩` from `obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (d.r ≫ Xo.s) d.r rfl rfl (by rw [LevelFibre.spMap_id', Category.comp_id]) Xo.univ`. Take `⟨u, hu, F₁⟩` from `exists_fib p L₁ (x := 𝟙 _) (Category.id_comp _)`. Take `⟨u₂, hu₂⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν₂ u`.

Establish `hA1 : ∀ a, d.Xo₂.univ.etaA a = 1` using `fun a => by`. Use `d.Xo₂.univ.etaA_ker a` as an intermediate fact. Rewrite `this` using `[hA2, one_smul]`. Then use the resulting hypothesis. Establish `hfix : ∀ a, (d.Xo₂.univ.eta (g a) ^ (d.l₂.M / l.M)).left = (d.Xo₂.univ.eta a ^ (d.l₂.M / l.M)).left` using `fun a => by`. Apply `d.m.cart.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[L₁.1, L₁.1, LevelActionLaws.eta_congr Xo (hg a)]`. Rewrite using `[LevelFibre.sec_w, LevelFibre.sec_w]`. Establish `hone : (1 : 𝟙_ (Over d.Xo₂.X) ⟶ d.Xo₂.univ.t.G).left ≫ ν₂.φ = ρ₂ ≫ (1 : 𝟙_ (Over d.Xo₂.X) ⟶ d.Xo₂.univ.t.G).left`. Use `hmv.2.2 0` as an intermediate fact. Rewrite `this` using `[hA1, hA1]`. Then use the resulting hypothesis.

Establish `F₂ : Fib o u₂`. Use `⟨fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hu₂, ← Category.assoc, F₁.1, Category.id_comp, ← hfix, pow_left_comp ν₂ (hmv.2.1 a), Category.id_comp, hfix]`. Rewrite using `[hu₂, ← Category.assoc, F₁.2, Category.id_comp, Category.id_comp, hA1, one_pow]`. Conclude with `hone`.

Take `⟨q, hq⟩` from `exists_objMap F₂ L₁`. Establish `hr : (𝟙 _ ≫ ρ₂) ≫ d.r = d.r`. Use `(Xo.rep d.Xo₂.X (d.r ≫ Xo.s) hred o).unique ⟨?_, ⟨q⟩⟩ ⟨rfl, ⟨p⟩⟩` and prove the remaining obligations. Rewrite using `[Category.id_comp, Category.assoc, hb, ← Category.assoc, hmv.1]`. Take `⟨q', hq'⟩` from `LevelFibre.sab_cast hr q.toSABMap`.

Establish `e : p.toSABMap.φ = q'.φ` using `sabMap_eq_of_level_eq hL obj_isAbelianScheme_dim_rigidified_sym E H Dw l _ _ _ _ _ _ _ _ Xo.univ o _ (Or.inl hred) p.toSABMap q' fun a => ⟨_, p.eta a, by rw [hq']; exact (q.eta a).trans (by rw [hr])⟩`. Rewrite `e` using `[hq', hq, ← hu, hu₂, Category.assoc]`. Establish `: IsIso u.φ` using `u.cart.1.isIso_fst_of_isIso`. Use `⟨by simpa using hr, ((cancel_epi u.φ).1 e).symm⟩` and prove the remaining obligations.
-/
theorem levMove_comm_levelMap_of_trivial_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (g gA : Dw.La →ₗ[𝓞 E] Dw.La), IsIso ρ₂ → IsLevMove ρ₂ ν₂ g gA → (∀ a, g a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ρ₂ ≫ d.r = d.r ∧ ν₂.φ ≫ d.m.φ = d.m.φ := by
  intro E _ _ _ H Dw l Xo c n d _ hLev hA2 hover ρ₂ ν₂ g gA _ hmv hg
  have hL : Out.Laws := GlobalTheory.T.abelianScheme_laws_unconditional.1
  obtain ⟨hd, hM, -, -, -, hE, -⟩ := hLev
  have hA : l.A = 1 := Nat.eq_one_of_dvd_one (hA2 ▸ hd.2.2)
  have hK : KA l ≤ KA d.l₂ := by
    show IntermediateField.adjoin ℚ {H.rt0, zeta l.A} ≤ IntermediateField.adjoin ℚ {H.rt0, zeta d.l₂.A}
    rw [hA, hA2]
  have hb := hover hK
  have hred : IsReduced d.Xo₂.X := by
    haveI := d.Xo₂.smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ d.Xo₂.s
      (SmoothOfRelativeDimension.smooth Dw.dim _)).1
  have hpd : d.pd = d.l₂.M / l.M := by
    rw [hM, Nat.mul_div_cancel_left _ (lt_of_lt_of_le (by norm_num) l.three_le)]
  have L₁ : Lev d.m := ⟨hpd ▸ hE.1, hE.2⟩
  obtain ⟨o, ⟨p⟩⟩ := obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (d.r ≫ Xo.s) d.r rfl rfl
    (by rw [LevelFibre.spMap_id', Category.comp_id]) Xo.univ
  obtain ⟨u, hu, F₁⟩ := exists_fib p L₁ (x := 𝟙 _) (Category.id_comp _)
  obtain ⟨u₂, hu₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν₂ u
  have hA1 : ∀ a, d.Xo₂.univ.etaA a = 1 := fun a => by
    have := d.Xo₂.univ.etaA_ker a
    rwa [hA2, one_smul] at this
  have hfix : ∀ a, (d.Xo₂.univ.eta (g a) ^ (d.l₂.M / l.M)).left = (d.Xo₂.univ.eta a ^ (d.l₂.M / l.M)).left :=
    fun a => by
      apply d.m.cart.1.hom_ext
      · rw [L₁.1, L₁.1, LevelActionLaws.eta_congr Xo (hg a)]
      · rw [LevelFibre.sec_w, LevelFibre.sec_w]
  have hone : (1 : 𝟙_ (Over d.Xo₂.X) ⟶ d.Xo₂.univ.t.G).left ≫ ν₂.φ = ρ₂ ≫ (1 : 𝟙_ (Over d.Xo₂.X) ⟶ d.Xo₂.univ.t.G).left := by
    have := hmv.2.2 0
    rwa [hA1, hA1] at this
  have F₂ : Fib o u₂ := by
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hu₂, ← Category.assoc, F₁.1, Category.id_comp, ← hfix, pow_left_comp ν₂ (hmv.2.1 a), Category.id_comp, hfix]
    · rw [hu₂, ← Category.assoc, F₁.2, Category.id_comp, Category.id_comp, hA1, one_pow]
      exact hone
  obtain ⟨q, hq⟩ := exists_objMap F₂ L₁
  have hr : (𝟙 _ ≫ ρ₂) ≫ d.r = d.r := by
    refine (Xo.rep d.Xo₂.X (d.r ≫ Xo.s) hred o).unique ⟨?_, ⟨q⟩⟩ ⟨rfl, ⟨p⟩⟩
    rw [Category.id_comp, Category.assoc, hb, ← Category.assoc, hmv.1]
  obtain ⟨q', hq'⟩ := LevelFibre.sab_cast hr q.toSABMap
  have e : p.toSABMap.φ = q'.φ := sabMap_eq_of_level_eq hL obj_isAbelianScheme_dim_rigidified_sym E H Dw l _ _ _ _ _ _
    _ _ Xo.univ o _ (Or.inl hred) p.toSABMap q' fun a => ⟨_, p.eta a, by rw [hq']; exact (q.eta a).trans (by rw [hr])⟩
  rw [hq', hq, ← hu, hu₂, Category.assoc] at e
  have : IsIso u.φ := u.cart.1.isIso_fst_of_isIso
  refine ⟨by simpa using hr, ((cancel_epi u.φ).1 e).symm⟩

end GlobalTheory
