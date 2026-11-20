import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerMemAdjoinJOfSlTwoIntInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaLeKer

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.LevelField

/- English proof (translation)
Use `letI : Algebra (IntermediateField.adjoin F {α}) (L.restrictScalars F) := inferInstanceAs (Algebra (IntermediateField.adjoin F {α}) L)`. Use `haveI : Module.Finite (IntermediateField.adjoin F {α}) (L.restrictScalars F) := hL`. Establish `hmap : (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}).map (L.restrictScalars F).val = IntermediateField.adjoin F {α}`. Rewrite using `[IntermediateField.adjoin_map, Set.image_singleton]`. Both sides reduce to the same expression.

Establish `hmem : ∀ c : IntermediateField.adjoin F {α}, algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F) c ∈ IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}`. Introduce `c`. Establish `hc : (c : K) ∈ (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}).map (L.restrictScalars F).val` using `by rw [hmap]; exact c.2`. Take `⟨y, hy, hyc⟩` from `(IntermediateField.mem_map _).1 hc`. Establish `e : algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F) c = y` using `Subtype.ext hyc.symm`.

Rewrite using `[e]`. Conclude with `hy`. Use `letI : Algebra (IntermediateField.adjoin F {α}) (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) := ((algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F)).codRestrict (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) hmem).toAlgebra`. Use `haveI : IsScalarTower (IntermediateField.adjoin F {α}) (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) (L.restrictScalars F) := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Conclude with `Module.Finite.of_restrictScalars_finite (IntermediateField.adjoin F {α}) _ _`.
-/
theorem finiteDimensional_adjoin_restrict {F K : Type} [Field F] [Field K] [Algebra F K] (α : K)
    (L : IntermediateField (IntermediateField.adjoin F {α}) K)
    (hL : FiniteDimensional (IntermediateField.adjoin F {α}) L) (hα : α ∈ L.restrictScalars F) :
    FiniteDimensional (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) (L.restrictScalars F) := by
  letI : Algebra (IntermediateField.adjoin F {α}) (L.restrictScalars F) :=
    inferInstanceAs (Algebra (IntermediateField.adjoin F {α}) L)
  haveI : Module.Finite (IntermediateField.adjoin F {α}) (L.restrictScalars F) := hL
  have hmap : (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}).map (L.restrictScalars F).val =
      IntermediateField.adjoin F {α} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ c : IntermediateField.adjoin F {α},
      algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F) c ∈
        IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)} := by
    intro c
    have hc : (c : K) ∈ (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}).map
        (L.restrictScalars F).val := by rw [hmap]; exact c.2
    obtain ⟨y, hy, hyc⟩ := (IntermediateField.mem_map _).1 hc
    have e : algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F) c = y := Subtype.ext hyc.symm
    rw [e]
    exact hy
  letI : Algebra (IntermediateField.adjoin F {α}) (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) :=
    ((algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F)).codRestrict
      (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) hmem).toAlgebra
  haveI : IsScalarTower (IntermediateField.adjoin F {α})
      (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) (L.restrictScalars F) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite (IntermediateField.adjoin F {α}) _ _

open GlobalTheory.FN.LevelGal in

/- English proof (translation)
Set `H` to `(rho X M).range`. Use `haveI : Finite H := finite_range X M hM`. Establish `hbot : IntermediateField.fixedField H = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`.

Rewrite `hx` using `[IntermediateField.mem_fixedField_iff]`. Establish `hxF : (x : X.K) ∈ IntermediateField.adjoin Ω {X.jK}`. Use `LevelOneFrac.mem_adjoin_of_sl_inv ε X hj x fun γ => ?_` and prove the remaining obligations. Establish `h1` using `congrArg Subtype.val (hx (rho X M γ⁻¹) ⟨γ⁻¹, rfl⟩)`. Rewrite `h1` using `[rho_val, inv_inv]`.

Conclude with `h1`. Rewrite using `[IntermediateField.mem_bot]`. Conclude with `⟨⟨x, hxF⟩, Subtype.ext rfl⟩`. Use `haveI hfd0 : FiniteDimensional (IntermediateField.fixedField H) (lvl X M) := (inferInstance : FiniteDimensional (FixedPoints.subfield H (lvl X M)) (lvl X M))`. Establish `: FiniteDimensional (⊥ : IntermediateField (IntermediateField.adjoin Ω {X.jK}) (lvl X M)) (lvl X M)` using `hbot ▸ hfd0`.

Conclude with `Module.Finite.trans (⊥ : IntermediateField (IntermediateField.adjoin Ω {X.jK}) (lvl X M)) (lvl X M)`.
-/
theorem finiteDimensional_lvl {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) (M : ℕ) (hM : 0 < M) :
    FiniteDimensional (IntermediateField.adjoin Ω {X.jK}) (lvl X M) := by
  let H := (rho X M).range
  haveI : Finite H := finite_range X M hM
  have hbot : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxF : (x : X.K) ∈ IntermediateField.adjoin Ω {X.jK} := by
      refine LevelOneFrac.mem_adjoin_of_sl_inv ε X hj x fun γ => ?_
      have h1 := congrArg Subtype.val (hx (rho X M γ⁻¹) ⟨γ⁻¹, rfl⟩)
      rw [rho_val, inv_inv] at h1
      exact h1
    rw [IntermediateField.mem_bot]
    exact ⟨⟨x, hxF⟩, Subtype.ext rfl⟩
  haveI hfd0 : FiniteDimensional (IntermediateField.fixedField H) (lvl X M) :=
    (inferInstance : FiniteDimensional (FixedPoints.subfield H (lvl X M)) (lvl X M))
  have : FiniteDimensional (⊥ : IntermediateField (IntermediateField.adjoin Ω {X.jK}) (lvl X M)) (lvl X M) :=
    hbot ▸ hfd0
  exact Module.Finite.trans (⊥ : IntermediateField (IntermediateField.adjoin Ω {X.jK}) (lvl X M)) (lvl X M)

/- English proof (translation)
Introduce `Ω _ _ _ ε X _ hj M hM`. Establish `hjL : X.jK ∈ (GlobalTheory.FN.LevelGal.lvl X M).restrictScalars Ω` using `fun γ _ => X.j_inv γ`. Conclude with `⟨(GlobalTheory.FN.LevelGal.lvl X M).restrictScalars Ω, fun f => Iff.rfl, hjL, finiteDimensional_adjoin_restrict X.jK _ (finiteDimensional_lvl ε X hj M hM) hjL⟩`.
-/
theorem exists_level_field : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M →
    ∃ L : IntermediateField Ω X.K, (∀ f : X.K, f ∈ L ↔ ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) ∧
      ∃ hj : X.jK ∈ L, FiniteDimensional (IntermediateField.adjoin Ω {(⟨X.jK, hj⟩ : L)}) L := by
  intro Ω _ _ _ ε X _ hj M hM
  have hjL : X.jK ∈ (GlobalTheory.FN.LevelGal.lvl X M).restrictScalars Ω := fun γ _ => X.j_inv γ
  exact ⟨(GlobalTheory.FN.LevelGal.lvl X M).restrictScalars Ω, fun f => Iff.rfl, hjL,
    finiteDimensional_adjoin_restrict X.jK _ (finiteDimensional_lvl ε X hj M hM) hjL⟩

end GlobalTheory.KZ.LevelField
