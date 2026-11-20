import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvenOrderNormsOneAddFourMulOfNoRootStatement

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Establish `: v.asIdeal.IsMaximal` using `v.isMaximal`. Set `f : 𝓞 F ⧸ v.asIdeal → 𝓞 F ⧸ v.asIdeal` to `fun x => x ^ 2 + x`. Establish `hni : ¬ Function.Injective f`. Introduce `h`. Establish `h0 : (0 : 𝓞 F ⧸ v.asIdeal) = -1` using `h (by simp [f])`.

Conclude with `one_ne_zero (neg_eq_zero.mp h0.symm)`. Establish `hns : ¬ Function.Surjective f` using `fun hs => hni (Finite.injective_iff_surjective.mpr hs)`. Simplify using `only [Function.Surjective, not_forall, not_exists] at hns`. Take `⟨r, hr⟩` from `hns`. Take `⟨ρ, rfl⟩` from `Ideal.Quotient.mk_surjective r`.

Use `⟨ρ, fun a ha => hr (Ideal.Quotient.mk _ a) ?_⟩` and prove the remaining obligations. Establish `h` using `(Ideal.Quotient.eq_zero_iff_mem).mpr ha`. Simplify using `only [map_sub, map_add, map_pow] at h`. Conclude with `sub_eq_zero.mp h`.
-/
theorem exists_not_mem_sq_add_sub (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ρ : 𝓞 F, ∀ a : 𝓞 F, a ^ 2 + a - ρ ∉ v.asIdeal := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  let f : 𝓞 F ⧸ v.asIdeal → 𝓞 F ⧸ v.asIdeal := fun x => x ^ 2 + x
  have hni : ¬ Function.Injective f := by
    intro h
    have h0 : (0 : 𝓞 F ⧸ v.asIdeal) = -1 := h (by simp [f])
    exact one_ne_zero (neg_eq_zero.mp h0.symm)
  have hns : ¬ Function.Surjective f := fun hs => hni (Finite.injective_iff_surjective.mpr hs)
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨r, hr⟩ := hns
  obtain ⟨ρ, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨ρ, fun a ha => hr (Ideal.Quotient.mk _ a) ?_⟩
  have h := (Ideal.Quotient.eq_zero_iff_mem).mpr ha
  simp only [map_sub, map_add, map_pow] at h
  exact sub_eq_zero.mp h

/- English proof (translation)
Introduce `F _ _ v`. Take `⟨_, hval, hrep, -⟩` from `GlobalTheory.T.exists_global_uniformizer_residue_representatives F v`. Take `⟨ρ, hρ⟩` from `exists_not_mem_sq_add_sub F v`. Use `set r : v.adicCompletion F := algebraMap F (v.adicCompletion F) (ρ : F) with hr`. Establish `h2 : (2 : v.adicCompletion F) ≠ 0`.

Establish `h` using `(map_ne_zero (algebraMap F (v.adicCompletion F))).mpr (two_ne_zero (α := F))`. Rewrite `h` using `[map_ofNat]`. Then use the resulting hypothesis. Establish `hint : ∀ a : 𝓞 F, Valued.v (algebraMap F (v.adicCompletion F) (a : F)) ≤ 1` using `fun a => by`. Rewrite using `[hval]`. Conclude with `v.valuation_le_one a`.

Establish `hone : ∀ a : 𝓞 F, a ∉ v.asIdeal → Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1` using `fun a ha => by`. Rewrite using `[hval]`. Conclude with `v.valuation_eq_one_iff_notMem.mpr ha`. Establish `key : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → Valued.v (x ^ 2 + x - r) = 1`. Introduce `x hx`.

Take `⟨a, ha⟩` from `hrep x hx`. Use `set b : v.adicCompletion F := algebraMap F (v.adicCompletion F) (a : F) with hb_def`. Establish `hb : Valued.v b ≤ 1` using `hint a`. Establish `hab : Valued.v (b ^ 2 + b - r) = 1`. Establish `h` using `hone (a ^ 2 + a - ρ) (hρ a)`.

Move the coercions through the operations in `at h`. Simplify `h` using `[hb_def, hr]`. Establish `h3 : Valued.v (x + b + 1) ≤ 1` using `Valuation.map_add_le _ (Valuation.map_add_le _ hx hb) (by simp)`. Establish `hsmall : Valued.v ((x - b) * (x + b + 1)) < Valued.v (b ^ 2 + b - r)`. Rewrite using `[hab, map_mul]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' h3) ha`. Establish `e : x ^ 2 + x - r = (x - b) * (x + b + 1) + (b ^ 2 + b - r)` using `by ring`. Rewrite using `[e, Valuation.map_add_eq_of_lt_right _ hsmall, hab]`. Use `⟨1 + 4 * r, GlobalTheory.T.evenOrderNorms_one_add_four_mul_of_no_root _ Valued.v r h2 (hint ρ) key, ?_, ?_⟩` and prove the remaining obligations. Establish `h2le : Valued.v (2 : v.adicCompletion F) ≤ 1`.

Rewrite using `[← one_add_one_eq_two]`. Conclude with `Valuation.map_add_le _ (by simp) (by simp)`. Establish `h4 : (4 : v.adicCompletion F) = 2 * 2` using `by norm_num`. Distinguish the cases in `h2v : Valued.v (2 : v.adicCompletion F) = 1`. Establish `hx : Valued.v (-(2 : v.adicCompletion F)⁻¹) = 1`.

Rewrite using `[Valuation.map_neg, map_inv₀, h2v, inv_one]`. Establish `hk` using `key (-(2 : v.adicCompletion F)⁻¹) hx.le`. Establish `h22 : (2 : v.adicCompletion F) * 2⁻¹ = 1` using `mul_inv_cancel₀ h2`. Establish `e : 1 + 4 * r = -(2 * 2) * ((-(2 : v.adicCompletion F)⁻¹) ^ 2 + (-(2 : v.adicCompletion F)⁻¹) - r)`. Take the linear combination `(2 * (2 : v.adicCompletion F)⁻¹ - 1) * h22`.

Rewrite using `[e, map_mul, hk, mul_one, Valuation.map_neg, map_mul, h2v, mul_one]`. Establish `h2lt : Valued.v (2 : v.adicCompletion F) < 1` using `lt_of_le_of_ne h2le h2v`. Establish `h4r : Valued.v (4 * r) < Valued.v (1 : v.adicCompletion F)`. Rewrite using `[map_one, map_mul, h4, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (hint ρ)) (lt_of_le_of_lt (mul_le_of_le_one_right' h2le) h2lt)`.

Rewrite using `[Valuation.map_add_eq_of_lt_left _ h4r, map_one]`. Rewrite using `[add_sub_cancel_left, map_mul]`. Conclude with `mul_le_of_le_one_right' (hint ρ)`.
-/
theorem exists_evenNorms_unit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), ∃ Δ : v.adicCompletion F, EvenNorms Valued.v Δ ∧ Valued.v Δ = 1 ∧ Valued.v (Δ - 1) ≤ Valued.v (4 : v.adicCompletion F) := by
  intro F _ _ v
  obtain ⟨_, hval, hrep, -⟩ := GlobalTheory.T.exists_global_uniformizer_residue_representatives F v
  obtain ⟨ρ, hρ⟩ := exists_not_mem_sq_add_sub F v
  set r : v.adicCompletion F := algebraMap F (v.adicCompletion F) (ρ : F) with hr
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    have h := (map_ne_zero (algebraMap F (v.adicCompletion F))).mpr (two_ne_zero (α := F))
    rwa [map_ofNat] at h
  have hint : ∀ a : 𝓞 F, Valued.v (algebraMap F (v.adicCompletion F) (a : F)) ≤ 1 := fun a => by
    rw [hval]; exact v.valuation_le_one a
  have hone : ∀ a : 𝓞 F, a ∉ v.asIdeal →
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 := fun a ha => by
    rw [hval]; exact v.valuation_eq_one_iff_notMem.mpr ha
  have key : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → Valued.v (x ^ 2 + x - r) = 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := hrep x hx
    set b : v.adicCompletion F := algebraMap F (v.adicCompletion F) (a : F) with hb_def
    have hb : Valued.v b ≤ 1 := hint a
    have hab : Valued.v (b ^ 2 + b - r) = 1 := by
      have h := hone (a ^ 2 + a - ρ) (hρ a)
      push_cast at h
      simpa [hb_def, hr] using h
    have h3 : Valued.v (x + b + 1) ≤ 1 :=
      Valuation.map_add_le _ (Valuation.map_add_le _ hx hb) (by simp)
    have hsmall : Valued.v ((x - b) * (x + b + 1)) < Valued.v (b ^ 2 + b - r) := by
      rw [hab, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' h3) ha
    have e : x ^ 2 + x - r = (x - b) * (x + b + 1) + (b ^ 2 + b - r) := by ring
    rw [e, Valuation.map_add_eq_of_lt_right _ hsmall, hab]
  refine ⟨1 + 4 * r, GlobalTheory.T.evenOrderNorms_one_add_four_mul_of_no_root _ Valued.v r h2 (hint ρ) key, ?_, ?_⟩
  · have h2le : Valued.v (2 : v.adicCompletion F) ≤ 1 := by
      rw [← one_add_one_eq_two]
      exact Valuation.map_add_le _ (by simp) (by simp)
    have h4 : (4 : v.adicCompletion F) = 2 * 2 := by norm_num
    by_cases h2v : Valued.v (2 : v.adicCompletion F) = 1
    · have hx : Valued.v (-(2 : v.adicCompletion F)⁻¹) = 1 := by
        rw [Valuation.map_neg, map_inv₀, h2v, inv_one]
      have hk := key (-(2 : v.adicCompletion F)⁻¹) hx.le
      have h22 : (2 : v.adicCompletion F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
      have e : 1 + 4 * r = -(2 * 2) *
          ((-(2 : v.adicCompletion F)⁻¹) ^ 2 + (-(2 : v.adicCompletion F)⁻¹) - r) := by
        linear_combination (2 * (2 : v.adicCompletion F)⁻¹ - 1) * h22
      rw [e, map_mul, hk, mul_one, Valuation.map_neg, map_mul, h2v, mul_one]
    · have h2lt : Valued.v (2 : v.adicCompletion F) < 1 := lt_of_le_of_ne h2le h2v
      have h4r : Valued.v (4 * r) < Valued.v (1 : v.adicCompletion F) := by
        rw [map_one, map_mul, h4, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint ρ))
          (lt_of_le_of_lt (mul_le_of_le_one_right' h2le) h2lt)
      rw [Valuation.map_add_eq_of_lt_left _ h4r, map_one]
  · rw [add_sub_cancel_left, map_mul]
    exact mul_le_of_le_one_right' (hint ρ)

end GlobalTheory.QNorm
