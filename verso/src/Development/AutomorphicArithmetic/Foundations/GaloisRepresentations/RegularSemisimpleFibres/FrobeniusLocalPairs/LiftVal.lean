import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjOfIsConjGlFieldExtensionInclusion

open ValuativeRel Matrix Polynomial GlobalTheory.DZA GlobalTheory.LBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

/- English proof (translation)
Establish `h1 : Nat.card (⊤ : Subgroup (K ≃ₐ[k] K)) ∣ Module.finrank k K`. Rewrite using `[← IntermediateField.finrank_fixedField_eq_card, ← Module.finrank_mul_finrank k (IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[k] K))) K]`. Conclude with `dvd_mul_left _ _`. Rewrite `h1` using `[Subgroup.card_top]`. Conclude with `orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard s).trans h1)`.
-/
private theorem pow_finrank_aut {k K : Type} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    (s : K ≃ₐ[k] K) : s ^ Module.finrank k K = 1 := by
  classical
  have h1 : Nat.card (⊤ : Subgroup (K ≃ₐ[k] K)) ∣ Module.finrank k K := by
    rw [← IntermediateField.finrank_fixedField_eq_card,
      ← Module.finrank_mul_finrank k (IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[k] K))) K]
    exact dvd_mul_left _ _
  rw [Subgroup.card_top] at h1
  exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard s).trans h1)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [GlobalTheory.LBC.galAct_one]`. Consider the case `succ m ih`. Rewrite using `[List.ofFn_succ', List.ofFn_succ', List.prod_concat, List.prod_concat]`. Simplify using `only [Fin.coe_castSucc, Fin.val_last]`.

Rewrite using `[ih]`. Establish `e : GlobalTheory.LBC.galAct (s ^ m) n (GlobalTheory.LBC.galAct s n g) = GlobalTheory.LBC.galAct (s ^ (m + 1)) n g`. Rewrite using `[pow_succ, GlobalTheory.LBC.galAct_mul, MonoidHom.comp_apply]`. Rewrite using `[map_mul, map_mul, map_inv, e]`. Use `group`.
-/
private theorem partial_twConj {k K : Type} [Field k] [Field K] [Algebra k K] (s : K ≃ₐ[k] K) (n : ℕ)
    (δ g : GL (Fin n) K) (m : ℕ) :
    (List.ofFn fun j : Fin m => GlobalTheory.LBC.galAct (s ^ (j : ℕ)) n (g⁻¹ * δ * GlobalTheory.LBC.galAct s n g)).prod =
      g⁻¹ * (List.ofFn fun j : Fin m => GlobalTheory.LBC.galAct (s ^ (j : ℕ)) n δ).prod * GlobalTheory.LBC.galAct (s ^ m) n g := by
  induction m with
  | zero => simp [GlobalTheory.LBC.galAct_one]
  | succ m ih =>
    rw [List.ofFn_succ', List.ofFn_succ', List.prod_concat, List.prod_concat]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    have e : GlobalTheory.LBC.galAct (s ^ m) n (GlobalTheory.LBC.galAct s n g) = GlobalTheory.LBC.galAct (s ^ (m + 1)) n g := by
      rw [pow_succ, GlobalTheory.LBC.galAct_mul, MonoidHom.comp_apply]
    rw [map_mul, map_mul, map_inv, e]
    group

/- English proof (translation)
Unfold `GlobalTheory.LBC.norm`. Rewrite using `[partial_twConj, pow_finrank_aut, GlobalTheory.LBC.galAct_one, MonoidHom.id_apply]`.
-/
private theorem norm_tw {k K : Type} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] (s : K ≃ₐ[k] K)
    (n : ℕ) (δ g : GL (Fin n) K) :
    GlobalTheory.LBC.norm k s (g⁻¹ * δ * GlobalTheory.LBC.galAct s n g) = g⁻¹ * GlobalTheory.LBC.norm k s δ * g := by
  unfold GlobalTheory.LBC.norm
  rw [partial_twConj, pow_finrank_aut, GlobalTheory.LBC.galAct_one, MonoidHom.id_apply]

/- English proof (translation)
Establish `hc : IsConj γ' γ` using `GlobalTheory.Shin.isConj_of_isConj_incl F₀ F₁ n γ' γ (h'.trans h.symm)`. Take `⟨c, hc⟩` from `isConj_iff.mp hc`. Use `hfb γ' c⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Rewrite using `[← this, hc]`.
-/
private theorem fb_eq_of_isFinNorm {F₀ F₁ : Type} [Field F₀] [Field F₁] [Algebra F₀ F₁] [Finite F₁]
    (sb : F₁ ≃ₐ[F₀] F₁) {n : ℕ} (fb : GL (Fin n) F₀ → ℂ) (hfb : ∀ a b, fb (b⁻¹ * a * b) = fb a)
    {δ : GL (Fin n) F₁} {γ γ' : GL (Fin n) F₀} (h : IsFinNorm sb δ γ) (h' : IsFinNorm sb δ γ') :
    fb γ' = fb γ := by
  have hc : IsConj γ' γ := GlobalTheory.Shin.isConj_of_isConj_incl F₀ F₁ n γ' γ (h'.trans h.symm)
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have := hfb γ' c⁻¹
  rw [inv_inv] at this
  rw [← this, hc]

end UpperTheory.Gal.InertialTypesAlt.L

/- English proof (translation)
Introduce `F₀ F₁ _ _ _ _ _ sb _ n fb hfb`. Use `haveI : FiniteDimensional F₀ F₁ := Module.Finite.of_finite`. Use `⟨fun δ γ h => ?_, fun δ x => ?_⟩` and prove the remaining obligations. Establish `hex : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ` using `⟨γ, h⟩`. Rewrite using `[GlobalTheory.DZA.normLift, dif_pos hex]`.

Conclude with `UpperTheory.Gal.InertialTypesAlt.L.fb_eq_of_isFinNorm sb fb hfb h hex.choose_spec`. Establish `hiff : ∀ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ ↔ GlobalTheory.DZA.IsFinNorm sb δ γ`. Introduce `γ`. Establish `hc : IsConj (GlobalTheory.LBC.norm F₀ sb δ) (GlobalTheory.LBC.norm F₀ sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x))`. Rewrite using `[UpperTheory.Gal.InertialTypesAlt.L.norm_tw]`.

Use `isConj_iff.mpr ⟨x⁻¹, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Conclude with `⟨fun h => IsConj.trans h hc.symm, fun h => IsConj.trans h hc⟩`. Establish `hfun : (fun γ => GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ) = fun γ => GlobalTheory.DZA.IsFinNorm sb δ γ` using `funext fun γ => propext (hiff γ)`. Distinguish the cases in `hex : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ`.

Take `⟨γ, hγ⟩` from `hex`. Establish `h1 : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ` using `⟨γ, hγ⟩`. Establish `h2 : ∃ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ` using `⟨γ, (hiff γ).2 hγ⟩`. Rewrite using `[GlobalTheory.DZA.normLift, GlobalTheory.DZA.normLift, dif_pos h1, dif_pos h2]`. Conclude with `(UpperTheory.Gal.InertialTypesAlt.L.fb_eq_of_isFinNorm sb fb hfb ((hiff _).1 h2.choose_spec) h1.choose_spec).symm`.

Establish `h2 : ¬ ∃ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ` using `fun ⟨γ, hγ⟩ => hex ⟨γ, (hiff γ).1 hγ⟩`. Rewrite using `[GlobalTheory.DZA.normLift, GlobalTheory.DZA.normLift, dif_neg hex, dif_neg h2]`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.liftVal :
    UpperTheory.Gal.InertialTypesAlt.L.LiftVal := by
  intro F₀ F₁ _ _ _ _ _ sb _ n fb hfb
  haveI : FiniteDimensional F₀ F₁ := Module.Finite.of_finite
  refine ⟨fun δ γ h => ?_, fun δ x => ?_⟩
  · have hex : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ := ⟨γ, h⟩
    rw [GlobalTheory.DZA.normLift, dif_pos hex]
    exact UpperTheory.Gal.InertialTypesAlt.L.fb_eq_of_isFinNorm sb fb hfb h hex.choose_spec
  · have hiff : ∀ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ ↔ GlobalTheory.DZA.IsFinNorm sb δ γ := by
      intro γ
      have hc : IsConj (GlobalTheory.LBC.norm F₀ sb δ) (GlobalTheory.LBC.norm F₀ sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x)) := by
        rw [UpperTheory.Gal.InertialTypesAlt.L.norm_tw]
        refine isConj_iff.mpr ⟨x⁻¹, ?_⟩
        simp
      exact ⟨fun h => IsConj.trans h hc.symm, fun h => IsConj.trans h hc⟩
    have hfun : (fun γ => GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ) =
        fun γ => GlobalTheory.DZA.IsFinNorm sb δ γ := funext fun γ => propext (hiff γ)
    by_cases hex : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ
    · obtain ⟨γ, hγ⟩ := hex
      have h1 : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ := ⟨γ, hγ⟩
      have h2 : ∃ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ := ⟨γ, (hiff γ).2 hγ⟩
      rw [GlobalTheory.DZA.normLift, GlobalTheory.DZA.normLift, dif_pos h1, dif_pos h2]
      exact (UpperTheory.Gal.InertialTypesAlt.L.fb_eq_of_isFinNorm sb fb hfb ((hiff _).1 h2.choose_spec) h1.choose_spec).symm
    · have h2 : ¬ ∃ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ :=
        fun ⟨γ, hγ⟩ => hex ⟨γ, (hiff γ).1 hγ⟩
      rw [GlobalTheory.DZA.normLift, GlobalTheory.DZA.normLift, dif_neg hex, dif_neg h2]
