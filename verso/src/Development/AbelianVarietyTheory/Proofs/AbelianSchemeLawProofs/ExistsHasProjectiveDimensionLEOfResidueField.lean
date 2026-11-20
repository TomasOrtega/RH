import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe

open CategoryTheory IsLocalRing

namespace GlobalTheory

universe u

/- English proof (translation)
Take `⟨xs, h, hd⟩` from `exists_ofList_eq_maximalIdeal_length_eq R`. Establish `hreg` using `isRegular_of_ofList_eq_maximalIdeal h hd.le`. Establish `key` using `ModuleCat.projectiveDimension_quotient_eq_length.{u} xs hreg`. Rewrite `key` using `[projectiveDimension_eq_of_iso (Shrink.linearEquiv R _).toModuleIso, h]`. Rewrite using `[key]`.

Conclude with `ne_of_beq_false rfl`.
-/
theorem projectiveDimension_quotient_maximalIdeal_ne_top (R : Type u) [CommRing R]
    [IsRegularLocalRing R] :
    projectiveDimension (ModuleCat.of R (R ⧸ maximalIdeal R)) ≠ ⊤ := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have key := ModuleCat.projectiveDimension_quotient_eq_length.{u} xs hreg
  rw [projectiveDimension_eq_of_iso (Shrink.linearEquiv R _).toModuleIso, h] at key
  rw [key]
  exact ne_of_beq_false rfl

/- English proof (translation)
It suffices to establish `H : ∀ (I : Ideal R) (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N], I ≤ Module.annihilator R N → ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R N) n from H ⊥ M bot_le`. Introduce `I`. Proceed by induction on `I using IsNoetherian.induction with`. Consider the case `hgt I ih`. Introduce `N _ _ hN`.

Proceed by induction on `hN using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with`. Consider the case `subsingleton N`. Introduce `_`. Use `(ModuleCat.isZero_of_subsingleton (ModuleCat.of R N)).hasProjectiveDimensionLT_zero` as an intermediate fact. Conclude with `⟨0, hasProjectiveDimensionLT_of_ge _ 0 _ (Nat.zero_le _)⟩`.

Consider the case `quotient N p f`. Introduce `hI`. Rewrite `hI` using `[f.annihilator_eq, Ideal.annihilator_quotient]`. Rewrite using `[← projectiveDimension_ne_top_iff, projectiveDimension_eq_of_iso f.toModuleIso]`. Distinguish the cases in `hp : p.asIdeal = maximalIdeal R`.

Rewrite using `[hp]`. Conclude with `hk`. Establish `hlt : p.asIdeal < maximalIdeal R` using `lt_of_le_of_ne (le_maximalIdeal p.2.ne_top) hp`. Take `⟨x, hx, hxp⟩` from `SetLike.exists_of_lt hlt`. Establish `hreg : IsSMulRegular (R ⧸ p.asIdeal) x`.

Introduce `a b hab`. Establish `hx0 : Ideal.Quotient.mk p.asIdeal x ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis. Use `mul_left_cancel₀ hx0 ?_` and prove the remaining obligations. Simplify `hab` using `only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]`.

Establish `hJ : I < p.asIdeal ⊔ Ideal.span {x}`. Use `lt_of_le_of_lt hI (lt_of_le_of_ne le_sup_left fun e => hxp ?_)` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)`. Establish `hq` using `ih _ hJ (QuotSMulTop x (R ⧸ p.asIdeal)) (sup_le (Ideal.annihilator_quotient.ge.trans (LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _))) ((Ideal.span_singleton_le_iff_mem _).mpr (QuotSMulTop.mem_annihilator _ x)))`.

Rewrite `hq` using `[← projectiveDimension_ne_top_iff]`. Establish `key` using `ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular (ModuleCat.of R (R ⧸ p.asIdeal)) x hreg hx`. Introduce `htop`. Apply `hq` to reduce the goal to its premises. Rewrite `key` using `[htop]`.

Conclude with `key.trans rfl`. Consider the case `exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃`. Introduce `hI`. Take `⟨a, ha⟩` from `h₁ (hI.trans (f.annihilator_le_of_injective hf))`. Take `⟨b, hb⟩` from `h₃ (hI.trans (g.annihilator_le_of_surjective hg))`.

Establish `hS : (ModuleCat.shortComplexOfCompEqZero f g hfg.linearMap_comp_eq_zero).ShortExact` using `ModuleCat.shortComplex_shortExact _ hfg hf hg`. Conclude with `⟨a + b, hS.hasProjectiveDimensionLT_X₂ _ (hasProjectiveDimensionLT_of_ge (ModuleCat.of R N₁) (a + 1) _ (by omega)) (hasProjectiveDimensionLT_of_ge (ModuleCat.of R N₃) (b + 1) _ (by omega))⟩`.
-/
theorem exists_hasProjectiveDimensionLE_of_residueField (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hk : projectiveDimension (ModuleCat.of R (R ⧸ maximalIdeal R)) ≠ ⊤)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  suffices H : ∀ (I : Ideal R) (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N],
      I ≤ Module.annihilator R N → ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R N) n from
    H ⊥ M bot_le
  intro I
  induction I using IsNoetherian.induction with
  | hgt I ih =>
  intro N _ _ hN
  induction hN using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton N =>
    intro _
    have := (ModuleCat.isZero_of_subsingleton (ModuleCat.of R N)).hasProjectiveDimensionLT_zero
    exact ⟨0, hasProjectiveDimensionLT_of_ge _ 0 _ (Nat.zero_le _)⟩
  | quotient N p f =>
    intro hI
    rw [f.annihilator_eq, Ideal.annihilator_quotient] at hI
    rw [← projectiveDimension_ne_top_iff, projectiveDimension_eq_of_iso f.toModuleIso]
    by_cases hp : p.asIdeal = maximalIdeal R
    · rw [hp]
      exact hk
    have hlt : p.asIdeal < maximalIdeal R := lt_of_le_of_ne (le_maximalIdeal p.2.ne_top) hp
    obtain ⟨x, hx, hxp⟩ := SetLike.exists_of_lt hlt
    have hreg : IsSMulRegular (R ⧸ p.asIdeal) x := by
      intro a b hab
      have hx0 : Ideal.Quotient.mk p.asIdeal x ≠ 0 := by
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      refine mul_left_cancel₀ hx0 ?_
      simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hab
    have hJ : I < p.asIdeal ⊔ Ideal.span {x} := by
      refine lt_of_le_of_lt hI (lt_of_le_of_ne le_sup_left fun e => hxp ?_)
      rw [e]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
    have hq := ih _ hJ (QuotSMulTop x (R ⧸ p.asIdeal)) (sup_le
      (Ideal.annihilator_quotient.ge.trans
        (LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _)))
      ((Ideal.span_singleton_le_iff_mem _).mpr (QuotSMulTop.mem_annihilator _ x)))
    rw [← projectiveDimension_ne_top_iff] at hq
    have key := ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
      (ModuleCat.of R (R ⧸ p.asIdeal)) x hreg hx
    intro htop
    apply hq
    rw [htop] at key
    exact key.trans rfl
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro hI
    obtain ⟨a, ha⟩ := h₁ (hI.trans (f.annihilator_le_of_injective hf))
    obtain ⟨b, hb⟩ := h₃ (hI.trans (g.annihilator_le_of_surjective hg))
    have hS : (ModuleCat.shortComplexOfCompEqZero f g hfg.linearMap_comp_eq_zero).ShortExact :=
      ModuleCat.shortComplex_shortExact _ hfg hf hg
    exact ⟨a + b, hS.hasProjectiveDimensionLT_X₂ _
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of R N₁) (a + 1) _ (by omega))
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of R N₃) (b + 1) _ (by omega))⟩

/- English proof (translation)
Introduce `R _ _ M _ _ _` and use `exists_hasProjectiveDimensionLE_of_residueField R (projectiveDimension_quotient_maximalIdeal_ne_top R) M`.
-/
theorem exists_hasProjectiveDimensionLE_of_isRegularLocalRing :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
      [Module.Finite R M], ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n :=
  fun R _ _ M _ _ _ => exists_hasProjectiveDimensionLE_of_residueField R
    (projectiveDimension_quotient_maximalIdeal_ne_top R) M

end GlobalTheory
