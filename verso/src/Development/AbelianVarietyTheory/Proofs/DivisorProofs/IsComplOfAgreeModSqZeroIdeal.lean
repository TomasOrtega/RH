import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroSummand

variable {R : Type} [CommRing R] (I : Ideal R) {C : Type 1} [AddCommGroup C] [Module R C]

/- English proof (translation)
Rewrite using `[← h.sup_eq_top, Submodule.smul_sup]`.
-/
theorem smul_top_eq_sup {P Q : Submodule R C} (h : IsCompl P Q) :
    I • (⊤ : Submodule R C) = I • P ⊔ I • Q := by
  rw [← h.sup_eq_top, Submodule.smul_sup]

/- English proof (translation)
Rewrite using `[smul_top_eq_sup I h, ← sup_assoc, sup_eq_left.mpr (Submodule.smul_le_right : I • P ≤ P)]`.
-/
theorem sup_smul_top_eq {P Q : Submodule R C} (h : IsCompl P Q) :
    P ⊔ I • (⊤ : Submodule R C) = P ⊔ I • Q := by
  rw [smul_top_eq_sup I h, ← sup_assoc, sup_eq_left.mpr (Submodule.smul_le_right : I • P ≤ P)]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Take `⟨hxP, hxJ⟩` from `Submodule.mem_inf.mp hx`. Rewrite `hxJ` using `[smul_top_eq_sup I h, Submodule.mem_sup]`. Take `⟨a, ha, b, hb, rfl⟩` from `hxJ`.

Establish `hbQ : b ∈ Q` using `Submodule.smul_le_right hb`. Establish `hbP : b ∈ P`. Establish `e : b = (a + b) - a` using `by abel`. Rewrite using `[e]`. Conclude with `P.sub_mem hxP (Submodule.smul_le_right ha)`.

Establish `hb0 : b = 0` using `(Submodule.disjoint_def.mp h.disjoint) b hbP hbQ`. Simplify `ha` using `[hb0]`. Conclude with `le_inf Submodule.smul_le_right (Submodule.smul_mono le_rfl le_top)`.
-/
theorem inf_smul_top {P Q : Submodule R C} (h : IsCompl P Q) :
    P ⊓ I • (⊤ : Submodule R C) = I • P := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxJ⟩ := Submodule.mem_inf.mp hx
    rw [smul_top_eq_sup I h, Submodule.mem_sup] at hxJ
    obtain ⟨a, ha, b, hb, rfl⟩ := hxJ
    have hbQ : b ∈ Q := Submodule.smul_le_right hb
    have hbP : b ∈ P := by
      have e : b = (a + b) - a := by abel
      rw [e]; exact P.sub_mem hxP (Submodule.smul_le_right ha)
    have hb0 : b = 0 := (Submodule.disjoint_def.mp h.disjoint) b hbP hbQ
    simpa [hb0] using ha
  · exact le_inf Submodule.smul_le_right (Submodule.smul_mono le_rfl le_top)

/- English proof (translation)
Rewrite using `[← Submodule.mul_smul, ← sq, hI, Submodule.zero_eq_bot, Submodule.bot_smul]`.
-/
theorem smul_smul_top (hI : I ^ 2 = 0) : I • I • (⊤ : Submodule R C) = ⊥ := by
  rw [← Submodule.mul_smul, ← sq, hI, Submodule.zero_eq_bot, Submodule.bot_smul]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem smul_le_of_sup_eq (hI : I ^ 2 = 0) {K F : Submodule R C}
    (h : K ⊔ I • ⊤ = F ⊔ I • ⊤) : I • K ≤ I • F := by
  calc I • K ≤ I • (K ⊔ I • ⊤) := Submodule.smul_mono le_rfl le_sup_left
    _ = I • F := by rw [h, Submodule.smul_sup, smul_smul_top I hI, sup_bot_eq]

end GlobalTheory.SqZeroSummand

open GlobalTheory.SqZeroSummand in

/- English proof (translation)
Introduce `R _ I hI C _ _ F K N hFN hKF`. Establish `isCompl_of : K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N`. Introduce `hi`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`.

Introduce `x hxK hxN`. Establish `hx : x ∈ F ⊔ I • N`. Rewrite using `[← sup_smul_top_eq I hFN, ← hKF]`. Conclude with `Submodule.mem_sup_left hxK`. Take `⟨y, hy, b, hb, rfl⟩` from `Submodule.mem_sup.mp hx`.

Establish `hbN : b ∈ N` using `Submodule.smul_le_right hb`. Establish `hyN : y ∈ N`. Establish `e : y = (y + b) - b` using `by abel`. Rewrite using `[e]`. Conclude with `N.sub_mem hxN hbN`.

Establish `hy0 : y = 0` using `(Submodule.disjoint_def.mp hFN.disjoint) y hy hyN`. Substitute `hy0` using the available equality. Rewrite `hxK`, `hxN`, the goal using `[zero_add]`. Establish `hbJ : b ∈ K ⊓ I • (⊤ : Submodule R C)` using `⟨hxK, Submodule.smul_mono le_rfl le_top hb⟩`. Rewrite `hbJ` using `[hi]`.

Conclude with `(Submodule.disjoint_def.mp hFN.disjoint) b hbJ.1 hbN`. Rewrite using `[codisjoint_iff, eq_top_iff, ← hFN.sup_eq_top]`. Establish `h1 : I • F ≤ K`. Establish `: I • F ≤ K ⊓ I • ⊤`. Rewrite using `[hi]`.

Conclude with `le_inf Submodule.smul_le_right (Submodule.smul_mono le_rfl le_top)`. Conclude with `this.trans inf_le_left`. Establish `h2 : F ≤ K ⊔ N`. Combine the equalities or inequalities in the displayed calculation. Conclude with `sup_le h2 le_sup_right`.

Use `⟨isCompl_of, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨N', hKN'⟩`. Establish `hi : K ⊓ I • ⊤ = F ⊓ I • ⊤`. Rewrite using `[inf_smul_top I hKN', inf_smul_top I hFN]`. Conclude with `le_antisymm (smul_le_of_sup_eq I hI hKF) (smul_le_of_sup_eq I hI hKF.symm)`.

Establish `hKN` using `isCompl_of hi`. Use `⟨hi, (N.projection K hKN.symm) ∘ₗ F.subtype, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `c`. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply]`. Use `⟨?_, Submodule.projection_apply_mem _ _, Submodule.sub_projection_mem _ _⟩` and prove the remaining obligations.

Establish `hc : c.1 ∈ K ⊔ I • N`. Rewrite using `[← sup_smul_top_eq I hKN, hKF]`. Conclude with `Submodule.mem_sup_left c.2`. Take `⟨k, hk, b, hb, hkb⟩` from `Submodule.mem_sup.mp hc`. Rewrite using `[← hkb, map_add, (Submodule.projection_apply_eq_zero_iff _).mpr hk, zero_add, Submodule.projection_apply_of_mem_left _ (Submodule.smul_le_right hb)]`.

Conclude with `Submodule.smul_mono le_rfl le_top hb`. Introduce `c hc`. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply]`. Establish `h' : c.1 ∈ K ⊓ I • (⊤ : Submodule R C)` using `by rw [hi]; exact ⟨c.2, hc⟩`. Conclude with `(Submodule.projection_apply_eq_zero_iff _).mpr h'.1`.

Introduce `k hk`. Establish `hk' : k ∈ F ⊔ I • N`. Rewrite using `[← sup_smul_top_eq I hFN, ← hKF]`. Conclude with `Submodule.mem_sup_left hk`. Take `⟨f, hf, b, hb, hfb⟩` from `Submodule.mem_sup.mp hk'`.

Use `⟨⟨f, hf⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply]`. Establish `hbN : b ∈ N` using `Submodule.smul_le_right hb`. Establish `ef : f = k - b` using `by rw [← hfb]; abel`. Rewrite using `[ef, map_sub, (Submodule.projection_apply_eq_zero_iff _).mpr hk, Submodule.projection_apply_of_mem_left _ hbN]`.

Normalize the expressions using the abelian group laws.
-/
theorem GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero :
    ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 → ∀ (C : Type 1) [AddCommGroup C] [Module R C] (F K N : Submodule R C), IsCompl F N → K ⊔ I • ⊤ = F ⊔ I • ⊤ → ((K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N) ∧ ((∃ N', IsCompl K N') → K ⊓ I • ⊤ = F ⊓ I • ⊤ ∧ ∃ u : F →ₗ[R] C, (∀ c, u c ∈ I • (⊤ : Submodule R C) ∧ u c ∈ N ∧ c.1 - u c ∈ K) ∧ (∀ c : F, c.1 ∈ I • (⊤ : Submodule R C) → u c = 0) ∧ ∀ k ∈ K, ∃ c : F, k = c.1 - u c)) := by
  intro R _ I hI C _ _ F K N hFN hKF
  have isCompl_of : K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N := by
    intro hi
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxK hxN
      have hx : x ∈ F ⊔ I • N := by
        rw [← sup_smul_top_eq I hFN, ← hKF]; exact Submodule.mem_sup_left hxK
      obtain ⟨y, hy, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      have hbN : b ∈ N := Submodule.smul_le_right hb
      have hyN : y ∈ N := by
        have e : y = (y + b) - b := by abel
        rw [e]; exact N.sub_mem hxN hbN
      have hy0 : y = 0 := (Submodule.disjoint_def.mp hFN.disjoint) y hy hyN
      subst hy0
      rw [zero_add] at hxK hxN ⊢
      have hbJ : b ∈ K ⊓ I • (⊤ : Submodule R C) :=
        ⟨hxK, Submodule.smul_mono le_rfl le_top hb⟩
      rw [hi] at hbJ
      exact (Submodule.disjoint_def.mp hFN.disjoint) b hbJ.1 hbN
    · rw [codisjoint_iff, eq_top_iff, ← hFN.sup_eq_top]
      have h1 : I • F ≤ K := by
        have : I • F ≤ K ⊓ I • ⊤ := by
          rw [hi]; exact le_inf Submodule.smul_le_right (Submodule.smul_mono le_rfl le_top)
        exact this.trans inf_le_left
      have h2 : F ≤ K ⊔ N := by
        calc F ≤ F ⊔ I • ⊤ := le_sup_left
          _ = K ⊔ I • ⊤ := hKF.symm
          _ = K ⊔ (I • F ⊔ I • N) := by rw [smul_top_eq_sup I hFN]
          _ ≤ K ⊔ N := sup_le le_sup_left
              (sup_le (h1.trans le_sup_left) (Submodule.smul_le_right.trans le_sup_right))
      exact sup_le h2 le_sup_right
  refine ⟨isCompl_of, ?_⟩
  rintro ⟨N', hKN'⟩
  have hi : K ⊓ I • ⊤ = F ⊓ I • ⊤ := by
    rw [inf_smul_top I hKN', inf_smul_top I hFN]
    exact le_antisymm (smul_le_of_sup_eq I hI hKF) (smul_le_of_sup_eq I hI hKF.symm)
  have hKN := isCompl_of hi
  refine ⟨hi, (N.projection K hKN.symm) ∘ₗ F.subtype, ?_, ?_, ?_⟩
  · intro c
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    refine ⟨?_, Submodule.projection_apply_mem _ _, Submodule.sub_projection_mem _ _⟩
    have hc : c.1 ∈ K ⊔ I • N := by
      rw [← sup_smul_top_eq I hKN, hKF]; exact Submodule.mem_sup_left c.2
    obtain ⟨k, hk, b, hb, hkb⟩ := Submodule.mem_sup.mp hc
    rw [← hkb, map_add, (Submodule.projection_apply_eq_zero_iff _).mpr hk, zero_add,
      Submodule.projection_apply_of_mem_left _ (Submodule.smul_le_right hb)]
    exact Submodule.smul_mono le_rfl le_top hb
  · intro c hc
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    have h' : c.1 ∈ K ⊓ I • (⊤ : Submodule R C) := by rw [hi]; exact ⟨c.2, hc⟩
    exact (Submodule.projection_apply_eq_zero_iff _).mpr h'.1
  · intro k hk
    have hk' : k ∈ F ⊔ I • N := by
      rw [← sup_smul_top_eq I hFN, ← hKF]; exact Submodule.mem_sup_left hk
    obtain ⟨f, hf, b, hb, hfb⟩ := Submodule.mem_sup.mp hk'
    refine ⟨⟨f, hf⟩, ?_⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    have hbN : b ∈ N := Submodule.smul_le_right hb
    have ef : f = k - b := by rw [← hfb]; abel
    rw [ef, map_sub, (Submodule.projection_apply_eq_zero_iff _).mpr hk,
      Submodule.projection_apply_of_mem_left _ hbN]
    abel
