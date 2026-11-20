import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Introduce `F _ _ v`. Establish `h2 : ∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x` using `fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x`. Establish `h3 : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1`. Introduce `x hx`. Take `⟨a, ha⟩` from `GlobalTheory.Idele.exists_valued_sub_le v hx 1`.

Use `⟨a, lt_of_le_of_lt ha ?_⟩` and prove the remaining obligations. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers. Use `⟨?_, h2, h3, ?_⟩` and prove the remaining obligations. Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer F`.

Conclude with `⟨π, hπ, (h2 π).trans hπ⟩`. Use `haveI : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot`. Use `letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _`. Use `choose s hs using Ideal.Quotient.mk_surjective (I := v.asIdeal)`. Use `⟨Finset.univ.image fun q : 𝓞 F ⧸ v.asIdeal => algebraMap F (v.adicCompletion F) ((s q : 𝓞 F) : F), ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `Finset.card_image_le.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Finset.card_univ, Nat.card_eq_fintype_card]`. Introduce `r hr`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hr`. Rewrite using `[h2]`.

Conclude with `v.valuation_le_one (s q)`. Introduce `x hx`. Take `⟨a, ha⟩` from `h3 x hx`. Use `⟨_, Finset.mem_image.2 ⟨Ideal.Quotient.mk _ a, Finset.mem_univ _, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hm : a - s (Ideal.Quotient.mk _ a) ∈ v.asIdeal` using `Ideal.Quotient.eq.1 (hs _).symm`.

Establish `hl : v.valuation F (algebraMap (𝓞 F) F (a - s (Ideal.Quotient.mk _ a))) < 1` using `(v.valuation_lt_one_iff_mem _).2 hm`. Rewrite `hl` using `[← h2, map_sub, map_sub]`. Rewrite using `[← sub_add_sub_cancel x (algebraMap F (v.adicCompletion F) (a : F))]`. Conclude with `lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hl)`.
-/
theorem exists_uniformizer_and_residue_representatives :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∃ π : F, v.valuation F π = WithZero.exp (-1) ∧ Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1)) ∧ (∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x) ∧ (∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1) ∧ ∃ R : Finset (v.adicCompletion F), R.card ≤ Ideal.absNorm v.asIdeal ∧ (∀ r ∈ R, Valued.v r ≤ 1) ∧ ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ r ∈ R, Valued.v (x - r) < 1 := by
  intro F _ _ v
  classical
  have h2 : ∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have h3 : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 →
      ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := GlobalTheory.Idele.exists_valued_sub_le v hx 1
    refine ⟨a, lt_of_le_of_lt ha ?_⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  refine ⟨?_, h2, h3, ?_⟩
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    exact ⟨π, hπ, (h2 π).trans hπ⟩
  · haveI : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    choose s hs using Ideal.Quotient.mk_surjective (I := v.asIdeal)
    refine ⟨Finset.univ.image fun q : 𝓞 F ⧸ v.asIdeal =>
      algebraMap F (v.adicCompletion F) ((s q : 𝓞 F) : F), ?_, ?_, ?_⟩
    · refine Finset.card_image_le.trans (le_of_eq ?_)
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Finset.card_univ, Nat.card_eq_fintype_card]
    · intro r hr
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
      rw [h2]
      exact v.valuation_le_one (s q)
    · intro x hx
      obtain ⟨a, ha⟩ := h3 x hx
      refine ⟨_, Finset.mem_image.2 ⟨Ideal.Quotient.mk _ a, Finset.mem_univ _, rfl⟩, ?_⟩
      have hm : a - s (Ideal.Quotient.mk _ a) ∈ v.asIdeal := Ideal.Quotient.eq.1 (hs _).symm
      have hl : v.valuation F (algebraMap (𝓞 F) F (a - s (Ideal.Quotient.mk _ a))) < 1 :=
        (v.valuation_lt_one_iff_mem _).2 hm
      rw [← h2, map_sub, map_sub] at hl
      rw [← sub_add_sub_cancel x (algebraMap F (v.adicCompletion F) (a : F))]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hl)

end GlobalTheory.QNorm
