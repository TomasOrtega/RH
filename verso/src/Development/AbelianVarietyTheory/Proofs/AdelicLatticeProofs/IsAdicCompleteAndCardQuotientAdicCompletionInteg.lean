import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Rewrite using `[Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Establish `ha : Valued.v (a : v.adicCompletion F) ≤ 1` using `a.2`. Express the relevant statement in the definitionally equal form `Valued.v ((a : v.adicCompletion F) * t) ≤ _`.

Rewrite using `[map_mul]`. Conclude with `mul_le_of_le_one_left' ha`. Introduce `hx`. Establish `ht1 : (t : v.adicCompletion F) ≠ 0`. Introduce `h`.

Rewrite `ht` using `[h]`. Simplify using `at ht`. Establish `hm : (x : v.adicCompletion F) / t ∈ v.adicCompletionIntegers F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, div_le_one₀ (zero_lt_iff.2 ht)]`. Conclude with `hx`.

Use `⟨⟨_, hm⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x : v.adicCompletion F) / t * t = x`. Rewrite using `[div_mul_cancel₀ _ ht1]`.
-/
theorem mem_span_singleton_adicCompletionIntegers {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {t : v.adicCompletionIntegers F}
    (ht : Valued.v (t : v.adicCompletion F) ≠ 0) (x : v.adicCompletionIntegers F) :
    x ∈ Ideal.span {t} ↔
      Valued.v (x : v.adicCompletion F) ≤ Valued.v (t : v.adicCompletion F) := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    have ha : Valued.v (a : v.adicCompletion F) ≤ 1 := a.2
    change Valued.v ((a : v.adicCompletion F) * t) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_left' ha
  · intro hx
    have ht1 : (t : v.adicCompletion F) ≠ 0 := by
      intro h; rw [h] at ht; simp at ht
    have hm : (x : v.adicCompletion F) / t ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, div_le_one₀ (zero_lt_iff.2 ht)]
      exact hx
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    change (x : v.adicCompletion F) / t * t = x
    rw [div_mul_cancel₀ _ ht1]

/- English proof (translation)
Introduce `F _ _ v`. Use `⟨fun t ht => ?_, fun t e ht => ?_⟩` and prove the remaining obligations. Use `NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion F) ⟨?_, ?_, ?_⟩ (IsNoetherian.noetherian _) ?_` and prove the remaining obligations. Conclude with `FaithfulSMul.algebraMap_injective _ _`. Introduce `x`.

Establish `: ‖(x : v.adicCompletion F)‖ ≤ 1` using `Valued.toNormedField.norm_le_one_iff.2 x.2`. Conclude with `this` after adjusting the coercions. Introduce `x hx`. Establish `: ‖x‖ ≤ 1` using `by exact_mod_cast hx`. Conclude with `⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩`.

Rewrite using `[Ne, Ideal.span_singleton_eq_top, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]`. Conclude with `ht.ne`. Establish `ht0 : Valued.v (t : v.adicCompletion F) ≠ 0` using `by rw [ht]; exact WithZero.exp_ne_zero`. Set `f : 𝓞 F →+* v.adicCompletionIntegers F ⧸ Ideal.span {t}` to `(Ideal.Quotient.mk _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))`. Establish `hs : Function.Surjective f`.

Introduce `y`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Take `⟨s, hs⟩` from `Idele.exists_valued_sub_le v (a := (y : v.adicCompletion F)) y.2 e`. Use `⟨s, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ _ = _`.

Rewrite using `[eq_comm, Ideal.Quotient.eq, mem_span_singleton_adicCompletionIntegers v ht0, ht]`. Conclude with `hs`. Establish `hk : RingHom.ker f = v.asIdeal ^ e`. Use extensionality with `s`. Rewrite using `[RingHom.mem_ker]`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ _ = _ ↔ _`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton_adicCompletionIntegers v ht0, ht, HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_ …`. Rewrite using `[← Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv, hk, ← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
theorem isAdicComplete_and_card_quotient_adicCompletionIntegers :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∀ t : v.adicCompletionIntegers F, Valued.v (t : v.adicCompletion F) < 1 → IsAdicComplete (Ideal.span {t}) (v.adicCompletionIntegers F)) ∧ ∀ (t : v.adicCompletionIntegers F) (e : ℕ), Valued.v (t : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) → Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {t}) = Ideal.absNorm v.asIdeal ^ e := by
  intro F _ _ v
  refine ⟨fun t ht => ?_, fun t e ht => ?_⟩
  · refine NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion F) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) ?_
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : v.adicCompletion F)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
    · rw [Ne, Ideal.span_singleton_eq_top,
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      exact ht.ne
  · have ht0 : Valued.v (t : v.adicCompletion F) ≠ 0 := by rw [ht]; exact WithZero.exp_ne_zero
    let f : 𝓞 F →+* v.adicCompletionIntegers F ⧸ Ideal.span {t} :=
      (Ideal.Quotient.mk _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
    have hs : Function.Surjective f := by
      intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨s, hs⟩ := Idele.exists_valued_sub_le v (a := (y : v.adicCompletion F)) y.2 e
      refine ⟨s, ?_⟩
      change Ideal.Quotient.mk _ _ = _
      rw [eq_comm, Ideal.Quotient.eq, mem_span_singleton_adicCompletionIntegers v ht0, ht]
      exact hs
    have hk : RingHom.ker f = v.asIdeal ^ e := by
      ext s
      rw [RingHom.mem_ker]
      change Ideal.Quotient.mk _ _ = _ ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton_adicCompletionIntegers v ht0, ht,
        HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    rw [← Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv, hk, ← map_pow,
      Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.CNorm
