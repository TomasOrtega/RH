import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.HatCap

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
The claim follows from `RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) (fun v => Valued.isOpen_valuationSubring (v.adicCompletion E))`.
-/
theorem isOpen_integral :
    IsOpen {y : Af E | ∀ v : HeightOneSpectrum (𝓞 E), y v ∈ v.adicCompletionIntegers E} :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion E))

/- English proof (translation)
Take `⟨n, hnc, hn0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hc`. Establish `hnE : algebraMap (OF E) E n ≠ 0`. Introduce `h`. Apply `hn0` to reduce the goal to its premises. Establish `h' : ((n : maximalRealSubfield E) : E) = 0` using `h`.

Conclude with `h'` after adjusting the coercions. Use `set m : E := algebraMap (OF E) E n with hm`. Establish `hcont : Continuous fun z : Af E => (algebraMap E (Af E) x - z) * algebraMap E (Af E) m⁻¹` using `(continuous_const.sub continuous_id).mul continuous_const`. Establish `hU` using `isOpen_integral.preimage hcont`. Take `⟨_, hz, y, hy, rfl⟩` from `mem_closure_iff.1 hx _ hU (by`.

Rewrite using `[Set.mem_preimage, sub_self, zero_mul]`. Conclude with `fun v => zero_mem _)`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = (x - y) * m⁻¹ := by`. Use `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun v => ?_` and prove the remaining obligations. Establish `h3 : (algebraMap E (Af E) ((x - y) * m⁻¹)) v ∈ v.adicCompletionIntegers E`.

Rewrite using `[map_mul, map_sub]`. Conclude with `hz v`. Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h3)`. Establish `hxy : x = y + algebraMap (𝓞 E) E (b * algebraMap (OF E) (𝓞 E) n)`. Establish `: algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) n) = m` using `rfl`.

Rewrite using `[map_mul, hb, this, mul_assoc, inv_mul_cancel₀ hnE]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hxy]`. Use `add_mem hy (mem_orderC.2 ⟨0, _, Ideal.mul_mem_left _ b (Ideal.mem_map_of_mem _ hnc), by simp⟩)` and prove the remaining obligations.
-/
theorem mem_orderC_of_mem_hatO {c : Ideal (OF E)} (hc : c ≠ ⊥) {x : E} (hx : algebraMap E (Af E) x ∈ hatO c) :
    x ∈ orderC c := by
  obtain ⟨n, hnc, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  have hnE : algebraMap (OF E) E n ≠ 0 := by
    intro h
    apply hn0
    have h' : ((n : maximalRealSubfield E) : E) = 0 := h
    exact_mod_cast h'
  set m : E := algebraMap (OF E) E n with hm
  have hcont : Continuous fun z : Af E => (algebraMap E (Af E) x - z) * algebraMap E (Af E) m⁻¹ :=
    (continuous_const.sub continuous_id).mul continuous_const
  have hU := isOpen_integral.preimage hcont
  obtain ⟨_, hz, y, hy, rfl⟩ := mem_closure_iff.1 hx _ hU (by
    rw [Set.mem_preimage, sub_self, zero_mul]
    exact fun v => zero_mem _)
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = (x - y) * m⁻¹ := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun v => ?_
    have h3 : (algebraMap E (Af E) ((x - y) * m⁻¹)) v ∈ v.adicCompletionIntegers E := by
      rw [map_mul, map_sub]; exact hz v
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h3)
  have hxy : x = y + algebraMap (𝓞 E) E (b * algebraMap (OF E) (𝓞 E) n) := by
    have : algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) n) = m := rfl
    rw [map_mul, hb, this, mul_assoc, inv_mul_cancel₀ hnE]; ring
  rw [hxy]
  refine add_mem hy (mem_orderC.2 ⟨0, _, Ideal.mul_mem_left _ b (Ideal.mem_map_of_mem _ hnc), by simp⟩)

/- English proof (translation)
Introduce `E _ _ _ c hc`. Use extensionality with `x`. Rewrite using `[mem_lattice, inv_one, Units.val_one, mul_one]`. Conclude with `⟨mem_orderC_of_mem_hatO hc, algebraMap_mem_hatO⟩`.
-/
theorem lattice_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → lattice c 1 = (orderC c : Set E) := by
  intro E _ _ _ c hc
  ext x
  rw [mem_lattice, inv_one, Units.val_one, mul_one]
  exact ⟨mem_orderC_of_mem_hatO hc, algebraMap_mem_hatO⟩

end GlobalTheory.CMVal.HatCap
