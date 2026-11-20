import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in
/- English proof (translation)
Rewrite using `[FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, HeightOneSpectrum.valuation_of_algebraMap, ← HeightOneSpectrum.intValuation_lt_one_iff_mem]`. Conclude with `one_lt_inv₀ (zero_lt_iff.mpr (Q.intValuation_ne_zero x hx))`.
-/
private lemma one_lt_valued_inv_iff_mem {E : Type} [Field E] [NumberField E]
    (Q : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) (hx : x ≠ 0) :
    1 < Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q) ↔ x ∈ Q.asIdeal := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
    ← HeightOneSpectrum.intValuation_lt_one_iff_mem]
  exact one_lt_inv₀ (zero_lt_iff.mpr (Q.intValuation_ne_zero x hx))

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in

/- English proof (translation)
Introduce `F E _ _ _ _ _ Φ hΦ hint hplace e P v ε hε he heε`. Take `⟨h0, -⟩` from `hplace v ε hε`. Establish `ha : (Φ e).1 = 0`. Establish `h` using `congrArg (fun z => (Φ z).1) heε`. Simplify using `only [map_mul, Prod.fst_mul, h0, mul_zero] at h`.

Conclude with `h.symm`. Establish `hidem : ∀ Q, (Φ e).2 Q = 0 ∨ (Φ e).2 Q = 1`. Introduce `Q`. Establish `h` using `congrArg (fun z => (Φ z).2 Q) he`. Rewrite `h` using `[map_mul]`.

Conclude with `IsIdempotentElem.iff_eq_zero_or_one.mp h`. Establish `key : ∀ x : 𝓞 E, x ≠ 0 → (_root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E (e * _root_.HeckeCharacterZeroLocus.ThmBIn.incA F E ((x : E)⁻¹)) ∉ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔ ∃ Q, (Φ e).2 Q = 1 ∧ x ∈ Q.asIdeal)`. Introduce `x hx`. Rewrite using `[hint, map_mul, hΦ]`. Use `push_neg`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Q, hQ⟩`. Express the relevant statement in the definitionally equal form `1 < Valued.v ((Φ e).2 Q * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q) at hQ`. Break down `hidem Q with h | h` into its components or cases. Rewrite `hQ` using `[h, zero_mul, map_zero]`.

Conclude with `absurd hQ (not_lt.mpr zero_le')`. Rewrite `hQ` using `[h, one_mul, one_lt_valued_inv_iff_mem Q x hx]`. Conclude with `⟨Q, h, hQ⟩`. Introduce and unpack `⟨Q, h, hQ⟩`. Use `⟨Q, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `1 < Valued.v ((Φ e).2 Q * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q)`. Rewrite using `[h, one_mul, one_lt_valued_inv_iff_mem Q x hx]`. Conclude with `hQ`. Prove the components needed by the constructor for the conclusion. Introduce `hcrit`.

Establish `hS : ∀ Q, (Φ e).2 Q = 1 → Q = P`. Introduce `Q hQ`. Assume the negation of the conclusion as `hne`. Establish `hnle : ¬ Q.asIdeal ≤ P.asIdeal` using `fun hle => hne (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hle))`. Take `⟨x, hxQ, hxP⟩` from `Set.not_subset.mp hnle`.

Establish `hx : x ≠ 0` using `fun h => hxP (h ▸ P.asIdeal.zero_mem)`. Conclude with `hxP ((hcrit x hx).mpr ((key x hx).mpr ⟨Q, hQ, hxQ⟩))`. Take `⟨x, hxP, hx⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot`. Take `⟨Q, hQ, -⟩` from `(key x hx).mp ((hcrit x hx).mp hxP)`. Establish `hQP` using `hS Q hQ`.

Substitute `hQP` using the available equality. Use `⟨ha, hQ, fun R hR => ?_⟩` and prove the remaining obligations. Break down `hidem R with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (hS R h) hR`.

Introduce and unpack `⟨-, hP, hQ⟩ x hx`. Rewrite using `[key x hx]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun hxP => ⟨P, hP, hxP⟩`. Introduce and unpack `⟨Q, h, hxQ⟩`.

Distinguish the cases in `hQP : Q = P`. Conclude with `hQP ▸ hxQ`. Rewrite `h` using `[hQ Q hQP]`. Conclude with `absurd h zero_ne_one`.
-/
theorem _root_.GlobalTheory.adele_idem_prime_criterion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Φ : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E)), (∀ x : E, Φ (_root_.HeckeCharacterZeroLocus.ThmBIn.incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ (e : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (ε : _root_.HeckeCharacterZeroLocus.ThmBIn.AF F), _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → e * e = e → e * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε = e → ((∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E (e * _root_.HeckeCharacterZeroLocus.ThmBIn.incA F E ((x : E)⁻¹)) ∉ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E)) ↔ ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0)) := by
  intro F E _ _ _ _ _ Φ hΦ hint hplace e P v ε hε he heε
  obtain ⟨h0, -⟩ := hplace v ε hε
  have ha : (Φ e).1 = 0 := by
    have h := congrArg (fun z => (Φ z).1) heε
    simp only [map_mul, Prod.fst_mul, h0, mul_zero] at h
    exact h.symm
  have hidem : ∀ Q, (Φ e).2 Q = 0 ∨ (Φ e).2 Q = 1 := by
    intro Q
    have h := congrArg (fun z => (Φ z).2 Q) he
    rw [map_mul] at h
    exact IsIdempotentElem.iff_eq_zero_or_one.mp h
  have key : ∀ x : 𝓞 E, x ≠ 0 → (_root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E (e * _root_.HeckeCharacterZeroLocus.ThmBIn.incA F E ((x : E)⁻¹)) ∉ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔
      ∃ Q, (Φ e).2 Q = 1 ∧ x ∈ Q.asIdeal) := by
    intro x hx
    rw [hint, map_mul, hΦ]
    push_neg
    constructor
    · rintro ⟨Q, hQ⟩
      change 1 < Valued.v ((Φ e).2 Q * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q) at hQ
      rcases hidem Q with h | h
      · rw [h, zero_mul, map_zero] at hQ
        exact absurd hQ (not_lt.mpr zero_le')
      · rw [h, one_mul, one_lt_valued_inv_iff_mem Q x hx] at hQ
        exact ⟨Q, h, hQ⟩
    · rintro ⟨Q, h, hQ⟩
      refine ⟨Q, ?_⟩
      change 1 < Valued.v ((Φ e).2 Q * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q)
      rw [h, one_mul, one_lt_valued_inv_iff_mem Q x hx]
      exact hQ
  constructor
  · intro hcrit
    have hS : ∀ Q, (Φ e).2 Q = 1 → Q = P := by
      intro Q hQ
      by_contra hne
      have hnle : ¬ Q.asIdeal ≤ P.asIdeal := fun hle =>
        hne (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hle))
      obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.mp hnle
      have hx : x ≠ 0 := fun h => hxP (h ▸ P.asIdeal.zero_mem)
      exact hxP ((hcrit x hx).mpr ((key x hx).mpr ⟨Q, hQ, hxQ⟩))
    obtain ⟨x, hxP, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    obtain ⟨Q, hQ, -⟩ := (key x hx).mp ((hcrit x hx).mp hxP)
    have hQP := hS Q hQ
    subst hQP
    refine ⟨ha, hQ, fun R hR => ?_⟩
    rcases hidem R with h | h
    · exact h
    · exact absurd (hS R h) hR
  · rintro ⟨-, hP, hQ⟩ x hx
    rw [key x hx]
    constructor
    · exact fun hxP => ⟨P, hP, hxP⟩
    · rintro ⟨Q, h, hxQ⟩
      by_cases hQP : Q = P
      · exact hQP ▸ hxQ
      · rw [hQ Q hQP] at h
        exact absurd h zero_ne_one

end GlobalTheory
