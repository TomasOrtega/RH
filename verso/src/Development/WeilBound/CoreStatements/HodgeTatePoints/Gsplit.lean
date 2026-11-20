import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Gsplit

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. A detailed English derivation is pending.
-/
theorem coprime_different (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ NumberField.discr E) :
    IsCoprime (Ideal.span {(p : 𝓞 E)}) (differentIdeal ℤ (𝓞 E)) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨a, b, hab⟩ := (hpz.irreducible.coprime_iff_not_dvd).mpr hd
  rw [Ideal.isCoprime_iff_exists]
  refine ⟨(a : 𝓞 E) * p, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _),
    (b : 𝓞 E) * (NumberField.discr E : 𝓞 E),
    Ideal.mul_mem_left _ _ (NumberField.discr_mem_differentIdeal E (𝓞 E)), ?_⟩
  have := congrArg (Int.cast : ℤ → 𝓞 E) hab
  push_cast at this
  exact this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem not_sq_dvd (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ NumberField.discr E) (w : Ideal (𝓞 E)) (hw : w ≠ ⊤) :
    ¬ w ^ 2 ∣ Ideal.span {(p : 𝓞 E)} := by
  intro h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  have hne : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hpz.ne_zero
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hdiff : w ^ (2 - 1) ∣ differentIdeal ℤ (𝓞 E) :=
    pow_sub_one_dvd_differentIdeal ℤ w 2 hne (by rw [hmap]; exact h)
  rw [show 2 - 1 = 1 from rfl, pow_one] at hdiff
  have hspan : w ∣ Ideal.span {(p : 𝓞 E)} := (dvd_pow_self w two_ne_zero).trans h
  exact hw (Ideal.isUnit_iff.mp
    ((PositivityTheory.HtPt.Gsplit.coprime_different E p hp hd).isUnit_of_dvd' hspan hdiff))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem glue_split : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (w : Ideal (𝓞 E)) [w.IsPrime], (p : 𝓞 E) ∈ w → ∃ ε : 𝓞 E, ε - 1 ∈ w ∧ (∀ w' : Ideal (𝓞 E), w'.IsPrime → (p : 𝓞 E) ∈ w' → w' ≠ w → ε ∈ w') ∧ (∀ a : 𝓞 E, (p : 𝓞 E) ∣ ε * a ↔ a ∈ w) ∧ (p : 𝓞 E) ∣ ε * ε - ε ∧ IsCoprime (Ideal.span {(p : 𝓞 E)}) (differentIdeal ℤ (𝓞 E)) := by
  intro E hEf hEn p hp hd w hw hpw
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hwtop : w ≠ ⊤ := hw.ne_top
  have hwbot : w ≠ ⊥ := fun h => hp0 (by rw [h] at hpw; exact Ideal.mem_bot.mp hpw)
  have hmax : w.IsMaximal := hw.isMaximal hwbot
  obtain ⟨J, hJ⟩ : w ∣ Ideal.span {(p : 𝓞 E)} := Ideal.dvd_span_singleton.mpr hpw
  have hJw : ¬ J ≤ w := by
    intro hle
    apply PositivityTheory.HtPt.Gsplit.not_sq_dvd E p hp hd w hwtop
    rw [hJ, pow_two]
    exact mul_dvd_mul_left w (Ideal.dvd_iff_le.mpr hle)
  have hsup : w ⊔ J = ⊤ := by
    by_contra hne
    apply hJw
    have heq : w ⊔ J = w := by
      by_contra h'
      exact hne (hmax.out.2 _ (lt_of_le_of_ne le_sup_left (Ne.symm h')))
    exact le_sup_right.trans heq.le
  have h1 : (1 : 𝓞 E) ∈ w ⊔ J := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨x, hx, ε, hε, hxε⟩ := Submodule.mem_sup.mp h1
  have hε1 : ε - 1 ∈ w := by
    have heq : ε - 1 = -x := by
      rw [← hxε]
      ring
    rw [heq]
    exact w.neg_mem hx
  have hεw : ε ∉ w := fun h => hwtop ((Ideal.eq_top_iff_one w).mpr (by
    have h2 := w.sub_mem h hε1
    simpa using h2))
  have hmemI : ∀ b, (p : 𝓞 E) ∣ b ↔ b ∈ w * J := by
    intro b
    rw [← Ideal.mem_span_singleton, hJ]
  refine ⟨ε, hε1, ?_, ?_, ?_, PositivityTheory.HtPt.Gsplit.coprime_different E p hp hd⟩
  · intro w' hw' hpw' hne
    have hle : w * J ≤ w' := by
      rw [← hJ, Ideal.span_singleton_le_iff_mem]
      exact hpw'
    rcases hw'.mul_le.mp hle with h | h
    · exact absurd (hmax.eq_of_le hw'.ne_top h).symm hne
    · exact h hε
  · intro a
    rw [hmemI]
    constructor
    · intro h
      have hle' : w * J ≤ w := Ideal.mul_le_left
      have hw1 : ε * a ∈ w := hle' h
      rcases hw.mem_or_mem hw1 with h' | h'
      · exact absurd h' hεw
      · exact h'
    · intro ha
      rw [mul_comm ε a]
      exact Ideal.mul_mem_mul ha hε
  · rw [hmemI]
    have heq : ε * ε - ε = (ε - 1) * ε := by ring
    rw [heq]
    exact Ideal.mul_mem_mul hε1 hε

end PositivityTheory.HtPt.Gsplit
