import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Gsplit

/- English proof (translation)
Establish `hpz : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Take `⟨a, b, hab⟩` from `(hpz.irreducible.coprime_iff_not_dvd).mpr hd`. Rewrite using `[Ideal.isCoprime_iff_exists]`. Use `⟨(a : 𝓞 E) * p, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), (b : 𝓞 E) * (NumberField.discr E : 𝓞 E), Ideal.mul_mem_left _ _ (NumberField.discr_mem_differentIdeal E (𝓞 E)), ?_⟩` and prove the remaining obligations. Use `congrArg (Int.cast : ℤ → 𝓞 E) hab` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`.
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
Introduce `h`. Establish `hpz : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Use `haveI : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible`. Establish `hne : Ideal.span {(p : ℤ)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`.

Conclude with `hpz.ne_zero`. Establish `hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)}`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `hdiff : w ^ (2 - 1) ∣ differentIdeal ℤ (𝓞 E)` using `pow_sub_one_dvd_differentIdeal ℤ w 2 hne (by rw [hmap]; exact h)`. Rewrite `hdiff` using `[show 2 - 1 = 1 from rfl, pow_one]`.

Establish `hspan : w ∣ Ideal.span {(p : 𝓞 E)}` using `(dvd_pow_self w two_ne_zero).trans h`. Conclude with `hw (Ideal.isUnit_iff.mp ((PositivityTheory.HtPt.Gsplit.coprime_different E p hp hd).isUnit_of_dvd' hspan hdiff))`.
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
Introduce `E hEf hEn p hp hd w hw hpw`. Establish `hp0 : (p : 𝓞 E) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`. Establish `hwtop : w ≠ ⊤` using `hw.ne_top`. Establish `hwbot : w ≠ ⊥` using `fun h => hp0 (by rw [h] at hpw; exact Ideal.mem_bot.mp hpw)`. Establish `hmax : w.IsMaximal` using `hw.isMaximal hwbot`.

Take `⟨J, hJ⟩ : w ∣ Ideal.span {(p : 𝓞 E)}` from `Ideal.dvd_span_singleton.mpr hpw`. Establish `hJw : ¬ J ≤ w`. Introduce `hle`. Apply `PositivityTheory.HtPt.Gsplit.not_sq_dvd E p hp hd w hwtop` to reduce the goal to its premises. Rewrite using `[hJ, pow_two]`.

Conclude with `mul_dvd_mul_left w (Ideal.dvd_iff_le.mpr hle)`. Establish `hsup : w ⊔ J = ⊤`. Assume the negation of the conclusion as `hne`. Apply `hJw` to reduce the goal to its premises. Establish `heq : w ⊔ J = w`.

Assume the negation of the conclusion as `h'`. Conclude with `hne (hmax.out.2 _ (lt_of_le_of_ne le_sup_left (Ne.symm h')))`. Conclude with `le_sup_right.trans heq.le`. Establish `h1 : (1 : 𝓞 E) ∈ w ⊔ J`. Rewrite using `[hsup]`.

Conclude with `Submodule.mem_top`. Take `⟨x, hx, ε, hε, hxε⟩` from `Submodule.mem_sup.mp h1`. Establish `hε1 : ε - 1 ∈ w`. Establish `heq : ε - 1 = -x`. Rewrite using `[← hxε]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Conclude with `w.neg_mem hx`. Establish `hεw : ε ∉ w` using `fun h => hwtop ((Ideal.eq_top_iff_one w).mpr (by`. Establish `h2` using `w.sub_mem h hε1`.

Simplify using `using h2))`. Establish `hmemI : ∀ b, (p : 𝓞 E) ∣ b ↔ b ∈ w * J`. Introduce `b`. Rewrite using `[← Ideal.mem_span_singleton, hJ]`. Use `⟨ε, hε1, ?_, ?_, ?_, PositivityTheory.HtPt.Gsplit.coprime_different E p hp hd⟩` and prove the remaining obligations.

Introduce `w' hw' hpw' hne`. Establish `hle : w * J ≤ w'`. Rewrite using `[← hJ, Ideal.span_singleton_le_iff_mem]`. Conclude with `hpw'`. Break down `hw'.mul_le.mp hle with h | h` into its components or cases.

Conclude with `absurd (hmax.eq_of_le hw'.ne_top h).symm hne`. Conclude with `h hε`. Introduce `a`. Rewrite using `[hmemI]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `hle' : w * J ≤ w` using `Ideal.mul_le_left`. Establish `hw1 : ε * a ∈ w` using `hle' h`. Break down `hw.mem_or_mem hw1 with h' | h'` into its components or cases. Conclude with `absurd h' hεw`.

Conclude with `h'`. Introduce `ha`. Rewrite using `[mul_comm ε a]`. Conclude with `Ideal.mul_mem_mul ha hε`. Rewrite using `[hmemI]`.

Establish `heq : ε * ε - ε = (ε - 1) * ε` using `by ring`. Rewrite using `[heq]`. Conclude with `Ideal.mul_mem_mul hε1 hε`.
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
