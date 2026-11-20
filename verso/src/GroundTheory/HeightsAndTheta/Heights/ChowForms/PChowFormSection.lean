import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {F : Type*} [Field F] {n : ℕ}

/- English proof (translation)
Simplify using `[incIdeal, Submodule.mem_iInf, RingHom.mem_ker]`.
-/
theorem mem_incIdeal_iff {P : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {g : MvPolynomial (Fin k × Fin n) F} :
    g ∈ incIdeal P k ↔ ∀ v ∈ incidence P k, aeval v g = 0 := by
  simp [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, h⟩`. Use `⟨h0, ?_⟩` and prove the remaining obligations. Use extensionality with `G`. Rewrite using `[mem_incIdeal_iff, Ideal.mem_span_singleton]`.

Conclude with `h G`. Introduce and unpack `⟨h0, h⟩`. Use `⟨h0, fun G => ?_⟩` and prove the remaining obligations. Rewrite using `[← mem_incIdeal_iff, h, Ideal.mem_span_singleton]`.
-/
theorem isChowForm_iff {P : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {g : MvPolynomial (Fin k × Fin n) F} :
    IsChowForm P k g ↔ g ≠ 0 ∧ incIdeal P k = Ideal.span {g} := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    ext G
    rw [mem_incIdeal_iff, Ideal.mem_span_singleton]
    exact h G
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun G => ?_⟩
    rw [← mem_incIdeal_iff, h, Ideal.mem_span_singleton]

/- English proof (translation)
Proceed by induction on `a using UniqueFactorizationMonoid.induction_on_prime generalizing b with`. Consider the case `h₁ => exact absurd rfl ha`. Consider the case `h₂ x hx => exact hx.dvd`. Consider the case `h₃ a p ha' hp ih`. Establish `hpp : emultiplicity p p = 1` using `(FiniteMultiplicity.of_not_isUnit hp.not_isUnit hp.ne_zero).emultiplicity_self`.

Establish `hpb : p ∣ b`. Apply `dvd_of_emultiplicity_pos` to reduce the goal to its premises. Use `h p hp.irreducible` as an intermediate fact. Rewrite `this` using `[emultiplicity_mul hp, hpp]`. Conclude with `lt_of_lt_of_le (by simp) this`.

Take `⟨b', rfl⟩` from `hpb`. Establish `hb' : b' ≠ 0` using `right_ne_zero_of_mul hb`. Use `mul_dvd_mul_left p (ih ha' hb' fun q hq => ?_)` and prove the remaining obligations. Establish `hqp : Prime q` using `hq.prime`. Establish `hfin : emultiplicity q p ≠ ⊤`.

Rewrite using `[Ne, emultiplicity_eq_top, not_not]`. Conclude with `FiniteMultiplicity.of_not_isUnit hqp.not_isUnit hp.ne_zero`. Use `h q hq` as an intermediate fact. Rewrite `this` using `[emultiplicity_mul hqp, emultiplicity_mul hqp]`. Conclude with `(WithTop.add_le_add_iff_left hfin).mp this`.
-/
theorem dvd_of_forall_emultiplicity_le {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p, Irreducible p → emultiplicity p a ≤ emultiplicity p b) : a ∣ b := by
  induction a using UniqueFactorizationMonoid.induction_on_prime generalizing b with
  | h₁ => exact absurd rfl ha
  | h₂ x hx => exact hx.dvd
  | h₃ a p ha' hp ih =>
    have hpp : emultiplicity p p = 1 :=
      (FiniteMultiplicity.of_not_isUnit hp.not_isUnit hp.ne_zero).emultiplicity_self
    have hpb : p ∣ b := by
      apply dvd_of_emultiplicity_pos
      have := h p hp.irreducible
      rw [emultiplicity_mul hp, hpp] at this
      exact lt_of_lt_of_le (by simp) this
    obtain ⟨b', rfl⟩ := hpb
    have hb' : b' ≠ 0 := right_ne_zero_of_mul hb
    refine mul_dvd_mul_left p (ih ha' hb' fun q hq => ?_)
    have hqp : Prime q := hq.prime
    have hfin : emultiplicity q p ≠ ⊤ := by
      rw [Ne, emultiplicity_eq_top, not_not]
      exact FiniteMultiplicity.of_not_isUnit hqp.not_isUnit hp.ne_zero
    have := h q hq
    rw [emultiplicity_mul hqp, emultiplicity_mul hqp] at this
    exact (WithTop.add_le_add_iff_left hfin).mp this

/- English proof (translation)
Introduce `F _ _ n e I f u hI hf hu`. Take `⟨hh0, hord⟩` from `h₅ F n e I f u hI hf hu`. Establish `hdim` using `h₁ F n (e + 1) I f hI hf`. Establish `hcomp : ∀ W ∈ (divCycle I u).support, W ∈ relComps (I ⊔ Ideal.span {linForm u})`. Introduce `W hW`.

Rewrite `hW` using `[Finsupp.mem_support_iff]`. Assume the negation of the conclusion as `h`. Conclude with `hW (by simp [divCycle, fundCycle, Finsupp.onFinset_apply, h])`. Establish `hW1 : ∀ W ∈ (divCycle I u).support, IsProjPrime W ∧ ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞)` using `fun W hW => h₂ F n e I W u hI hdim hu (hcomp W hW)`. Establish `hex : ∀ W ∈ (divCycle I u).support, ∃ g, IsChowForm W e g` using `fun W hW => h₃ F n e W (hW1 W hW).1 (hW1 W hW).2`.

Set `g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin e × Fin n) F` to `fun W => if h : ∃ g, IsChowForm W e g then h.choose else 1`. Establish `hg : ∀ W ∈ (divCycle I u).support, IsChowForm W e (g W)` using `fun W hW => by`. Simplify using `only [g, dif_pos (hex W hW)]`. Conclude with `(hex W hW).choose_spec`. Establish `hspan : ∀ W ∈ (divCycle I u).support, incIdeal W e = Ideal.span {g W}` using `fun W hW => (isChowForm_iff.mp (hg W hW)).2`.

Establish `hgprime : ∀ W ∈ (divCycle I u).support, Prime (g W)`. Introduce `W hW`. Establish `hp` using `h₄ F n e W (hW1 W hW).1.isPrime (hW1 W hW).1.isRelevant`. Rewrite `hp` using `[hspan W hW]`. Conclude with `(Ideal.span_singleton_prime (isChowForm_iff.mp (hg W hW)).1).mp hp`.

Use `set Pr := ∏ W ∈ (divCycle I u).support, g W ^ (divCycle I u) W with hPr`. Establish `hPr0 : Pr ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hgprime W hW).ne_zero`. Establish `hmult : ∀ q, Irreducible q → emultiplicity q Pr = emultiplicity q (specFirst f u)`. Introduce `q hq`. Establish `hqp : Prime q` using `hq.prime`.

Rewrite using `[hord q hq, hPr, Finset.emultiplicity_prod hqp, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun W hW => ?_` and prove the remaining obligations. Rewrite using `[emultiplicity_pow hqp]`. Use `split_ifs with hs`. Establish `hass : Associated q (g W)`.

Rewrite using `[← Ideal.span_singleton_eq_span_singleton, hs, hspan W hW]`. Rewrite using `[← emultiplicity_eq_of_associated_left hass, (FiniteMultiplicity.of_not_isUnit (hgprime W hW).not_isUnit (hgprime W hW).ne_zero).emultiplicity_self, mul_one]`. Establish `: emultiplicity q (g W) = 0`. Rewrite using `[emultiplicity_eq_zero]`. Introduce `hdvd`.

Apply `hs` to reduce the goal to its premises. Rewrite using `[hspan W hW, Ideal.span_singleton_eq_span_singleton]`. Conclude with `hq.associated_of_dvd (hgprime W hW).irreducible hdvd`. Rewrite using `[this, mul_zero]`. Establish `hass : Associated Pr (specFirst f u)` using `associated_of_dvd_dvd (dvd_of_forall_emultiplicity_le hPr0 hh0 fun q hq => (hmult q hq).le) (dvd_of_forall_emultiplicity_le hh0 hPr0 fun q hq => (hmult q hq).ge)`.

Take `⟨v, hv⟩` from `hass`. Take `⟨c, hc, hvc⟩` from `(isUnit_iff_eq_C_of_isReduced (P := (v : MvPolynomial (Fin e × Fin n) F))).mp v.isUnit`. Use `⟨c, hc.ne_zero, g, hg, ?_⟩` and prove the remaining obligations. Rewrite using `[← hv, hvc, mul_comm]`.
-/
theorem ChowFormSection.proof (h₁ : ConeDimOfChowForm.Statement) (h₂ : ConeDimComponent.Statement)
    (h₃ : ChowFormExists.Statement) (h₄ : IncIdealPrime.Statement) (h₅ : SectionOrder.Statement) :
    ChowFormSection.Statement := by
  intro F _ _ n e I f u hI hf hu
  classical
  obtain ⟨hh0, hord⟩ := h₅ F n e I f u hI hf hu
  have hdim := h₁ F n (e + 1) I f hI hf
  have hcomp : ∀ W ∈ (divCycle I u).support, W ∈ relComps (I ⊔ Ideal.span {linForm u}) := by
    intro W hW
    rw [Finsupp.mem_support_iff] at hW
    by_contra h
    exact hW (by simp [divCycle, fundCycle, Finsupp.onFinset_apply, h])
  have hW1 : ∀ W ∈ (divCycle I u).support, IsProjPrime W ∧
      ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := fun W hW =>
    h₂ F n e I W u hI hdim hu (hcomp W hW)
  have hex : ∀ W ∈ (divCycle I u).support, ∃ g, IsChowForm W e g := fun W hW =>
    h₃ F n e W (hW1 W hW).1 (hW1 W hW).2
  let g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin e × Fin n) F :=
    fun W => if h : ∃ g, IsChowForm W e g then h.choose else 1
  have hg : ∀ W ∈ (divCycle I u).support, IsChowForm W e (g W) := fun W hW => by
    simp only [g, dif_pos (hex W hW)]
    exact (hex W hW).choose_spec
  have hspan : ∀ W ∈ (divCycle I u).support, incIdeal W e = Ideal.span {g W} := fun W hW =>
    (isChowForm_iff.mp (hg W hW)).2
  have hgprime : ∀ W ∈ (divCycle I u).support, Prime (g W) := by
    intro W hW
    have hp := h₄ F n e W (hW1 W hW).1.isPrime (hW1 W hW).1.isRelevant
    rw [hspan W hW] at hp
    exact (Ideal.span_singleton_prime (isChowForm_iff.mp (hg W hW)).1).mp hp
  set Pr := ∏ W ∈ (divCycle I u).support, g W ^ (divCycle I u) W with hPr
  have hPr0 : Pr ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hgprime W hW).ne_zero
  have hmult : ∀ q, Irreducible q → emultiplicity q Pr = emultiplicity q (specFirst f u) := by
    intro q hq
    have hqp : Prime q := hq.prime
    rw [hord q hq, hPr, Finset.emultiplicity_prod hqp, Finset.sum_filter]
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [emultiplicity_pow hqp]
    split_ifs with hs
    · have hass : Associated q (g W) := by
        rw [← Ideal.span_singleton_eq_span_singleton, hs, hspan W hW]
      rw [← emultiplicity_eq_of_associated_left hass,
        (FiniteMultiplicity.of_not_isUnit (hgprime W hW).not_isUnit (hgprime W hW).ne_zero).emultiplicity_self,
        mul_one]
    · have : emultiplicity q (g W) = 0 := by
        rw [emultiplicity_eq_zero]
        intro hdvd
        apply hs
        rw [hspan W hW, Ideal.span_singleton_eq_span_singleton]
        exact hq.associated_of_dvd (hgprime W hW).irreducible hdvd
      rw [this, mul_zero]
  have hass : Associated Pr (specFirst f u) :=
    associated_of_dvd_dvd
      (dvd_of_forall_emultiplicity_le hPr0 hh0 fun q hq => (hmult q hq).le)
      (dvd_of_forall_emultiplicity_le hh0 hPr0 fun q hq => (hmult q hq).ge)
  obtain ⟨v, hv⟩ := hass
  obtain ⟨c, hc, hvc⟩ := (isUnit_iff_eq_C_of_isReduced (P := (v : MvPolynomial (Fin e × Fin n) F))).mp
    v.isUnit
  refine ⟨c, hc.ne_zero, g, hg, ?_⟩
  rw [← hv, hvc, mul_comm]

end

end GroundTheory.Heights₂.Heights
