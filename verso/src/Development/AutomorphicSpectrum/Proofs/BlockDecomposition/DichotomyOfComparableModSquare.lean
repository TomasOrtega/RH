import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisibilityChainPowerFactorization

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.DichMod

variable {S : Type} [CommRing S]

/- English proof (translation)
Establish `h` using `Ideal.mem_jacobson_bot.mp hJ (-w)`. Establish `e : ϖ * -w + 1 = 1 - w * ϖ` using `by ring`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem isUnit_one_sub_mul {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) (w : S) :
    IsUnit (1 - w * ϖ) := by
  have h := Ideal.mem_jacobson_bot.mp hJ (-w)
  have e : ϖ * -w + 1 = 1 - w * ϖ := by ring
  rwa [e] at h

/- English proof (translation)
Break down `hc f ϖ with h | h` into its components or cases. Use `left`. Take `⟨c, d, e⟩` from `Ideal.mem_span_pair.mp h`. Conclude with `⟨c + d * ϖ, by rw [← e]; ring⟩`. Use `right`.

Take `⟨c, w, e⟩` from `Ideal.mem_span_pair.mp h`. Establish `hu` using `isUnit_one_sub_mul hJ w`. Establish `key : (1 - w * ϖ) * ϖ = c * f`. Establish `: c * f = ϖ - w * ϖ ^ 2` using `by linear_combination e`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `hu.dvd_mul_left.mp (key ▸ dvd_mul_left f c)`.
-/
theorem dvd_or_dvd {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson)
    (hc : ∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) (f : S) :
    ϖ ∣ f ∨ f ∣ ϖ := by
  rcases hc f ϖ with h | h
  · left
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    exact ⟨c + d * ϖ, by rw [← e]; ring⟩
  · right
    obtain ⟨c, w, e⟩ := Ideal.mem_span_pair.mp h
    have hu := isUnit_one_sub_mul hJ w
    have key : (1 - w * ϖ) * ϖ = c * f := by
      have : c * f = ϖ - w * ϖ ^ 2 := by linear_combination e
      rw [this]; ring
    exact hu.dvd_mul_left.mp (key ▸ dvd_mul_left f c)

/- English proof (translation)
Break down `hc f g with h | h` into its components or cases. Use `left`. Take `⟨c, d, e⟩` from `Ideal.mem_span_pair.mp h`. Rewrite using `[← e]`. Conclude with `dvd_add (dvd_mul_left g c) ((hg.trans (dvd_pow_self ϖ two_ne_zero)).mul_left d)`.

Use `right`. Take `⟨c, d, e⟩` from `Ideal.mem_span_pair.mp h`. Rewrite using `[← e]`. Conclude with `dvd_add (dvd_mul_left f c) ((hf.trans (dvd_pow_self ϖ two_ne_zero)).mul_left d)`.
-/
theorem comparable {ϖ : S}
    (hc : ∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) {f g : S}
    (hf : f ∣ ϖ) (hg : g ∣ ϖ) : g ∣ f ∨ f ∣ g := by
  rcases hc f g with h | h
  · left
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    rw [← e]
    exact dvd_add (dvd_mul_left g c) ((hg.trans (dvd_pow_self ϖ two_ne_zero)).mul_left d)
  · right
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    rw [← e]
    exact dvd_add (dvd_mul_left f c) ((hf.trans (dvd_pow_self ϖ two_ne_zero)).mul_left d)

/- English proof (translation)
Take `⟨t, ht⟩` from `h`. Establish `hu` using `isUnit_one_sub_mul hJ (a * t)`. Establish `key : (1 - a * t * ϖ) * ϖ ^ N = b * g`. Establish `: b * g = ϖ ^ N - a * f` using `by linear_combination e`. Rewrite using `[this, ht]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hg : g ∣ ϖ ^ N` using `hu.dvd_mul_left.mp (key ▸ dvd_mul_left g b)`. Conclude with `hg.trans ⟨ϖ * t, by rw [ht]; ring⟩`.
-/
theorem dvd_of_high {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) {f g a b : S} {N : ℕ}
    (e : a * f + b * g = ϖ ^ N) (h : ϖ ^ (N + 1) ∣ f) : g ∣ f := by
  obtain ⟨t, ht⟩ := h
  have hu := isUnit_one_sub_mul hJ (a * t)
  have key : (1 - a * t * ϖ) * ϖ ^ N = b * g := by
    have : b * g = ϖ ^ N - a * f := by linear_combination e
    rw [this, ht]; ring
  have hg : g ∣ ϖ ^ N := hu.dvd_mul_left.mp (key ▸ dvd_mul_left g b)
  exact hg.trans ⟨ϖ * t, by rw [ht]; ring⟩

/- English proof (translation)
Establish `h1 : f ∣ ϖ ^ (i + 1)`. Rewrite using `[hf, pow_succ]`. Conclude with `mul_dvd_mul_left _ hf'`. Establish `h2 : ϖ ^ (i + 1) ∣ g`. Rewrite using `[hg]`.

Conclude with `(pow_dvd_pow ϖ hij).mul_right g'`. Conclude with `h1.trans h2`.
-/
theorem dvd_of_lt {ϖ f g f' g' : S} {i j : ℕ} (hf : f = ϖ ^ i * f') (hg : g = ϖ ^ j * g')
    (hf' : f' ∣ ϖ) (hij : i < j) : f ∣ g := by
  have h1 : f ∣ ϖ ^ (i + 1) := by
    rw [hf, pow_succ]
    exact mul_dvd_mul_left _ hf'
  have h2 : ϖ ^ (i + 1) ∣ g := by
    rw [hg]
    exact (pow_dvd_pow ϖ hij).mul_right g'
  exact h1.trans h2

/- English proof (translation)
Introduce `S _ ϖ hJ hc f g hN`. Take `⟨N, hN⟩` from `hN`. Take `⟨a, b, e⟩` from `Ideal.mem_span_pair.mp hN`. Establish `hd` using `dvd_or_dvd hJ hc`. Break down `GlobalTheory.CompanionTheory.NormalForm.normal_form_of_dichotomy ϖ hd f (N + 1) with hf | ⟨i, f', hf, hf'⟩` into its components or cases.

Conclude with `Or.inl (dvd_of_high hJ e hf)`. Break down `GlobalTheory.CompanionTheory.NormalForm.normal_form_of_dichotomy ϖ hd g (N + 1) with hg | ⟨j, g', hg, hg'⟩` into its components or cases. Conclude with `Or.inr (dvd_of_high hJ (by rw [add_comm]; exact e) hg)`. Break down `lt_trichotomy i j with hij | hij | hij` into its components or cases. Conclude with `Or.inr (dvd_of_lt hf hg hf' hij)`.

Substitute `hij` using the available equality. Rewrite using `[hf, hg]`. Break down `comparable hc hf' hg' with h | h` into its components or cases. Conclude with `Or.inl (mul_dvd_mul_left _ h)`. Conclude with `Or.inr (mul_dvd_mul_left _ h)`.

Conclude with `Or.inl (dvd_of_lt hg hf hg' hij)`.
-/
theorem dich_of_mod : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson →
    (∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) → Dich ϖ := by
  intro S _ ϖ hJ hc f g hN
  obtain ⟨N, hN⟩ := hN
  obtain ⟨a, b, e⟩ := Ideal.mem_span_pair.mp hN
  have hd := dvd_or_dvd hJ hc
  rcases GlobalTheory.CompanionTheory.NormalForm.normal_form_of_dichotomy ϖ hd f (N + 1) with hf | ⟨i, f', hf, hf'⟩
  · exact Or.inl (dvd_of_high hJ e hf)
  rcases GlobalTheory.CompanionTheory.NormalForm.normal_form_of_dichotomy ϖ hd g (N + 1) with hg | ⟨j, g', hg, hg'⟩
  · exact Or.inr (dvd_of_high hJ (by rw [add_comm]; exact e) hg)
  rcases lt_trichotomy i j with hij | hij | hij
  · exact Or.inr (dvd_of_lt hf hg hf' hij)
  · subst hij
    rw [hf, hg]
    rcases comparable hc hf' hg' with h | h
    · exact Or.inl (mul_dvd_mul_left _ h)
    · exact Or.inr (mul_dvd_mul_left _ h)
  · exact Or.inl (dvd_of_lt hg hf hg' hij)

end GlobalTheory.CompanionTheory.DichMod
