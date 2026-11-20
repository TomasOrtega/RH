import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicThreeRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivWeierstrassPAddHalfPeriodStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

/- English proof (translation)
Introduce `L a b t ha hb hc h2a h2b h2t`. Establish `h2c : 2 * (a + b) ∈ L.lattice`. Rewrite using `[mul_add]`. Conclude with `L.lattice.add_mem h2a h2b`. Establish `hshift : ∀ u : ℂ, 2 * u ∈ L.lattice → t + u ∉ L.lattice`.

Introduce `u hu htu`. Apply `h2t` to reduce the goal to its premises. Use `L.lattice.sub_mem (L.lattice.add_mem htu htu) hu` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `ht : t ∉ L.lattice` using `by simpa using hshift 0 (by simp)`. Establish `hroot : ∀ u : ℂ, u ∉ L.lattice → 2 * u ∈ L.lattice → 4 * L.weierstrassP u ^ 3 - L.g₂ * L.weierstrassP u - L.g₃ = 0`. Introduce `u hu h2u`. Rewrite using `[← L.derivWeierstrassP_sq u hu, (derivWeierstrassP_eq_zero_iff L hu).2 (by rwa [← two_mul])]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hne : ∀ u v : ℂ, u ∉ L.lattice → v ∉ L.lattice → 2 * v ∈ L.lattice → u + v ∉ L.lattice → L.weierstrassP u ≠ L.weierstrassP v`. Introduce `u v hu hv h2v huv h`. Break down `(weierstrassP_eq_iff L hu hv).1 h with h' | h'` into its components or cases. Apply `huv` to reduce the goal to its premises. Use `L.lattice.add_mem h' h2v` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Conclude with `huv h'`. Establish `h12` using `hne a b ha hb h2b hc`. Establish `h13` using `hne a (a + b) ha hc h2c (by`.

Introduce `h`. Apply `hb` to reduce the goal to its premises. Use `L.lattice.sub_mem h h2a` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use the proof step `ring)`.

Establish `h23` using `hne b (a + b) hb hc h2c (by`. Introduce `h`. Apply `ha` to reduce the goal to its premises. Use `L.lattice.sub_mem h h2b` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use the proof step `ring)`. Take `⟨hfac, hdisc⟩` from `GlobalTheory.T.cubic_factor_and_discriminant_of_three_distinct_roots L.g₂ L.g₃ _ _ _ (hroot a ha h2a) (hroot b hb h2b) (hroot _ hc h2c) h12 h13 h23`. Establish `e1` using `GlobalTheory.T.derivWeierstrassP_add_half_period' L a t ha h2a ht (hshift a h2a)`. Establish `e2` using `GlobalTheory.T.derivWeierstrassP_add_half_period' L b t hb h2b ht (hshift b h2b)`. Establish `e3` using `GlobalTheory.T.derivWeierstrassP_add_half_period' L (a + b) t hc h2c ht (hshift _ h2c)`.

Establish `hsq` using `L.derivWeierstrassP_sq t ht`. Rewrite `hsq` using `[hfac]`. Establish `hd : L.derivWeierstrassP t ≠ 0` using `fun h => h2t (by rw [two_mul]; exact (derivWeierstrassP_eq_zero_iff L ht).1 h)`. Rewrite using `[latticeCurve_Δ]`. Generalize the expression as in `L.derivWeierstrassP t = d at *`.

Generalize the expression as in `L.derivWeierstrassP (t + a) = d₁ at *`. Generalize the expression as in `L.derivWeierstrassP (t + b) = d₂ at *`. Generalize the expression as in `L.derivWeierstrassP (t + (a + b)) = d₃ at *`. Generalize the expression as in `L.weierstrassP t = x at *`. Generalize the expression as in `L.weierstrassP a = e₁ at *`.

Generalize the expression as in `L.weierstrassP b = e₂ at *`. Generalize the expression as in `L.weierstrassP (a + b) = e₃ at *`. Apply `mul_left_cancel₀ (pow_ne_zero 3 hd)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsq]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = -(16 * ((3 * e₁ ^ 2 - L.g₂ / 4) * (3 * e₂ ^ 2 - L.g₂ / 4) * (3 * e₃ ^ 2 - L.g₂ / 4))) * d ^ 3 := by`. Rewrite using `[e1, e2, e3]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = d ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by rw [hdisc]; ring`.
-/
theorem prod_derivWeierstrassP_translates_eq_Δ : ∀ (L : PeriodPair) (a b t : ℂ),
    a ∉ L.lattice → b ∉ L.lattice → a + b ∉ L.lattice → 2 * a ∈ L.lattice →
    2 * b ∈ L.lattice → 2 * t ∉ L.lattice →
    L.derivWeierstrassP t * L.derivWeierstrassP (t + a) * L.derivWeierstrassP (t + b) *
      L.derivWeierstrassP (t + (a + b)) = (latticeCurve L).Δ := by
  intro L a b t ha hb hc h2a h2b h2t
  have h2c : 2 * (a + b) ∈ L.lattice := by
    rw [mul_add]; exact L.lattice.add_mem h2a h2b
  have hshift : ∀ u : ℂ, 2 * u ∈ L.lattice → t + u ∉ L.lattice := by
    intro u hu htu
    apply h2t
    have := L.lattice.sub_mem (L.lattice.add_mem htu htu) hu
    convert this using 1; ring
  have ht : t ∉ L.lattice := by simpa using hshift 0 (by simp)
  have hroot : ∀ u : ℂ, u ∉ L.lattice → 2 * u ∈ L.lattice →
      4 * L.weierstrassP u ^ 3 - L.g₂ * L.weierstrassP u - L.g₃ = 0 := by
    intro u hu h2u
    rw [← L.derivWeierstrassP_sq u hu,
      (derivWeierstrassP_eq_zero_iff L hu).2 (by rwa [← two_mul])]
    ring
  have hne : ∀ u v : ℂ, u ∉ L.lattice → v ∉ L.lattice → 2 * v ∈ L.lattice →
      u + v ∉ L.lattice → L.weierstrassP u ≠ L.weierstrassP v := by
    intro u v hu hv h2v huv h
    rcases (weierstrassP_eq_iff L hu hv).1 h with h' | h'
    · apply huv
      have := L.lattice.add_mem h' h2v
      convert this using 1; ring
    · exact huv h'
  have h12 := hne a b ha hb h2b hc
  have h13 := hne a (a + b) ha hc h2c (by
    intro h; apply hb
    have := L.lattice.sub_mem h h2a
    convert this using 1; ring)
  have h23 := hne b (a + b) hb hc h2c (by
    intro h; apply ha
    have := L.lattice.sub_mem h h2b
    convert this using 1; ring)
  obtain ⟨hfac, hdisc⟩ := GlobalTheory.T.cubic_factor_and_discriminant_of_three_distinct_roots L.g₂ L.g₃ _ _ _ (hroot a ha h2a) (hroot b hb h2b)
    (hroot _ hc h2c) h12 h13 h23
  have e1 := GlobalTheory.T.derivWeierstrassP_add_half_period' L a t ha h2a ht (hshift a h2a)
  have e2 := GlobalTheory.T.derivWeierstrassP_add_half_period' L b t hb h2b ht (hshift b h2b)
  have e3 := GlobalTheory.T.derivWeierstrassP_add_half_period' L (a + b) t hc h2c ht (hshift _ h2c)
  have hsq := L.derivWeierstrassP_sq t ht
  rw [hfac] at hsq
  have hd : L.derivWeierstrassP t ≠ 0 := fun h =>
    h2t (by rw [two_mul]; exact (derivWeierstrassP_eq_zero_iff L ht).1 h)
  rw [latticeCurve_Δ]
  generalize L.derivWeierstrassP t = d at *
  generalize L.derivWeierstrassP (t + a) = d₁ at *
  generalize L.derivWeierstrassP (t + b) = d₂ at *
  generalize L.derivWeierstrassP (t + (a + b)) = d₃ at *
  generalize L.weierstrassP t = x at *
  generalize L.weierstrassP a = e₁ at *
  generalize L.weierstrassP b = e₂ at *
  generalize L.weierstrassP (a + b) = e₃ at *
  apply mul_left_cancel₀ (pow_ne_zero 3 hd)
  calc d ^ 3 * (d * d₁ * d₂ * d₃) = (d ^ 2) ^ 2 * (d₁ * d₂ * d₃) := by ring
    _ = 16 * ((d₁ * (x - e₁) ^ 2) * (d₂ * (x - e₂) ^ 2) * (d₃ * (x - e₃) ^ 2)) := by
        rw [hsq]; ring
    _ = -(16 * ((3 * e₁ ^ 2 - L.g₂ / 4) * (3 * e₂ ^ 2 - L.g₂ / 4) *
          (3 * e₃ ^ 2 - L.g₂ / 4))) * d ^ 3 := by
        rw [e1, e2, e3]; ring
    _ = d ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by rw [hdisc]; ring

end GlobalTheory.CMModel
