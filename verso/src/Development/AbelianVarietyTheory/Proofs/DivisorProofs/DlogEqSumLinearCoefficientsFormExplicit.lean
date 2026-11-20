import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.Chart

open GlobalTheory.PDiv

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ}

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, α i ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h (Finsupp.ext hc)`. Establish `hle : Finsupp.single i 1 ≤ α`.

Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [Finsupp.single_eq_same]`. Use linear arithmetic over natural numbers and integers.

Simplify using `[Finsupp.single_apply, Ne.symm hj]`. Use `⟨i, α - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← tsub_add_cancel_of_le hle]`. Rewrite using `[map_add, Finsupp.degree_single]`.
-/
theorem exists_eq_add_single {α : Fin d →₀ ℕ} (h : α ≠ 0) :
    ∃ (i : Fin d) (β : Fin d →₀ ℕ), α = β + Finsupp.single i 1 ∧ α.degree = β.degree + 1 := by
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (Finsupp.ext hc)
  have hle : Finsupp.single i 1 ≤ α := by
    intro j
    by_cases hj : j = i
    · subst hj; simp only [Finsupp.single_eq_same]; omega
    · simp [Finsupp.single_apply, Ne.symm hj]
  refine ⟨i, α - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm, ?_⟩
  conv_lhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add, Finsupp.degree_single]

variable (c : Chart G d)

/- English proof (translation)
Take `⟨i, γ, rfl, -⟩` from `exists_eq_add_single hβ`. Rewrite using `[← mul_one a, ← monomial_mul_monomial, map_mul, map_mul]`. Express the relevant statement in the definitionally equal form `_ * Bialgebra.counitAlgHom O (G.A n) (c.ev n (X i)) = 0`. Rewrite using `[(c.isEval n).1 i, Bialgebra.counitAlgHom_apply O (G.A n) (c.x n i), c.aug, mul_zero]`.
-/
theorem counit_ev_monomial (n : ℕ) {β : Fin d →₀ ℕ} (hβ : β ≠ 0) (a : O) :
    Bialgebra.counitAlgHom O (G.A n) (c.ev n (monomial β a)) = 0 := by
  obtain ⟨i, γ, rfl, -⟩ := exists_eq_add_single hβ
  rw [← mul_one a, ← monomial_mul_monomial, map_mul, map_mul]
  change _ * Bialgebra.counitAlgHom O (G.A n) (c.ev n (X i)) = 0
  rw [(c.isEval n).1 i, Bialgebra.counitAlgHom_apply O (G.A n) (c.x n i), c.aug, mul_zero]

/- English proof (translation)
Establish `h0 : α ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hα`. Take `⟨i, β, rfl, hdeg⟩` from `exists_eq_add_single h0`. Establish `hβ : β ≠ 0`.

Establish `hb : β.degree ≠ 0` using `by omega`. Conclude with `fun h => hb (by rw [h]; simp)`. Rewrite using `[← mul_one a, ← monomial_mul_monomial, map_mul, dUnit, AugCot.d_mul, c.counit_ev_monomial n hβ]`. Express the relevant statement in the definitionally equal form `_ • _ + Bialgebra.counitAlgHom O (G.A n) (c.ev n (X i)) • _ = 0`. Rewrite using `[(c.isEval n).1 i, Bialgebra.counitAlgHom_apply O (G.A n) (c.x n i), c.aug, zero_smul, zero_smul, add_zero]`.
-/
theorem dUnit_ev_monomial (n : ℕ) {α : Fin d →₀ ℕ} (hα : 2 ≤ α.degree) (a : O) :
    dUnit O (c.ev n (monomial α a)) = 0 := by
  have h0 : α ≠ 0 := by
    rintro rfl
    simp at hα
  obtain ⟨i, β, rfl, hdeg⟩ := exists_eq_add_single h0
  have hβ : β ≠ 0 := by
    have hb : β.degree ≠ 0 := by omega
    exact fun h => hb (by rw [h]; simp)
  rw [← mul_one a, ← monomial_mul_monomial, map_mul, dUnit, AugCot.d_mul,
    c.counit_ev_monomial n hβ]
  change _ • _ + Bialgebra.counitAlgHom O (G.A n) (c.ev n (X i)) • _ = 0
  rw [(c.isEval n).1 i, Bialgebra.counitAlgHom_apply O (G.A n) (c.x n i), c.aug, zero_smul, zero_smul, add_zero]

/- English proof (translation)
Take `⟨b, hb⟩` from `hN f hf`. Rewrite using `[hb, dUnit, AugCot.d_mul]`. Establish `h1 : ((p : G.A n) ^ n) = algebraMap O (G.A n) ((p : O) ^ n)` using `by simp`. Rewrite using `[h1, AugCot.d_algebraMap, smul_zero, add_zero, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]`. Conclude with `G.pow_smul_cot n _`.
-/
theorem dUnit_ev_of_high (n N : ℕ) (hN : ∀ f : MvPowerSeries (Fin d) O,
    (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) → (p : G.A n) ^ n ∣ c.ev n f)
    (f : MvPowerSeries (Fin d) O) (hf : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) :
    dUnit O (c.ev n f) = 0 := by
  obtain ⟨b, hb⟩ := hN f hf
  rw [hb, dUnit, AugCot.d_mul]
  have h1 : ((p : G.A n) ^ n) = algebraMap O (G.A n) ((p : O) ^ n) := by simp
  rw [h1, AugCot.d_algebraMap, smul_zero, add_zero, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply]
  exact G.pow_smul_cot n _

/- English proof (translation)
Take `⟨N, hN⟩` from `(c.isEval n).2 n`. Use `set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) f with hP`. Establish `hsplit : f = (P : MvPowerSeries (Fin d) O) + (f - P)` using `by ring`. Rewrite using `[hsplit, map_add, dUnit, map_add, ← dUnit, ← dUnit]`. Rewrite using `[c.dUnit_ev_of_high n N hN (f - P) fun α hα => ?_, add_zero]`.

Rewrite using `[MvPolynomial.as_sum P]`. Establish `: ((∑ v ∈ P.support, MvPolynomial.monomial v (MvPolynomial.coeff v P) : MvPolynomial (Fin d) O) : MvPowerSeries (Fin d) O) = ∑ v ∈ P.support, monomial v (MvPolynomial.coeff v P)`. Rewrite using `[← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]`. Simplify using `only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]`. Rewrite using `[this, map_sum, dUnit, map_sum]`.

Use `Finset.sum_eq_zero fun v hv => ?_` and prove the remaining obligations. Establish `hv' : MvPolynomial.coeff v P ≠ 0` using `MvPolynomial.mem_support_iff.1 hv`. Establish `h2 : 2 ≤ v.degree`. Assume the negation of the conclusion as `hc`. Apply `hv'` to reduce the goal to its premises.

Rewrite using `[hP, coeff_trunc']`. Use `split_ifs`. Conclude with `hf v (by omega)`. Both sides reduce to the same expression. Conclude with `c.dUnit_ev_monomial n h2 _`.

Rewrite using `[map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos, sub_self]`. Introduce `j`. Conclude with `((Finsupp.le_degree j α).trans hα.le)`.
-/
theorem dUnit_ev_of_two (n : ℕ) (f : MvPowerSeries (Fin d) O)
    (hf : ∀ α : Fin d →₀ ℕ, α.degree ≤ 1 → coeff α f = 0) : dUnit O (c.ev n f) = 0 := by
  obtain ⟨N, hN⟩ := (c.isEval n).2 n
  classical
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) f with hP
  have hsplit : f = (P : MvPowerSeries (Fin d) O) + (f - P) := by ring
  rw [hsplit, map_add, dUnit, map_add, ← dUnit, ← dUnit]
  rw [c.dUnit_ev_of_high n N hN (f - P) fun α hα => ?_, add_zero]
  · rw [MvPolynomial.as_sum P]
    have : ((∑ v ∈ P.support, MvPolynomial.monomial v (MvPolynomial.coeff v P) :
        MvPolynomial (Fin d) O) : MvPowerSeries (Fin d) O) =
        ∑ v ∈ P.support, monomial v (MvPolynomial.coeff v P) := by
      rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
      simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]
    rw [this, map_sum, dUnit, map_sum]
    refine Finset.sum_eq_zero fun v hv => ?_
    have hv' : MvPolynomial.coeff v P ≠ 0 := MvPolynomial.mem_support_iff.1 hv
    have h2 : 2 ≤ v.degree := by
      by_contra hc
      apply hv'
      rw [hP, coeff_trunc']
      split_ifs
      · exact hf v (by omega)
      · rfl
    exact c.dUnit_ev_monomial n h2 _
  · rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos, sub_self]
    intro j
    exact ((Finsupp.le_degree j α).trans hα.le)

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `n`. Rewrite using `[Submodule.coe_sum, Finset.sum_apply, dlog_val, ← hu n]`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply]`. Use `set g : MvPowerSeries (Fin d) O := ∑ i, lin u i • X i with hg`.

Establish `hsplit : u = 1 + g + (u - 1 - g)` using `by ring`. Establish `hev : c.ev n g = ∑ i, lin u i • c.x n i`. Rewrite using `[hg, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, (c.isEval n).1 i]`.

Establish `e1 : dUnit O (c.ev n u) = dUnit O (c.ev n 1) + dUnit O (c.ev n g) + dUnit O (c.ev n (u - 1 - g))` using `by conv_lhs => rw [hsplit]`. Simplify using `only [PDiv.dUnit, map_add]`. Rewrite using `[e1, c.dUnit_ev_of_two n (u - 1 - g) ?_, add_zero, map_one, hev]`. Simplify using `only [PDiv.dUnit, AugCot.d_one, zero_add, map_sum, map_smul]`. Both sides reduce to the same expression.

Introduce `α hα`. Establish `hcg : ∀ i, coeff (Finsupp.single i 1) g = lin u i` using `fun i => by`. Rewrite using `[hg, map_sum]`. Simplify using `only [map_smul, coeff_X, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_eq_single i]`.

Simplify using the standard rewrite rules. Introduce `j _ hj`. Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hj ((Finsupp.single_left_inj one_ne_zero).1 h).symm`.

Simplify using the standard rewrite rules. Break down `Nat.le_one_iff_eq_zero_or_eq_one.1 hα with h0 | h1'` into its components or cases. Rewrite using `[(Finsupp.degree_eq_zero_iff α).1 h0]`. Establish `hg0 : coeff 0 g = 0`. Rewrite using `[hg, map_sum]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, coeff_X, if_neg, smul_zero]`. Introduce `h`. Use `congrArg (fun a : Fin d →₀ ℕ => a i) h` as an intermediate fact. Simplify using `at this`.

Rewrite using `[map_sub, map_sub, hg0, coeff_zero_eq_constantCoeff_apply, h1, coeff_zero_eq_constantCoeff_apply, map_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hne : α ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h1'`.

Take `⟨i, β, rfl, hdeg⟩` from `exists_eq_add_single hne`. Establish `hβ : β = 0` using `(Finsupp.degree_eq_zero_iff β).1 (by omega)`. Substitute `hβ` using the available equality. Rewrite using `[zero_add, map_sub, map_sub, hcg, coeff_one, if_neg, sub_zero]`. Conclude with `sub_self _`.

Introduce `h`. Use `congrArg (fun a : Fin d →₀ ℕ => a i) h` as an intermediate fact. Simplify using `at this`.
-/
theorem dlog_eq_sum_lin [Fact p.Prime] (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O)
    (h1 : constantCoeff u = 1) (hu : ∀ n, c.ev n u = charElem χ n) :
    dlog G χ = ∑ i, lin u i • c.form i := by
  classical
  apply Subtype.ext
  funext n
  rw [Submodule.coe_sum, Finset.sum_apply, dlog_val, ← hu n]
  simp only [Submodule.coe_smul, Pi.smul_apply]
  set g : MvPowerSeries (Fin d) O := ∑ i, lin u i • X i with hg
  have hsplit : u = 1 + g + (u - 1 - g) := by ring
  have hev : c.ev n g = ∑ i, lin u i • c.x n i := by
    rw [hg, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, (c.isEval n).1 i]
  have e1 : dUnit O (c.ev n u) = dUnit O (c.ev n 1) + dUnit O (c.ev n g) +
      dUnit O (c.ev n (u - 1 - g)) := by
    conv_lhs => rw [hsplit]
    simp only [PDiv.dUnit, map_add]
  rw [e1, c.dUnit_ev_of_two n (u - 1 - g) ?_, add_zero, map_one, hev]
  · simp only [PDiv.dUnit, AugCot.d_one, zero_add, map_sum, map_smul]
    rfl
  intro α hα
  have hcg : ∀ i, coeff (Finsupp.single i 1) g = lin u i := fun i => by
    rw [hg, map_sum]
    simp only [map_smul, coeff_X, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj ((Finsupp.single_left_inj one_ne_zero).1 h).symm
    · simp
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hα with h0 | h1'
  · rw [(Finsupp.degree_eq_zero_iff α).1 h0]
    have hg0 : coeff 0 g = 0 := by
      rw [hg, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, coeff_X, if_neg, smul_zero]
      intro h
      have := congrArg (fun a : Fin d →₀ ℕ => a i) h
      simp at this
    rw [map_sub, map_sub, hg0, coeff_zero_eq_constantCoeff_apply, h1,
      coeff_zero_eq_constantCoeff_apply, map_one]
    ring
  · have hne : α ≠ 0 := by
      rintro rfl
      simp at h1'
    obtain ⟨i, β, rfl, hdeg⟩ := exists_eq_add_single hne
    have hβ : β = 0 := (Finsupp.degree_eq_zero_iff β).1 (by omega)
    subst hβ
    rw [zero_add, map_sub, map_sub, hcg, coeff_one, if_neg, sub_zero]
    · exact sub_self _
    · intro h
      have := congrArg (fun a : Fin d →₀ ℕ => a i) h
      simp at this

end GlobalTheory.QLog.Chart

namespace GlobalTheory.QLog.Chart

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ c χ u h1 hu` and use `c.dlog_eq_sum_lin χ u h1 hu`.
-/
theorem dlog_eq_sum_lin' : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), constantCoeff u = 1 → (∀ n, c.ev n u = charElem χ n) → dlog G χ = ∑ i, lin u i • c.form i :=
  fun _ _ _ _ _ _ _ _ c χ u h1 hu => c.dlog_eq_sum_lin χ u h1 hu

end GlobalTheory.QLog.Chart
