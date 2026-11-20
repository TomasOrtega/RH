import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.AugNil

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem aeval_mem_span {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {d : ℕ}
    (x : Fin d → A) (P : MvPolynomial (Fin d) R) (h0 : MvPolynomial.constantCoeff P = 0) :
    MvPolynomial.aeval x P ∈ Ideal.span (Set.range x) := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (MvPolynomial.mem_support_iff.1 hm) (by rwa [MvPolynomial.constantCoeff_eq] at h0)
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm0 (Finsupp.ext h)
  refine Ideal.mul_mem_left _ _ ?_
  have hdvd : x i ∣ ∏ j ∈ m.support, x j ^ m j :=
    (dvd_pow_self (x i) hi).trans (Finset.dvd_prod_of_mem _ (Finsupp.mem_support_iff.2 hi))
  obtain ⟨c, hc⟩ := hdvd
  rw [hc]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem dvd_pow_of_mem_span {A : Type} [CommRing A] {d : ℕ} (x : Fin d → A) (p : A) (N₀ : ℕ)
    (hx : ∀ i, p ∣ x i ^ N₀) (a : A) (ha : a ∈ Ideal.span (Set.range x)) :
    p ∣ a ^ (d * N₀ + 1) := by
  obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 ha
  have h := Ideal.sum_pow_mem_span_pow Finset.univ (fun i => r i • x i) N₀
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [← Ideal.mem_span_singleton]
  refine Ideal.span_le.2 ?_ h
  rintro _ ⟨i, -, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_span_singleton]
  simp only [smul_eq_mul, mul_pow]
  exact Dvd.dvd.mul_left ((hx i).trans (pow_dvd_pow _ (Nat.le_succ _))) _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem aug_nil : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d), ∃ N : ℕ, ∀ f : MvPowerSeries (Fin d) O, constantCoeff f = 0 →
      (p : G.A 1) ∣ c.ev 1 f ^ N := by
  intro p O _ G d c
  classical
  choose Ni hNi using c.nil 1
  let N₀ := Finset.univ.sup Ni
  have hx : ∀ i, (p : G.A 1) ∣ c.x 1 i ^ N₀ := fun i =>
    (hNi i).trans (pow_dvd_pow _ (Finset.le_sup (Finset.mem_univ i)))
  obtain ⟨N₁, hN₁⟩ := (c.isEval 1).2 1
  refine ⟨d * N₀ + 1, fun f hf => ?_⟩
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N₁) f with hPdef
  have hR : (p : G.A 1) ∣ c.ev 1 (f - (P : MvPowerSeries (Fin d) O)) := by
    have h := hN₁ (f - P) (fun α hα => ?_)
    · simpa using h
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos, sub_self]
    intro i
    have : α i ≤ α.degree := by
      rw [Finsupp.degree]
      by_cases hi : α i = 0
      · rw [hi]; exact Nat.zero_le _
      · exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finsupp.mem_support_iff.2 hi)
    simpa using this.trans hα.le
  have hP : c.ev 1 (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval (c.x 1) P := by
    have : (c.ev 1).comp (MvPolynomial.coeToMvPowerSeries.algHom O) = MvPolynomial.aeval (c.x 1) :=
      MvPolynomial.algHom_ext fun i => by simp [(c.isEval 1).1 i]
    exact congrArg (fun φ => φ P) this
  have hP0 : MvPolynomial.constantCoeff P = 0 := by
    rw [MvPolynomial.constantCoeff_eq, hPdef, coeff_trunc', if_pos (zero_le')]
    simpa using hf
  have ha := dvd_pow_of_mem_span (c.x 1) (p : G.A 1) N₀ hx _ (aeval_mem_span (c.x 1) P hP0)
  rw [← hP] at ha
  have hsub := sub_dvd_pow_sub_pow (c.ev 1 f) (c.ev 1 P) (d * N₀ + 1)
  rw [← map_sub] at hsub
  simpa using dvd_add (hR.trans hsub) ha

end GlobalTheory.AugNil
