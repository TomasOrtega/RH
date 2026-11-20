import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem algHom_coe_eq_aeval {O T : Type} [CommRing O] [CommRing T] [Algebra O T]
    (ρ : PowerSeries O →ₐ[O] T) (r : Polynomial O) :
    ρ (r : PowerSeries O) = Polynomial.aeval (ρ X) r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.coe_add, map_add, hp, hq, map_add]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X, map_mul, map_pow, map_mul, map_pow,
      Polynomial.aeval_C, Polynomial.aeval_X]
    congr 1
    all_goals first
      | exact ρ.commutes a
      | simpa using ρ.commutes a
      | (rw [← ρ.commutes a]; rfl)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem constantCoeff_aeval {O S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (x : PowerSeries S) (r : Polynomial O) :
    constantCoeff (Polynomial.aeval x r) = Polynomial.aeval (constantCoeff x) r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow]
    congr 1
    all_goals first
      | rfl
      | simp [PowerSeries.algebraMap_apply'']
      | (rw [IsScalarTower.algebraMap_apply O S (PowerSeries S)]; simp)

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem eq_of_X_mul_eq {S : Type} [CommRing S] {f g : PowerSeries S}
    (h : (X : PowerSeries S) * f = X * g) : f = g := by
  first
  | (ext n; simpa [PowerSeries.coeff_succ_X_mul] using congrArg (PowerSeries.coeff (n + 1)) h)
  | (ext n; simpa [PowerSeries.coeff_succ_X_mul] using congrArg (PowerSeries.coeff S (n + 1)) h)
  | exact PowerSeries.X_mul_cancel h
  | exact mul_left_cancel₀ PowerSeries.X_ne_zero h

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem map_coe_eq_X_pow_lemma {O K : Type} [CommRing O] [CommRing K] (I : Ideal O) (f : O →+* K)
    (hf : ∀ c ∈ I, f c = 0) (P : Polynomial O) (hP : P.IsDistinguishedAt I) :
    PowerSeries.map f (P : PowerSeries O) = X ^ P.natDegree := by
  have hmon : P.Monic := by first | exact hP.monic | exact hP.2
  have hmem : ∀ {n : ℕ}, n < P.natDegree → P.coeff n ∈ I := by
    intro n hn
    first | exact hP.mem hn | exact hP.1.mem hn | exact hP.toIsWeaklyEisensteinAt.mem hn
  ext n
  rw [PowerSeries.coeff_map, Polynomial.coeff_coe, PowerSeries.coeff_X_pow]
  split_ifs with hn
  · rw [hn, hmon.coeff_natDegree, map_one]
  · rcases Nat.lt_or_gt_of_ne hn with h | h
    · exact hf _ (hmem h)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, map_zero]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Treat this case separately. Treat this case separately.

Reduce the conclusion to the remaining proof obligations. Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
private theorem exists_weierstrass_div_lemma_2 {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] (P : Polynomial O) (hP : P.IsDistinguishedAt (maximalIdeal O))
    (a : PowerSeries O) :
    ∃ (q : PowerSeries O) (r : Polynomial O), r.degree < P.natDegree ∧
      a = (P : PowerSeries O) * q + r := by
  have h1 : PowerSeries.map (residue O) (P : PowerSeries O) = X ^ P.natDegree :=
    map_coe_eq_X_pow_lemma _ _ (fun c hc => (residue_eq_zero_iff c).2 hc) P hP
  have h2 : (PowerSeries.map (residue O) (P : PowerSeries O)).order.toNat = P.natDegree := by
    rw [h1, PowerSeries.order_X_pow]; rfl
  have h3 : PowerSeries.map (residue O) (P : PowerSeries O) ≠ 0 := by
    rw [h1]; exact pow_ne_zero _ PowerSeries.X_ne_zero
  obtain ⟨q, r, hr, he⟩ := PowerSeries.exists_isWeierstrassDivision (f := a) h3
  have h2' : (PowerSeries.map (Ideal.Quotient.mk (maximalIdeal O)) (P : PowerSeries O)).order.toNat =
      P.natDegree := by
    first
      | exact h2
      | (rw [map_coe_eq_X_pow_lemma _ _ (fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc) P hP,
          PowerSeries.order_X_pow]; rfl)
  refine ⟨q, r, ?_, he⟩
  first
    | (rw [h2'] at hr; exact hr)
    | (rw [h2] at hr; exact hr)
    | simpa [h2'] using hr

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem rhoCompl : RhoComplStatement := by
  intro O LL S _ _ _ _ _ _ _ _ _ _ _ P hP ρ hunit hann
  have hmon : P.Monic := by first | exact hP.monic | exact hP.2
  have key : ∀ a : PowerSeries O, (X : PowerSeries S) ∣ ρ a → (P : PowerSeries O) ∣ a := by
    intro a ha
    obtain ⟨q, r, hr, he⟩ := exists_weierstrass_div_lemma_2 P hP a
    obtain ⟨w, hw⟩ := hunit
    have hρa : ρ a = (w : PowerSeries S) * X * ρ q + Polynomial.aeval (ρ X) r := by
      rw [he, map_add, map_mul, hw, algHom_coe_eq_aeval]
    have h0 : constantCoeff (ρ a) = 0 := by
      obtain ⟨c, hc⟩ := ha
      rw [hc, map_mul, PowerSeries.constantCoeff_X, zero_mul]
    have hr0 : Polynomial.aeval (constantCoeff (ρ X)) r = 0 := by
      have h1 := congrArg constantCoeff hρa
      rw [h0, map_add, map_mul, map_mul, PowerSeries.constantCoeff_X, mul_zero, zero_mul, zero_add,
        constantCoeff_aeval] at h1
      exact h1.symm
    have hdvd : P.map (algebraMap O LL) ∣ r.map (algebraMap O LL) := by
      apply hann
      first | (rw [Polynomial.aeval_map_algebraMap]; exact hr0) | simpa [Polynomial.aeval_map_algebraMap] using hr0
    have hmap0 : r.map (algebraMap O LL) = 0 := by
      apply Polynomial.eq_zero_of_dvd_of_degree_lt hdvd
      calc (r.map (algebraMap O LL)).degree ≤ r.degree := by
            first | exact Polynomial.degree_map_le | exact Polynomial.degree_map_le _ _
        _ < P.natDegree := hr
        _ = P.degree := (Polynomial.degree_eq_natDegree hmon.ne_zero).symm
        _ = (P.map (algebraMap O LL)).degree := (hmon.degree_map _).symm
    have hr' : r = 0 := by
      apply Polynomial.map_injective (algebraMap O LL) (IsFractionRing.injective O LL)
      rw [hmap0, Polynomial.map_zero]
    rw [hr', Polynomial.coe_zero, add_zero] at he
    exact ⟨q, he⟩
  intro k
  induction k with
  | zero => intro a _; simp
  | succ k ih =>
    intro a ha
    obtain ⟨b, rfl⟩ := key a (dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero k)) ha)
    obtain ⟨w, hw⟩ := hunit
    rw [map_mul, hw] at ha
    obtain ⟨c, hc⟩ := ha
    have h2 : (w : PowerSeries S) * ρ b = X ^ k * c := by
      apply eq_of_X_mul_eq
      linear_combination hc
    have hb : (X : PowerSeries S) ^ k ∣ ρ b := by
      refine ⟨(↑w⁻¹ : PowerSeries S) * c, ?_⟩
      calc ρ b = (↑w⁻¹ : PowerSeries S) * ((w : PowerSeries S) * ρ b) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = (↑w⁻¹ : PowerSeries S) * (X ^ k * c) := by rw [h2]
        _ = X ^ k * ((↑w⁻¹ : PowerSeries S) * c) := by ring
    obtain ⟨d, hd⟩ := ih b hb
    exact ⟨d, by rw [hd]; ring⟩

end LevelStatements.Lv
