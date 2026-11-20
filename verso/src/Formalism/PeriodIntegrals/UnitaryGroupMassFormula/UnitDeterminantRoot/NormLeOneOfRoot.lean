import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobalLUnit
import Lemmata.GeneralBFactLeftTer.Imports

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
lemma conj_theta (b : ℤ) (d : ℕ) : conj (UnitDetRootDefs.cmTheta b d) = (b : ℂ) - UnitDetRootDefs.cmTheta b d := by
  simp only [UnitDetRootDefs.cmTheta, map_div₀, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast,
    map_ofNat]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conjMem : ConjMem := by
  intro b d x hx
  have hle : KF b d ≤ IntermediateField.comap ((starRingEnd ℂ).toRatAlgHom) (KF b d) := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    show conj (UnitDetRootDefs.cmTheta b d) ∈ KF b d
    rw [conj_theta]
    exact sub_mem (IntermediateField.intCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ _)
  exact hle hx

/- English proof (translation)
Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem conjLUnit : ConjLUnit := by
  rintro l x ⟨hx0, k, hk, h1, h2⟩
  refine ⟨(map_ne_zero _).mpr hx0, k, hk, ?_, ?_⟩
  · have h := h1.map (starRingEnd ℂ).toIntAlgHom
    change IsIntegral ℤ (conj ((k : ℂ) * x)) at h
    rwa [map_mul, map_natCast] at h
  · have h := h2.map (starRingEnd ℂ).toIntAlgHom
    change IsIntegral ℤ (conj ((k : ℂ) * x⁻¹)) at h
    rwa [map_mul, map_natCast, map_inv₀] at h

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
lemma norm_le_one_of_root {F : Type*} [NormedField F] [IsUltrametricDist F] {y : F}
    (p : Polynomial ℤ) (hp : p.Monic) (hpy : p.eval₂ (Int.castRingHom F) y = 0) : ‖y‖ ≤ 1 := by
  first | exact Bl.general_b_fact_left_ter.goal1 .. | (apply Bl.general_b_fact_left_ter.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_ter.goal1 <;> assumption)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma norm_iota_natCast (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (k : ℕ) (hk : ¬ l ∣ k) :
    ‖ι (k : ℂ)‖ = 1 := by
  rw [map_natCast]
  have e : ((k : ℚ_[l]) : ℂ_[l]) = (k : ℂ_[l]) := by simp
  rw [← e, PadicComplex.norm_extends', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hk

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
theorem normOne : NormOne := by
  rintro l _ ι x ⟨hx0, k, hk, h1, h2⟩
  have hI : ∀ z : ℂ, IsIntegral ℤ z → ‖ι z‖ ≤ 1 := by
    rintro z ⟨p, hp, hpz⟩
    apply norm_le_one_of_root p hp
    have h : (ι.toRingHom) (p.eval₂ (algebraMap ℤ ℂ) z) = 0 := by rw [hpz, map_zero]
    rw [Polynomial.hom_eval₂, RingHom.ext_int (ι.toRingHom.comp (algebraMap ℤ ℂ)) (Int.castRingHom _)] at h
    exact h
  have e1 := hI _ h1
  have e2 := hI _ h2
  rw [map_mul, norm_mul, norm_iota_natCast l ι k hk, one_mul] at e1 e2
  have e3 : ‖ι x‖ * ‖ι x⁻¹‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι x⁻¹)]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Take a linear combination of the given relations to obtain the conclusion.
-/
lemma theta_sq {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) :
    UnitDetRootDefs.cmTheta b d ^ 2 = b * UnitDetRootDefs.cmTheta b d - (a : ℂ) * c := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = d := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  have h4 : (4 : ℂ) * a * c = b ^ 2 + d := by exact_mod_cast hok.1
  simp only [UnitDetRootDefs.cmTheta]
  linear_combination (((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) / 4) * Complex.I_mul_I
    - (1 / 4 : ℂ) * hs + (1 / 4 : ℂ) * h4

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
lemma theta_isIntegral {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) : IsIntegral ℚ (UnitDetRootDefs.cmTheta b d) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C ((a : ℚ) * c), ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X, eq_ratCast, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast]
    linear_combination theta_sq hok

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative.

A detailed English derivation is pending.
-/
lemma sigma_on_KF {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) (σ : ℂ ≃+* ℂ) :
    (∀ x ∈ KF b d, σ x = x) ∨ (∀ x ∈ KF b d, σ x = conj x) := by
  have hq : (σ (UnitDetRootDefs.cmTheta b d) - UnitDetRootDefs.cmTheta b d) * (σ (UnitDetRootDefs.cmTheta b d) - conj (UnitDetRootDefs.cmTheta b d)) = 0 := by
    have h := congrArg σ (theta_sq hok)
    simp only [map_pow, map_sub, map_mul, map_intCast, map_natCast] at h
    rw [conj_theta]
    linear_combination h - theta_sq hok
  have key : ∀ f : ℂ →+* ℂ, σ (UnitDetRootDefs.cmTheta b d) = f (UnitDetRootDefs.cmTheta b d) → ∀ x ∈ KF b d, σ x = f x := by
    intro f hf x hx
    let S : Subfield ℂ := RingHom.eqLocusField σ.toRingHom f
    let E : IntermediateField ℚ ℂ := S.toIntermediateField (fun q => by
      show σ (algebraMap ℚ ℂ q) = f (algebraMap ℚ ℂ q)
      simp [eq_ratCast])
    have hle : KF b d ≤ E := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact hf
    exact hle hx
  rcases mul_eq_zero.mp hq with h | h
  · exact Or.inl (key (RingHom.id ℂ) (sub_eq_zero.mp h))
  · exact Or.inr (key (starRingEnd ℂ) (sub_eq_zero.mp h))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Use the polynomial consequences of the given equalities and inequalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem rootStep : RootStep := by
  intro a b c d hok β hβ hββ N hN
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq β⁻¹ hN
  have hnorm : ‖β‖ = 1 := by
    have h := congrArg (fun z => ‖z‖) hββ
    simp only [norm_mul, Complex.norm_conj, norm_one] at h
    nlinarith [norm_nonneg β]
  refine ⟨κ, hκ, ?_, ?_⟩
  · have := IntermediateField.adjoin.finiteDimensional (theta_isIntegral hok)
    have hβi : β⁻¹ ∈ KF b d := inv_mem hβ
    have : IsIntegral ℚ β⁻¹ := by
      have h := (Algebra.IsIntegral.isIntegral (R := ℚ) (⟨β⁻¹, hβi⟩ : KF b d)).map (KF b d).val
      simpa using h
    exact IsAlgebraic.of_pow hN (hκ ▸ this.isAlgebraic)
  · intro σ
    have h1 : ‖σ κ‖ ^ N = 1 := by
      rw [← norm_pow, ← map_pow, hκ, map_inv₀, norm_inv]
      rcases sigma_on_KF hok σ with h | h
      · rw [h β hβ, hnorm, inv_one]
      · rw [h β hβ, Complex.norm_conj, hnorm, inv_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h1

end PI.UnitaryGroupMassFormula.UnitDetRoot
