import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.LadicPlace

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Chain the equalities or inequalities of the calculation. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem norm_embedding_integer_le_one {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
    (τ : E →+* PadicAlgCl l) (a : 𝓞 E) : ‖τ (a : E)‖ ≤ 1 := by
  have h : IsIntegral ℤ (τ (a : E)) := by
    have := (RingOfIntegers.isIntegral_coe a).map τ.toIntAlgHom
    simpa using this
  obtain ⟨p, hp, hp0⟩ := h
  by_contra hlt
  push_neg at hlt
  set y := τ (a : E)
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at hp0
  have h1 : y ^ p.natDegree =
      - ∑ i ∈ Finset.range p.natDegree, algebraMap ℤ (PadicAlgCl l) (p.coeff i) * y ^ i := by
    linear_combination hp0
  have hpos : 0 < ‖y‖ ^ p.natDegree := pow_pos (by linarith) _
  have h2 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap ℤ (PadicAlgCl l) (p.coeff i) * y ^ i‖
      < ‖y‖ ^ p.natDegree := by
    refine Finset.sum_induction _ (fun z => ‖z‖ < ‖y‖ ^ p.natDegree) ?_ (by simpa using hpos) ?_
    · intro u v hu hv
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max u v) (max_lt hu hv)
    · intro i hi
      rw [norm_mul, norm_pow]
      have h3 : ‖algebraMap ℤ (PadicAlgCl l) (p.coeff i)‖ ≤ 1 := by
        simpa using IsUltrametricDist.norm_intCast_le_one (PadicAlgCl l) (p.coeff i)
      calc _ ≤ 1 * ‖y‖ ^ i := by gcongr
        _ = ‖y‖ ^ i := one_mul _
        _ < _ := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  rw [← norm_neg, ← h1, norm_pow] at h2
  exact lt_irrefl _ h2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem exists_place_of_embedding :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (τ : E →+* Qbar l),
      ∃ v : HeightOneSpectrum (𝓞 E), ∀ x : E, v.valuation E x < 1 ↔ ‖τ x‖ < 1 := by
  intro E _ _ l hl τ
  have hle : ∀ a : 𝓞 E, ‖τ (a : E)‖ ≤ 1 := norm_embedding_integer_le_one τ
  let P : Ideal (𝓞 E) :=
    { carrier := {a | ‖τ (a : E)‖ < 1}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [RingOfIntegers.coe_eq_algebraMap, map_add, map_add]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [RingOfIntegers.coe_eq_algebraMap, smul_eq_mul, map_mul, map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) ha }
  have hP : ∀ a : 𝓞 E, a ∈ P ↔ ‖τ (algebraMap (𝓞 E) E a)‖ < 1 := fun a => Iff.rfl
  have hone : ∀ a : 𝓞 E, a ∉ P → ‖τ (algebraMap (𝓞 E) E a)‖ = 1 := fun a ha =>
    le_antisymm (hle a) (not_lt.mp (fun h => ha ((hP a).mpr h)))
  have hprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hP]; simp
    · intro a b hab
      by_contra hn
      rw [not_or] at hn
      rw [hP, map_mul, map_mul, norm_mul, hone a hn.1, hone b hn.2] at hab
      simp at hab
  have hlP : (l : 𝓞 E) ∈ P := by
    rw [hP, map_natCast, map_natCast]
    have h1 : ((l : ℕ) : PadicAlgCl l) = ((l : ℚ_[l]) : PadicAlgCl l) := by
      simp
    rw [h1, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hlP
    exact hl.out.ne_zero (by exact_mod_cast hlP)
  let v : HeightOneSpectrum (𝓞 E) := ⟨P, hprime, hne⟩
  have key : ∀ x : E, v.valuation E x ≤ 1 → ∃ a s : 𝓞 E, s ∉ P ∧
      x * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a := by
    intro x hx
    obtain ⟨a, s, h⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
    exact ⟨a, s, s.2, h⟩
  refine ⟨v, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨a, s, hs, h⟩ := key x hx.le
    have ha : a ∈ P := by
      have : v.valuation E (algebraMap (𝓞 E) E a) < 1 := by
        rw [← h, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (v.valuation_le_one s)) hx
      exact (v.valuation_lt_one_iff_mem a).mp this
    rw [hP, ← h, map_mul, norm_mul, hone s hs, mul_one] at ha
    exact ha
  · by_contra hn
    have hn' : 1 ≤ v.valuation E x := not_lt.mp hn
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hn'
    have hinv : v.valuation E x⁻¹ ≤ 1 := by
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ hn'
    obtain ⟨a, s, hs, h⟩ := key _ hinv
    have h2 : algebraMap (𝓞 E) E s = x * algebraMap (𝓞 E) E a := by
      rw [← h, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
    have h3 := hone s hs
    rw [h2, map_mul, norm_mul] at h3
    have h4 := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx (hle a)
    exact absurd h3 h4.ne

end GlobalTheory.LadicPlace
