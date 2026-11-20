import Mathlib
open scoped NNReal TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis.

Supply the required witnesses or components. Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Assume the negation of the conclusion and derive a contradiction. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem valuation_map_algEquiv_eq_of_le_one_iff_isIntegral (R Ω : Type) [CommRing R] [Nontrivial R]
    [Field Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω]
    (hinj : Function.Injective (algebraMap R Ω)) (v : Valuation Ω ℝ≥0)
    (hv : ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x) (g : Ω ≃ₐ[R] Ω) (x : Ω) : v (g x) = v x := by
  have hle : ∀ a b : Ω, v (g a) ≤ v (g b) ↔ v a ≤ v b := by
    intro a b
    by_cases hb : b = 0
    · subst hb
      simp
    · have hgb : g b ≠ 0 := by simpa using hb
      have hvb : 0 < v b := by simpa [pos_iff_ne_zero] using hb
      have hvgb : 0 < v (g b) := by simpa [pos_iff_ne_zero] using hgb
      have h1 : v (a / b) ≤ 1 ↔ v a ≤ v b := by rw [map_div₀, div_le_one hvb]
      have h2 : v (g (a / b)) ≤ 1 ↔ v (g a) ≤ v (g b) := by
        rw [map_div₀ g, map_div₀, div_le_one hvgb]
      rw [← h1, ← h2, hv, hv, isIntegral_algEquiv]
  have hlt : ∀ a b : Ω, v (g a) < v (g b) ↔ v a < v b := by
    intro a b
    rw [← not_le, ← not_le, hle]
  obtain ⟨k, l, hkl, heq⟩ : ∃ k l : ℕ, k < l ∧ (g ^ k) x = (g ^ l) x := by
    obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) x
    have hmap : p.map (algebraMap R Ω) ≠ 0 := by
      rwa [Ne, Polynomial.map_eq_zero_iff hinj]
    have hsub : Set.range (fun k : ℕ => (g ^ k) x) ⊆ p.rootSet Ω := by
      rintro _ ⟨k, rfl⟩
      rw [Polynomial.mem_rootSet']
      refine ⟨hmap, ?_⟩
      rw [Polynomial.aeval_algEquiv]
      simp [hpx]
    have hfin := (Polynomial.rootSet_finite p Ω).subset hsub
    have hni : ¬ Function.Injective (fun k : ℕ => (g ^ k) x) := fun hi =>
      Set.infinite_range_of_injective hi hfin
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a, b, h, hab⟩
    · exact ⟨b, a, h, hab.symm⟩
  have hstep : ∀ k : ℕ, (g ^ (k + 1)) x = g ((g ^ k) x) := by
    intro k
    rw [pow_succ', AlgEquiv.mul_apply]
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hs : ∀ n : ℕ, v ((g ^ (n + 1)) x) < v ((g ^ n) x) := by
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        rw [hstep (n + 1), hstep n, hlt]
        rw [hstep n] at ih
        simpa [hstep] using ih
    have hanti : StrictAnti (fun n : ℕ => v ((g ^ n) x)) := strictAnti_nat_of_succ_lt hs
    have := hanti hkl
    simp only [heq] at this
    exact lt_irrefl _ this
  · have hs : ∀ n : ℕ, v ((g ^ n) x) < v ((g ^ (n + 1)) x) := by
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        rw [hstep (n + 1), hstep n, hlt]
        rw [hstep n] at ih
        simpa [hstep] using ih
    have hmono : StrictMono (fun n : ℕ => v ((g ^ n) x)) := strictMono_nat_of_lt_succ hs
    have := hmono hkl
    simp only [heq] at this
    exact lt_irrefl _ this

end GlobalTheory
