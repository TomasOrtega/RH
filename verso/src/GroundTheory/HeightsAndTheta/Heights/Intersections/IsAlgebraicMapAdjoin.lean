import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StWWRatioBasis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

variable {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem RatioField.map_mem [CharZero Ω] [CharZero Φ] {S : Set Ω} {L : IntermediateField ℚ Φ}
    (hS : ∀ w ∈ S, algebraMap Ω Φ w ∈ L) {z : Ω} (hz : z ∈ IntermediateField.adjoin ℚ S) :
    algebraMap Ω Φ z ∈ L := by
  have hle : (IntermediateField.adjoin ℚ S).map (algebraMap Ω Φ).toRatAlgHom ≤ L := by
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨w, hw, rfl⟩
    exact hS w hw
  exact hle ((IntermediateField.mem_map _).mpr ⟨z, hz, rfl⟩)

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem RatioField.isAlgebraic_map [CharZero Ω] [CharZero Φ] {d : ℕ} {t : Fin d → Ω}
    (ht : AlgebraicIndependent ℚ t) {z : Ω} (hz : IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) z)
    {s : Set Φ} (hs : ∀ n, algebraMap Ω Φ (t n) ∈ s) :
    IsAlgebraic (IntermediateField.adjoin ℚ s) (algebraMap Ω Φ z) := by
  let ψ := (algebraMap Ω Φ).toRatAlgHom
  have ht' : AlgebraicIndependent ℚ (ψ ∘ t) := ht.map' (algebraMap Ω Φ).injective
  have h4 : IsAlgebraic (Algebra.adjoin ℚ (Set.range (ψ ∘ t))) (ψ z) := by
    by_contra h
    have h3 : AlgebraicIndependent ℚ (fun o : Option (Fin d) => o.elim z t) := by
      refine AlgebraicIndependent.of_comp ψ ?_
      convert (ht'.option_iff_transcendental (ψ z)).mpr h using 1
      funext o
      cases o <;> rfl
    exact (ht.option_iff_transcendental z).mp h3 (IntermediateField.isAlgebraic_adjoin_iff.mp hz)
  have hsub : Set.range (ψ ∘ t) ⊆ s := by
    rintro _ ⟨n, rfl⟩
    exact hs n
  exact IntermediateField.isAlgebraic_adjoin_iff.mpr (h4.tower_top_of_subalgebra_le (Algebra.adjoin_mono hsub))

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem RatioField.isAlgebraic_map_adjoin [CharZero Ω] [CharZero Φ] {d : ℕ} {t : Fin d → Ω}
    (ht : AlgebraicIndependent ℚ t) {S : Set Ω}
    (hS : ∀ w ∈ S, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) w) {s : Set Φ}
    (hs : ∀ n, algebraMap Ω Φ (t n) ∈ s) {z : Ω} (hz : z ∈ IntermediateField.adjoin ℚ S) :
    IsAlgebraic (IntermediateField.adjoin ℚ s) (algebraMap Ω Φ z) := by
  have h := RatioField.map_mem (L := (algebraicClosure (IntermediateField.adjoin ℚ s) Φ).restrictScalars ℚ)
    (fun w hw => (IntermediateField.mem_restrictScalars ℚ).mpr
      (mem_algebraicClosure_iff.mpr (RatioField.isAlgebraic_map ht (hS w hw) hs))) hz
  exact mem_algebraicClosure_iff.mp ((IntermediateField.mem_restrictScalars ℚ).mp h)

variable {E κ : Type*} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem RatioField.lineVal_cramer (e b : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (g : κ → Fin 2 → Ω)
    (X : Ω) (k₀ k₁ k : κ) (hφ : ∀ k q, φ k (b q) = X * g k q)
    (hg : g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0) (a : Φ) :
    T.lineVal e (φ k) a =
      algebraMap Ω Φ ((g k 0 * g k₁ 1 - g k 1 * g k₁ 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) *
          T.lineVal e (φ k₀) a +
        algebraMap Ω Φ ((g k₀ 0 * g k 1 - g k₀ 1 * g k 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) *
          T.lineVal e (φ k₁) a := by
  have hlin : φ k = ((g k 0 * g k₁ 1 - g k 1 * g k₁ 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) • φ k₀ +
      ((g k₀ 0 * g k 1 - g k₀ 1 * g k 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) • φ k₁ := by
    refine b.ext fun q => ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hφ, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hg]
    fin_cases q <;> simp <;> ring
  rw [hlin]
  simp only [T.lineVal, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem RatioField.det_ne_zero (e b : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (g : κ → Fin 2 → Ω)
    (X : Ω) (hX : X ≠ 0) (k₀ k₁ : κ) (hφ : ∀ k q, φ k (b q) = X * g k q)
    (hg : g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0) :
    φ k₁ (e 0) * φ k₀ (e 1) - φ k₁ (e 1) * φ k₀ (e 0) ≠ 0 := by
  have hval : ∀ k q, φ k (b q) = e.repr (b q) 0 * φ k (e 0) + e.repr (b q) 1 * φ k (e 1) := by
    intro k q
    conv_lhs => rw [← e.sum_repr (b q)]
    simp only [Fin.sum_univ_two, map_add, map_smul, smul_eq_mul]
  intro h
  apply hg
  have hX2 : X * X ≠ 0 := mul_ne_zero hX hX
  apply (mul_right_injective₀ hX2).eq_iff.mp
  have h00 := hval k₀ 0
  have h01 := hval k₀ 1
  have h10 := hval k₁ 0
  have h11 := hval k₁ 1
  rw [hφ] at h00 h01 h10 h11
  linear_combination (X * g k₀ 0) * h11 + (e.repr (b 1) 1 * φ k₁ (e 1) + e.repr (b 1) 0 * φ k₁ (e 0)) * h00 -
    (X * g k₀ 1) * h10 - (e.repr (b 0) 1 * φ k₁ (e 1) + e.repr (b 0) 0 * φ k₁ (e 0)) * h01 +
    -(e.repr (b 0) 0 * e.repr (b 1) 1 - e.repr (b 0) 1 * e.repr (b 1) 0) * h

end

end GroundTheory.Heights₂.Heights.Inter
