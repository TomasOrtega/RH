import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.DPFiltration

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dpow_mem_span_pow {B : Type} [CommRing B] [Algebra ℚ B] {x : B}
    (δ : DividedPowers (Ideal.span {x})) (k : ℕ) {y : B} (hy : y ∈ Ideal.span {x}) :
    δ.dpow k y ∈ Ideal.span {x ^ k} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ δ hy, Algebra.smul_def, mul_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem list_prod_dpow_mem {B : Type} [CommRing B] [Algebra ℚ B] {x : B}
    (δ : DividedPowers (Ideal.span {x})) (l : List (ℕ × B))
    (hl : ∀ q ∈ l, q.2 ∈ Ideal.span {x}) :
    (l.map fun q => δ.dpow q.1 q.2).prod ∈ Ideal.span {x ^ (l.map Prod.fst).sum} := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add]
    have h1 := dpow_mem_span_pow δ q.1 (hl q (by simp))
    have h2 := ih (fun q' hq' => hl q' (by simp [hq']))
    rw [Ideal.mem_span_singleton] at h1 h2 ⊢
    exact mul_dvd_mul h1 h2

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem dividedPowerFiltration_span_singleton {B : Type} [CommRing B] [Algebra ℚ B] (x : B)
    (δ : DividedPowers (Ideal.span {x})) (r : ℕ) :
    CrystallineSemistableComparison.Pb.pdP δ r = Ideal.span {x ^ r} := by
  apply le_antisymm
  · unfold CrystallineSemistableComparison.Pb.pdP
    rw [Ideal.span_le]
    rintro z ⟨l, hl, hr, rfl⟩
    have h := list_prod_dpow_mem δ l hl
    rw [Ideal.mem_span_singleton] at h
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    exact (pow_dvd_pow x hr).trans h
  · rw [Ideal.span_singleton_le_iff_mem]
    unfold CrystallineSemistableComparison.Pb.pdP
    apply Ideal.subset_span
    refine ⟨List.replicate r (1, x), ?_, ?_, ?_⟩
    · intro q hq
      rw [List.eq_of_mem_replicate hq]
      exact Ideal.mem_span_singleton_self x
    · simp
    · simp [δ.dpow_one (Ideal.mem_span_singleton_self x)]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pdP_γB {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (r : ℕ) :
    pdP (Lat.γB f ξ) r = Ideal.span {f ξ ^ r} :=
  dividedPowerFiltration_span_singleton (f ξ) (Lat.γB f ξ) r

end GlobalTheory.CompanionTheory.DPFiltration
