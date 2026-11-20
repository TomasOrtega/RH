import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
open UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.cxLin_of :
    CxFlat → CxLin := by
  intro hflat p _ G v K m f a hfin A w c
  classical
  have hU : (⋃ i, {z : Σ q : GlobalTheory.LKCx.FCls G, PtsOf G v K q × GlobalTheory.LKCx.grp G (Quot.out q).β |
      Seen G v K (f i) z.1 z.2.1 z.2.2}).Finite := Set.finite_iUnion hfin
  have hS : ∀ i z, Seen G v K (f i) z.1 z.2.1 z.2.2 → z ∈ hU.toFinset := by
    intro i z hz
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.2 ⟨i, hz⟩
  have hS' : ∀ z, Seen G v K (∑ i, a i • f i) z.1 z.2.1 z.2.2 → z ∈ hU.toFinset := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    rw [Finset.sum_apply] at h2
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
    refine hS i z ⟨h1, ?_, h3⟩
    intro h0
    apply hi
    simp [Pi.smul_apply, smul_eq_mul, h0]
  have hR : ∀ α i, GlobalTheory.RootSumWeights.cxTotalM G v (c α) K (f i) (Kp G) (oneP G) =
      ∑ z ∈ hU.toFinset, summ G v (c α) K (f i) z :=
    fun α i => hflat p G v (c α) K (f i) hU.toFinset (hS i)
  have hT : ∀ z, summ G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) z =
      ∑ i, a i * w.sum fun α r => r * summ G v (c α) K (f i) z := by
    intro z
    unfold summ
    split_ifs with hfix
    · simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro α _
      ring
    · simp [Finsupp.sum]
  calc GlobalTheory.RootSumWeights.cxTotalM G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) (Kp G) (oneP G)
      = ∑ z ∈ hU.toFinset, summ G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) z :=
        hflat p G v _ K _ hU.toFinset hS'
    _ = ∑ z ∈ hU.toFinset, ∑ i, a i * w.sum fun α r => r * summ G v (c α) K (f i) z :=
        Finset.sum_congr rfl fun z _ => hT z
    _ = ∑ i, ∑ z ∈ hU.toFinset, a i * w.sum fun α r => r * summ G v (c α) K (f i) z := Finset.sum_comm
    _ = ∑ i, a i * w.sum fun α r => r * GlobalTheory.RootSumWeights.cxTotalM G v (c α) K (f i) (Kp G) (oneP G) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finsupp.sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [hR α i, Finset.mul_sum]
