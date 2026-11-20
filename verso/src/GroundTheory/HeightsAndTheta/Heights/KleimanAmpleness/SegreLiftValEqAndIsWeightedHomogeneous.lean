import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime blockWeight)

noncomputable section

section Lift

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type} [Field F]

def segreSubstVal : (Σ d, segreIdx ι d) → MRing ι F
  | ⟨Sum.inl _, c⟩ => ∏ k, X ⟨k, c k⟩
  | ⟨Sum.inr k, i⟩ => X ⟨k, i⟩

def segreDeg (b : Unit ⊕ K → ℕ) : K → ℕ := fun k => b (Sum.inr k) + b (Sum.inl ())

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Separate the alternatives or extract the components of the hypothesis. Split into cases according to the possible forms of the given data. Establish an intermediate fact. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem segreDeg_injective_of_fst {b b' : Unit ⊕ K → ℕ} (h₀ : b' (Sum.inl ()) = b (Sum.inl ()))
    (h : segreDeg b' = segreDeg b) : b' = b := by
  funext x
  rcases x with u | k
  · cases u; exact h₀
  · have := congrFun h k
    simp only [segreDeg] at this
    omega

/- English proof (translation)
Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Split into cases according to the possible forms of the given data. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem segreLiftVal_eq_and_isWeightedHomogeneous (W : Ideal (MRing ι F)) (v : Σ d, segreIdx ι d) :
    segreLiftVal ι F W v = Polynomial.C (Ideal.Quotient.mk W (segreSubstVal v)) *
        Polynomial.X ^ (blockWeight (segreIdx ι) v (Sum.inl ())) ∧
      IsWeightedHomogeneous (blockWeight ι) (segreSubstVal (F := F) v)
        (segreDeg (blockWeight (segreIdx ι) v)) := by
  obtain ⟨d, i⟩ := v
  rcases d with u | k
  · cases u
    refine ⟨by simp [segreLiftVal, segreSubstVal, blockWeight]; ring, ?_⟩
    have hp := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, i k⟩ : MRing ι F)) (fun k => blockWeight ι ⟨k, i k⟩)
      (fun k _ => isWeightedHomogeneous_X _ _ _)
    have hd : segreDeg (blockWeight (segreIdx ι) ⟨Sum.inl (), i⟩) =
        ∑ k, blockWeight ι ⟨k, i k⟩ := by
      funext k
      simp [segreDeg, blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hd]
    exact hp
  · refine ⟨by simp [segreLiftVal, segreSubstVal, blockWeight], ?_⟩
    have hd : segreDeg (blockWeight (segreIdx ι) ⟨Sum.inr k, i⟩) = blockWeight ι ⟨k, i⟩ := by
      funext k'
      by_cases h : k' = k
      · subst h; simp [segreDeg, blockWeight]
      · simp [segreDeg, blockWeight, h]
    rw [hd]
    exact isWeightedHomogeneous_X _ _ _

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem segreLiftMap_of_isMultiHomog (W : Ideal (MRing ι F)) (b : Unit ⊕ K → ℕ)
    {f : MRing (segreIdx ι) F} (hf : IsWeightedHomogeneous (blockWeight (segreIdx ι)) f b) :
    segreLiftMap ι F W f = Polynomial.C (Ideal.Quotient.mk W (aeval segreSubstVal f)) *
        Polynomial.X ^ (b (Sum.inl ())) ∧
      IsWeightedHomogeneous (blockWeight ι) (aeval (segreSubstVal (F := F)) f) (segreDeg b) := by
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => exact ⟨by simp, isWeightedHomogeneous_zero _ _ _⟩
  | add p q hp hq ihp ihq =>
    refine ⟨?_, ?_⟩
    · rw [map_add, map_add, map_add, map_add, ihp.1, ihq.1, add_mul]
    · rw [map_add]; exact ihp.2.add ihq.2
  | monomial d r hr =>
    have hb : b (Sum.inl ()) =
        ∑ v ∈ d.support, blockWeight (segreIdx ι) v (Sum.inl ()) * d v := by
      rw [← hr, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      simp [smul_eq_mul, mul_comm]
    have hdeg : segreDeg b = ∑ v ∈ d.support, d v • segreDeg (blockWeight (segreIdx ι) v) := by
      rw [← hr, Finsupp.weight_apply, Finsupp.sum]
      funext k
      simp [segreDeg, Finset.sum_apply, Finset.sum_add_distrib, mul_add]
    rw [monomial_eq, Finsupp.prod]
    refine ⟨?_, ?_⟩
    · simp only [map_mul, map_prod, map_pow, segreLiftMap, aeval_X, aeval_C]
      rw [Finset.prod_congr rfl (fun v _ => by rw [(segreLiftVal_eq_and_isWeightedHomogeneous W v).1]), hb]
      rw [Finset.prod_congr rfl (fun v _ =>
        show (Polynomial.C (Ideal.Quotient.mk W (segreSubstVal v)) *
            Polynomial.X ^ blockWeight (segreIdx ι) v (Sum.inl ())) ^ d v =
          Polynomial.C (Ideal.Quotient.mk W (segreSubstVal v)) ^ d v *
            Polynomial.X ^ (blockWeight (segreIdx ι) v (Sum.inl ()) * d v) by ring)]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Polynomial.algebraMap_apply,
        ← Ideal.Quotient.mk_algebraMap]
      ring
    · simp only [map_mul, map_prod, map_pow, aeval_X, aeval_C]
      rw [hdeg]
      refine IsWeightedHomogeneous.C_mul ?_ _
      exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (segreLiftVal_eq_and_isWeightedHomogeneous (F := F) ⊥ v).2.pow _

end Lift

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem SegreLiftPrime.proof : SegreLiftPrime.Statement := by
  intro F _ K _ _ ι _ W hW
  classical
  have := hW.isPrime
  refine ⟨RingHom.ker_isPrime _, ?_, ?_⟩
  · intro f hf b
    set w := blockWeight (segreIdx ι)
    have hB := fun b' => segreLiftMap_of_isMultiHomog W b'
      (weightedHomogeneousComponent_isWeightedHomogeneous (w := w) b' f)
    set s : Finset (Unit ⊕ K → ℕ) := insert b (f.support.image (Finsupp.weight w)) with hs
    have hsum : f = ∑ b' ∈ s, weightedHomogeneousComponent w b' f := by
      ext d
      simp only [coeff_sum, coeff_weightedHomogeneousComponent]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · by_contra hne
        exact h (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne)))
    have hker : segreLiftMap ι F W f = 0 := hf
    rw [hsum, map_sum, Finset.sum_congr rfl (fun b' _ => (hB b').1)] at hker
    have hcoeff := congrArg (fun p => Polynomial.coeff p (b (Sum.inl ()))) hker
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero]
      at hcoeff
    rw [← Finset.sum_filter, ← map_sum, Ideal.Quotient.eq_zero_iff_mem] at hcoeff
    have hcomp := hW.multiHomog _ hcoeff (segreDeg b)
    have hval : ∀ b' ∈ s.filter (fun b' => b (Sum.inl ()) = b' (Sum.inl ())),
        weightedHomogeneousComponent (blockWeight ι) (segreDeg b)
            (aeval (segreSubstVal (F := F)) (weightedHomogeneousComponent w b' f)) =
          if b' = b then aeval (segreSubstVal (F := F)) (weightedHomogeneousComponent w b' f)
          else 0 := by
      intro b' hb'
      rw [weightedHomogeneousComponent_of_mem
        (by rw [mem_weightedHomogeneousSubmodule]; exact (hB b').2)]
      have h₀ := (Finset.mem_filter.mp hb').2
      by_cases hbb : b' = b
      · subst hbb; simp
      · rw [if_neg hbb, if_neg (fun h => hbb (segreDeg_injective_of_fst h₀.symm h.symm))]
    have hbmem : b ∈ s.filter (fun b' => b (Sum.inl ()) = b' (Sum.inl ())) :=
      Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, rfl⟩
    rw [map_sum, Finset.sum_congr rfl hval, Finset.sum_ite_eq', if_pos hbmem] at hcomp
    show segreLiftMap ι F W _ = 0
    rw [(hB b).1, (Ideal.Quotient.eq_zero_iff_mem).mpr hcomp, map_zero, zero_mul]
  · intro d
    rcases d with u | k
    · choose c hc using hW.relevant
      refine ⟨c, ?_⟩
      show ¬ segreLiftMap ι F W _ = 0
      rw [segreLiftMap, aeval_X]
      simp only [segreLiftVal, mul_eq_zero, Polynomial.X_ne_zero, false_or, Polynomial.C_eq_zero,
        Ideal.Quotient.eq_zero_iff_mem]
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨k, -, hk⟩
      exact hc k hk
    · obtain ⟨i, hi⟩ := hW.relevant k
      refine ⟨i, ?_⟩
      show ¬ segreLiftMap ι F W _ = 0
      rw [segreLiftMap, aeval_X]
      simp only [segreLiftVal, Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact hi

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
