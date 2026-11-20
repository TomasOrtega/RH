import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem isGl_negT {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (F : ι → ι → Module.End ℂ M) (h : IsGl F) : IsGl (negT F) := by
  intro a b c d
  have h1 := h d c b a
  simp only [negT, neg_mul_neg]
  have e1 : F b a * F d c - F d c * F b a = -(F d c * F b a - F b a * F d c) := by abel
  rw [e1, h1]
  simp only [@eq_comm _ c b, @eq_comm _ a d]
  split_ifs <;> abel

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem unitOn_negT {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) (h : UnitOn s F U) :
    UnitOn s (negT F) U := by
  obtain ⟨hfd, hst, ip, hsym, hpos, hadj⟩ := h
  refine ⟨hfd, fun a b hab u hu => ?_, ip, hsym, hpos, fun a b hab x hx y hy => ?_⟩
  · simp only [negT, LinearMap.neg_apply]
    exact U.neg_mem (hst b a hab.symm u hu)
  · simp only [negT, LinearMap.neg_apply, map_neg, LinearMap.neg_apply]
    rw [hadj b a hab.symm x hx y hy]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.
-/
theorem unitOn_not {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) (h : UnitOn s F U) :
    UnitOn (fun a => !s a) F U := by
  obtain ⟨hfd, hst, ip, hsym, hpos, hadj⟩ := h
  refine ⟨hfd, fun a b hab u hu => hst a b (by simpa using hab) u hu, ip, hsym, hpos,
    fun a b hab x hx y hy => hadj a b (by simpa using hab) x hx y hy⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem sym_negT_swap : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), (IsGl F → IsGl (negT F)) ∧ cas s (negT F) = cas s F ∧ cas (fun a => !s a) F = cas s F ∧ (∀ U, UnitOn s F U → UnitOn s (negT F) U ∧ UnitOn (fun a => !s a) F U) ∧ (LocU s F → LocU s (negT F) ∧ LocU (fun a => !s a) F) := by
  intro ι M _ _ _ _ s F
  refine ⟨isGl_negT F, ?_, ?_, fun U hU => ⟨unitOn_negT s F U hU, unitOn_not s F U hU⟩, fun h => ⟨?_, ?_⟩⟩
  · unfold cas negT
    simp only [neg_mul_neg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [eq_comm]
  · unfold cas
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Bool.not_inj_iff]
  · intro t
    obtain ⟨U, hU, hUn⟩ := h t
    exact ⟨U, hU, unitOn_negT s F U hUn⟩
  · intro t
    obtain ⟨U, hU, hUn⟩ := h t
    exact ⟨U, hU, unitOn_not s F U hUn⟩

end GlobalTheory.HoweR
