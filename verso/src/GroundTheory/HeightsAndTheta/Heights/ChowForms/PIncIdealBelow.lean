import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

private def shiftGroup {e n : ℕ} (ij : Fin e × Fin n) : Fin (e + 1) × Fin n := (ij.1.succ, ij.2)

/- English proof (translation)
Introduce and unpack `⟨a, b⟩ ⟨c, d⟩ h`. Simplify using `only [shiftGroup, Prod.mk.injEq, Fin.succ_inj] at h`. Rewrite using `[h.1, h.2]`.
-/
private theorem shiftGroup_injective {e n : ℕ} : Function.Injective (shiftGroup (e := e) (n := n)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [shiftGroup, Prod.mk.injEq, Fin.succ_inj] at h
  rw [h.1, h.2]

private def killFirst {F : Type*} [Field F] {e n : ℕ} (ij : Fin (e + 1) × Fin n) :
    MvPolynomial (Fin (e + 1) × Fin n) F :=
  if ij.1 = 0 then 0 else X ij

/- English proof (translation)
Rewrite using `[aeval_def, eval₂_eq]`. Use `Finset.sum_eq_zero fun d hd => ?_` and prove the remaining obligations. Establish `hw` using `congrFun (hf (mem_support_iff.mp hd)) 0`. Rewrite `hw` using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Establish `hne : (∑ c ∈ d.support, (d c • groupWeight (e + 1) n c) 0) ≠ 0` using `by rw [hw]; omega`.

Take `⟨ij, hij, hij0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hne`. Establish `h1 : ij.1 = 0`. Assume the negation of the conclusion as `h`. Apply `hij0` to reduce the goal to its premises. Simplify using `[groupWeight, Ne.symm h]`.

Use `mul_eq_zero_of_right _ (Finset.prod_eq_zero hij ?_)` and prove the remaining obligations. Rewrite using `[killFirst, if_pos h1]`. Conclude with `zero_pow (Finsupp.mem_support_iff.mp hij)`.
-/
private theorem aeval_killFirst_eq_zero {F : Type*} [Field F] {e n δ : ℕ} (hδ : 1 ≤ δ)
    {f : MvPolynomial (Fin (e + 1) × Fin n) F} (hf : IsMultiHomog δ f) :
    aeval (killFirst (F := F)) f = 0 := by
  classical
  rw [aeval_def, eval₂_eq]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw := congrFun (hf (mem_support_iff.mp hd)) 0
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at hw
  have hne : (∑ c ∈ d.support, (d c • groupWeight (e + 1) n c) 0) ≠ 0 := by rw [hw]; omega
  obtain ⟨ij, hij, hij0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have h1 : ij.1 = 0 := by
    by_contra h
    apply hij0
    simp [groupWeight, Ne.symm h]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hij ?_)
  rw [killFirst, if_pos h1]
  exact zero_pow (Finsupp.mem_support_iff.mp hij)

/- English proof (translation)
Introduce `F _ n e I f hI hf`. Take `⟨δ, hδ, hmh⟩` from `h₁ F n (e + 1) I f hI hf`. Rewrite using `[eq_bot_iff]`. Introduce `g hg`. Rewrite using `[Ideal.mem_bot]`.

Use `set g' : MvPolynomial (Fin (e + 1) × Fin n) F := rename shiftGroup g with hg'`. Establish `hvan : ∀ v ∈ incidence I (e + 1), aeval v g' = 0`. Introduce and unpack `v ⟨x, hx0, hxI, hxv⟩`. Rewrite using `[hg', aeval_rename]`. Conclude with `(mem_incIdeal_iff.mp hg) (v ∘ shiftGroup) ⟨x, hx0, hxI, fun i => hxv i.succ⟩`.

Take `⟨h, hh⟩` from `(hf.2 g').mp hvan`. Establish `hfix : aeval (killFirst (F` using `F)) g' = g' := by`. Rewrite using `[hg', aeval_rename]`. Use `conv_rhs => rw [← aeval_X_left_apply (rename shiftGroup g), aeval_rename]`. Use `congr 1`.

Establish `hzero : g' = 0`. Rewrite using `[← hfix, hh, map_mul, aeval_killFirst_eq_zero hδ hmh, zero_mul]`. Conclude with `rename_injective _ shiftGroup_injective (by rw [← hg', hzero, map_zero])`.
-/
theorem IncIdealBelow.proof (h₁ : ChowFormMultiHomog.Statement) : IncIdealBelow.Statement := by
  intro F _ n e I f hI hf
  classical
  obtain ⟨δ, hδ, hmh⟩ := h₁ F n (e + 1) I f hI hf
  rw [eq_bot_iff]
  intro g hg
  rw [Ideal.mem_bot]
  set g' : MvPolynomial (Fin (e + 1) × Fin n) F := rename shiftGroup g with hg'
  have hvan : ∀ v ∈ incidence I (e + 1), aeval v g' = 0 := by
    rintro v ⟨x, hx0, hxI, hxv⟩
    rw [hg', aeval_rename]
    exact (mem_incIdeal_iff.mp hg) (v ∘ shiftGroup) ⟨x, hx0, hxI, fun i => hxv i.succ⟩
  obtain ⟨h, hh⟩ := (hf.2 g').mp hvan
  have hfix : aeval (killFirst (F := F)) g' = g' := by
    rw [hg', aeval_rename]
    conv_rhs => rw [← aeval_X_left_apply (rename shiftGroup g), aeval_rename]
    congr 1
  have hzero : g' = 0 := by
    rw [← hfix, hh, map_mul, aeval_killFirst_eq_zero hδ hmh, zero_mul]
  exact rename_injective _ shiftGroup_injective (by rw [← hg', hzero, map_zero])

end

end GroundTheory.Heights₂.Heights
