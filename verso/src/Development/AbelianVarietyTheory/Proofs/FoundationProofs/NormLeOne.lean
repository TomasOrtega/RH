import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.MinkAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

namespace GlobalTheory.ScalarNormBound

variable {l : ℕ} [Fact (Nat.Prime l)]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem norm_smul_le_self (a : ℤ_[l]) (y : PadicAlgCl l) : ‖a • y‖ ≤ ‖y‖ := by
  have ha : ‖(a : ℚ_[l])‖ ≤ 1 := a.2
  have hs : a • y = (a : ℚ_[l]) • y := (algebraMap_smul ℚ_[l] a y).symm
  rw [hs, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg y) ha

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_bound (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [Module.Finite ℤ_[l] O] :
    ∃ C : ℝ, ∀ y : O, ‖(y : PadicAlgCl l)‖ ≤ C := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] O).FG)
  have hnn : ∀ z ∈ s, 0 ≤ ‖((z : O) : PadicAlgCl l)‖ := fun z _ => norm_nonneg _
  refine ⟨∑ z ∈ s, ‖((z : O) : PadicAlgCl l)‖, fun y => ?_⟩
  have hy : y ∈ Submodule.span ℤ_[l] (s : Set O) := hs ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact Finset.single_le_sum hnn hx
  | zero => simpa using Finset.sum_nonneg hnn
  | add x z _ _ hx hz =>
    have e : ((x + z : O) : PadicAlgCl l) = (x : PadicAlgCl l) + (z : PadicAlgCl l) := rfl
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hz)
  | smul a x _ hx =>
    have e : ((a • x : O) : PadicAlgCl l) = a • (x : PadicAlgCl l) := rfl
    rw [e]
    exact (norm_smul_le_self a _).trans hx

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_le_one : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) (x : ↥(UpperTheory.V.HV.Coef.O c)), ‖(↑x : PadicAlgCl l)‖ ≤ (1 : ℝ) := by
  intro l _ c x
  obtain ⟨C, hC⟩ := exists_bound (UpperTheory.V.HV.Coef.O c)
  by_contra h
  rw [not_le] at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have hb := hC (x ^ n)
  have e : ‖((x ^ n : UpperTheory.V.HV.Coef.O c) : PadicAlgCl l)‖ = ‖(x : PadicAlgCl l)‖ ^ n := by
    rw [SubmonoidClass.coe_pow, norm_pow]
  linarith

end GlobalTheory.ScalarNormBound
