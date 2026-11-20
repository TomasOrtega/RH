import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.MinkAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

namespace GlobalTheory.ScalarNormBound

variable {l : ℕ} [Fact (Nat.Prime l)]

/- English proof (translation)
Establish `ha : ‖(a : ℚ_[l])‖ ≤ 1` using `a.2`. Establish `hs : a • y = (a : ℚ_[l]) • y` using `(algebraMap_smul ℚ_[l] a y).symm`. Rewrite using `[hs, norm_smul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg y) ha`.
-/
theorem norm_smul_le_self (a : ℤ_[l]) (y : PadicAlgCl l) : ‖a • y‖ ≤ ‖y‖ := by
  have ha : ‖(a : ℚ_[l])‖ ≤ 1 := a.2
  have hs : a • y = (a : ℚ_[l]) • y := (algebraMap_smul ℚ_[l] a y).symm
  rw [hs, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg y) ha

/- English proof (translation)
Take `⟨s, hs⟩` from `(Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] O).FG)`. Establish `hnn : ∀ z ∈ s, 0 ≤ ‖((z : O) : PadicAlgCl l)‖` using `fun z _ => norm_nonneg _`. Use `⟨∑ z ∈ s, ‖((z : O) : PadicAlgCl l)‖, fun y => ?_⟩` and prove the remaining obligations. Establish `hy : y ∈ Submodule.span ℤ_[l] (s : Set O)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem x hx => exact Finset.single_le_sum hnn hx`. Consider the case `zero => simpa using Finset.sum_nonneg hnn`. Consider the case `add x z _ _ hx hz`. Establish `e : ((x + z : O) : PadicAlgCl l) = (x : PadicAlgCl l) + (z : PadicAlgCl l)` using `rfl`. Rewrite using `[e]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hz)`. Consider the case `smul a x _ hx`. Establish `e : ((a • x : O) : PadicAlgCl l) = a • (x : PadicAlgCl l)` using `rfl`. Rewrite using `[e]`. Conclude with `(norm_smul_le_self a _).trans hx`.
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
Introduce `l _ c x`. Take `⟨C, hC⟩` from `exists_bound (UpperTheory.V.HV.Coef.O c)`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_le]`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt C h`.

Establish `hb` using `hC (x ^ n)`. Establish `e : ‖((x ^ n : UpperTheory.V.HV.Coef.O c) : PadicAlgCl l)‖ = ‖(x : PadicAlgCl l)‖ ^ n`. Rewrite using `[SubmonoidClass.coe_pow, norm_pow]`. Combine the linear equalities and inequalities to obtain the conclusion.
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
