import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

namespace GlobalTheory.BoundedScalarNorm

/- English proof (translation)
Establish `h : a • y = (a : ℚ_[l]) • y`. Rewrite using `[← IsScalarTower.algebraMap_smul ℚ_[l] a y]`. Both sides reduce to the same expression. Rewrite using `[h, norm_smul]`. Establish `h1 : ‖(a : ℚ_[l])‖ ≤ 1` using `a.2`.

Conclude with `mul_le_of_le_one_left (norm_nonneg _) h1`.
-/
theorem norm_smul_le_self {l : ℕ} [Fact l.Prime] (a : ℤ_[l]) (y : PadicAlgCl l) : ‖a • y‖ ≤ ‖y‖ := by
  have h : a • y = (a : ℚ_[l]) • y := by
    rw [← IsScalarTower.algebraMap_smul ℚ_[l] a y]; rfl
  rw [h, norm_smul]
  have h1 : ‖(a : ℚ_[l])‖ ≤ 1 := a.2
  exact mul_le_of_le_one_left (norm_nonneg _) h1

/- English proof (translation)
Take `⟨s, rfl⟩` from `h`. Use `⟨∑ z ∈ s, ‖z‖, fun y hy => ?_⟩` and prove the remaining obligations. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz => exact Finset.single_le_sum (f := fun z => ‖z‖) (fun _ _ => norm_nonneg _) hz`. Consider the case `zero => rw [norm_zero]`.

Conclude with `Finset.sum_nonneg fun _ _ => norm_nonneg _`. Consider the case `add u v _ _ hu hv => exact (IsUltrametricDist.norm_add_le_max u v).trans (max_le hu hv)`. Consider the case `smul a u _ hu => exact (norm_smul_le_self a u).trans hu`.
-/
theorem bounded {l : ℕ} [Fact l.Prime] (M : Submodule ℤ_[l] (PadicAlgCl l)) (h : M.FG) :
    ∃ C : ℝ, ∀ y ∈ M, ‖y‖ ≤ C := by
  obtain ⟨s, rfl⟩ := h
  refine ⟨∑ z ∈ s, ‖z‖, fun y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem z hz => exact Finset.single_le_sum (f := fun z => ‖z‖) (fun _ _ => norm_nonneg _) hz
  | zero => rw [norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  | add u v _ _ hu hv => exact (IsUltrametricDist.norm_add_le_max u v).trans (max_le hu hv)
  | smul a u _ hu => exact (norm_smul_le_self a u).trans hu

/- English proof (translation)
Introduce `l _ c x hx`. Establish `hfg : (Subalgebra.toSubmodule c.O).FG` using `Module.Finite.iff_fg.mp c.fin`. Take `⟨C, hC⟩` from `bounded _ hfg`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`.

Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt C hlt`. Use `hC (x ^ n) (c.O.pow_mem hx n)` as an intermediate fact. Rewrite `this` using `[norm_pow]`. Conclude with `absurd hn (not_lt.mpr this)`.
-/
theorem norm_le_one : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ UpperTheory.V.HV.Coef.O c → ‖x‖ ≤ (1 : ℝ) := by
  intro l _ c x hx
  have hfg : (Subalgebra.toSubmodule c.O).FG := Module.Finite.iff_fg.mp c.fin
  obtain ⟨C, hC⟩ := bounded _ hfg
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
  have := hC (x ^ n) (c.O.pow_mem hx n)
  rw [norm_pow] at this
  exact absurd hn (not_lt.mpr this)

end GlobalTheory.BoundedScalarNorm
