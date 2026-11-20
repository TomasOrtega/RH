import Mathlib

namespace GlobalTheory.IntegralNormAlgebraMap

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']`. Conclude with `a.2`.
-/
theorem norm_algebraMap_le_one {l : ℕ} [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
  exact a.2

/- English proof (translation)
Set `v : Valuation (PadicAlgCl l) NNReal` to `NormedField.valuation`. Establish `hv : ∀ y : PadicAlgCl l, v y ≤ 1 ↔ ‖y‖ ≤ 1` using `fun y => by`. Express the relevant statement in the definitionally equal form `‖y‖₊ ≤ 1 ↔ _`. Conclude with `Iff.rfl` after adjusting the coercions. Set `φ : ℤ_[l] →+* v.integer` to `(algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer (fun a => (hv _).2 (norm_algebraMap_le_one a))`.

Establish `h : IsIntegral v.integer x` using `IsIntegral.map_of_comp_eq φ (RingHom.id _) (by ext a; rfl) hx`. Conclude with `(hv x).1 (Valuation.Integers.mem_of_integral (Valuation.integer.integers v) h)`.
-/
theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  let v : Valuation (PadicAlgCl l) NNReal := NormedField.valuation
  have hv : ∀ y : PadicAlgCl l, v y ≤ 1 ↔ ‖y‖ ≤ 1 := fun y => by
    change ‖y‖₊ ≤ 1 ↔ _
    exact_mod_cast Iff.rfl
  let φ : ℤ_[l] →+* v.integer :=
    (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer
      (fun a => (hv _).2 (norm_algebraMap_le_one a))
  have h : IsIntegral v.integer x :=
    IsIntegral.map_of_comp_eq φ (RingHom.id _) (by ext a; rfl) hx
  exact (hv x).1 (Valuation.Integers.mem_of_integral (Valuation.integer.integers v) h)

end GlobalTheory.IntegralNormAlgebraMap
