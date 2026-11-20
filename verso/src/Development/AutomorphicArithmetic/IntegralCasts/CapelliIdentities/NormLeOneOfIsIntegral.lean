import Mathlib

namespace UpperTheory.Reformulated.B.NormLeOneOfIsIntegral

/- English proof (translation)
Establish `hle : ∀ y : PadicAlgCl l, y ∈ (PadicAlgCl.valued l).v.integer ↔ ‖y‖ ≤ 1`. Introduce `y`. Rewrite using `[Valuation.mem_integer_iff, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]`. Establish `hmem : ∀ a : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) a ∈ (PadicAlgCl.valued l).v.integer`. Introduce `a`.

Rewrite using `[hle, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]`. Conclude with `(PadicAlgCl.norm_extends l _).trans_le a.2`. Establish `hint : IsIntegral (PadicAlgCl.valued l).v.integer x` using `hx.map_of_comp_eq ((algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict _ hmem) (RingHom.id _) rfl`. Conclude with `(hle x).1 ((Valuation.integer.integers (PadicAlgCl.valued l).v).mem_of_integral hint)`.
-/
theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hle : ∀ y : PadicAlgCl l,
      y ∈ (PadicAlgCl.valued l).v.integer ↔ ‖y‖ ≤ 1 := by
    intro y
    rw [Valuation.mem_integer_iff, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  have hmem : ∀ a : ℤ_[l],
      algebraMap ℤ_[l] (PadicAlgCl l) a ∈ (PadicAlgCl.valued l).v.integer := by
    intro a
    rw [hle, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact (PadicAlgCl.norm_extends l _).trans_le a.2
  have hint : IsIntegral (PadicAlgCl.valued l).v.integer x :=
    hx.map_of_comp_eq ((algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict _ hmem) (RingHom.id _) rfl
  exact (hle x).1 ((Valuation.integer.integers (PadicAlgCl.valued l).v).mem_of_integral hint)

end UpperTheory.Reformulated.B.NormLeOneOfIsIntegral
