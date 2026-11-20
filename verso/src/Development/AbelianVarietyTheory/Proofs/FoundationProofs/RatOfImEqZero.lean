import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH

namespace GlobalTheory.RationalOfReal

open IntermediateField

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Proceed by induction. Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components.

Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Move the embeddings inside the algebraic operations.

Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem exists_coords {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] (β : E) (d : ℚ)
    (hβ : β * β = -(d : E)) (y : E) (hy : y ∈ ℚ⟮β⟯) : ∃ u v : ℚ, y = (u : E) + (v : E) * β := by
  have hint : IsIntegral ℚ β := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have : β ^ 2 = algebraMap ℚ E (-d) := by rw [pow_two, hβ]; simp
    rw [this]
    exact isIntegral_algebraMap
  have hy' : y ∈ Algebra.adjoin ℚ ({β} : Set E) := by
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  clear hy
  induction hy' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    refine ⟨u * u' - d * v * v', u * v' + v * u', ?_⟩
    push_cast
    linear_combination (v : E) * (v' : E) * hβ

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem rat_of_im_eq_zero {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] (φ : E →+* ℂ) (β : E)
    (d : ℕ) (hd : 0 < d) (hφ : φ β = Complex.I * (Real.sqrt d : ℂ)) (y : E) (hy : y ∈ ℚ⟮β⟯)
    (him : (φ y).im = 0) : ∃ a : ℚ, y = (a : E) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hβ : β * β = -(((d : ℚ)) : E) := by
    apply φ.injective
    have h2 : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
      simp
    rw [map_mul, hφ, map_neg, map_ratCast]
    push_cast
    linear_combination (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) * Complex.I_mul_I - h2
  obtain ⟨u, v, rfl⟩ := exists_coords β d hβ y hy
  rw [map_add, map_mul, map_ratCast, map_ratCast, hφ] at him
  have hv : (v : ℝ) * Real.sqrt d = 0 := by simpa using him
  have hv0 : v = 0 := by
    have := (mul_eq_zero.1 hv).resolve_right hs.ne'
    exact_mod_cast this
  exact ⟨u, by simp [hv0]⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem rat_of_real (D : Formalism.BasicNotions.D7) (x : D.host.K)
    (hx : (D.host.φ₀ (x : D.host.E)).im = 0) : ∃ a : ℚ, x = (a : D.host.K) := by
  obtain ⟨a, ha⟩ := rat_of_im_eq_zero D.host.φ₀ (D.host.sqd) D.host.d
    D.host.hyp.2.1.pos D.host.φ₀_mem (x : D.host.E) x.2 hx
  exact ⟨a, Subtype.ext (by simpa using ha)⟩

end GlobalTheory.RationalOfReal
