import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace CompanionTheory.Member.TraceCoefficientSum

variable {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Simplify using `[zOf, MonoidAlgebra.coeff_sum, Finsupp.single_apply]`.
-/
theorem coeff_zOf (χ : G → ℂ) (x : G) : (zOf χ).coeff x = χ 1 / (Fintype.card G : ℂ) * χ x⁻¹ := by
  simp [zOf, MonoidAlgebra.coeff_sum, Finsupp.single_apply]

/- English proof (translation)
Use extensionality with `y`. Simplify using `[MonoidAlgebra.coeff_sum, Finsupp.single_apply]`.
-/
theorem eq_sum_single (a : MonoidAlgebra ℂ G) : a = ∑ x, MonoidAlgebra.single x (a.coeff x) := by
  ext y
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

/- English proof (translation)
Use `conv_lhs => rw [eq_sum_single a]`. Rewrite using `[Finset.sum_mul, MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[MonoidAlgebra.coeff_single_mul_apply, coeff_zOf, mul_one, inv_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_mul_zOf (a : MonoidAlgebra ℂ G) (χ : G → ℂ) :
    (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * ∑ x, a.coeff x * χ x := by
  conv_lhs => rw [eq_sum_single a]
  rw [Finset.sum_mul, MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MonoidAlgebra.coeff_single_mul_apply, coeff_zOf, mul_one, inv_inv]
  ring

/- English proof (translation)
Use `conv_rhs => rw [eq_sum_single a]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Representation.asAlgebraHom_single, map_smul, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem trace_alg (a : MonoidAlgebra ℂ G) (V : FDRep ℂ G) :
    ∑ x, a.coeff x * V.character x =
      LinearMap.trace ℂ V (Representation.asAlgebraHom (V.ρ : Representation ℂ G V) a) := by
  conv_rhs => rw [eq_sum_single a]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Representation.asAlgebraHom_single, map_smul, smul_eq_mul]
  rfl

/- English proof (translation)
Establish `hi : IsIdempotentElem (Representation.asAlgebraHom (V.ρ : Representation ℂ G V) a)`. Unfold `IsIdempotentElem`. Rewrite using `[← map_mul, ha]`. Rewrite using `[trace_alg]`. Conclude with `⟨_, (LinearMap.IsIdempotentElem.isProj_range _ hi).trace⟩`.
-/
theorem trace_nat (a : MonoidAlgebra ℂ G) (ha : a * a = a) (V : FDRep ℂ G) :
    ∃ m : ℕ, ∑ x, a.coeff x * V.character x = m := by
  have hi : IsIdempotentElem (Representation.asAlgebraHom (V.ρ : Representation ℂ G V) a) := by
    unfold IsIdempotentElem
    rw [← map_mul, ha]
  rw [trace_alg]
  exact ⟨_, (LinearMap.IsIdempotentElem.isProj_range _ hi).trace⟩

/- English proof (translation)
Take `⟨V, -, hV⟩` from `hχ`. Take `⟨m, hm⟩` from `trace_nat a ha V`. Rewrite using `[coeff_mul_zOf, ← hV 1, FDRep.char_one]`. Simplify using `only [← hV]`. Rewrite using `[hm, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast m, ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]`.

Check the signs of the components of the expression.
-/
theorem re_nonneg (a : MonoidAlgebra ℂ G) (ha : a * a = a) (χ : G → ℂ) (hχ : IsIrr χ) :
    0 ≤ ((a * zOf χ).coeff 1).re := by
  obtain ⟨V, -, hV⟩ := hχ
  obtain ⟨m, hm⟩ := trace_nat a ha V
  rw [coeff_mul_zOf, ← hV 1, FDRep.char_one]
  simp only [← hV]
  rw [hm, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast m,
    ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

end CompanionTheory.Member.TraceCoefficientSum

/- English proof (translation)
Introduce `g _ L n a ha h1 f`. Use `div_nonneg ?_ h1` and prove the remaining obligations. Unfold `eSerC`. Use `finsum_mem_induction (fun b => 0 ≤ ((a * b).coeff 1).re) (by simp) ?_ ?_` and prove the remaining obligations. Introduce `x y hx hy`.

Rewrite using `[mul_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, Complex.add_re]`. Conclude with `add_nonneg hx hy`. Introduce `χ hχ`. Conclude with `CompanionTheory.Member.TraceCoefficientSum.re_nonneg a ha χ hχ.1`.
-/
theorem CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (a : MonoidAlgebra ℂ (Gn g n)), a * a = a → 0 ≤ (a.coeff 1).re → ∀ f, 0 ≤ wtC L a f := by
  intro g _ L n a ha h1 f
  refine div_nonneg ?_ h1
  unfold eSerC
  refine finsum_mem_induction (fun b => 0 ≤ ((a * b).coeff 1).re) (by simp) ?_ ?_
  · intro x y hx hy
    rw [mul_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, Complex.add_re]
    exact add_nonneg hx hy
  · intro χ hχ
    exact CompanionTheory.Member.TraceCoefficientSum.re_nonneg a ha χ hχ.1

end

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
/- English proof (translation)
Apply the tactic sequence `first | exact @CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent | exact CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent | (intros; apply CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent <;> assumption)`.
-/
theorem _root_.GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (a : MonoidAlgebra ℂ (Gn g n)), a * a = a → 0 ≤ (a.coeff 1).re → ∀ f, 0 ≤ wtC L a f := by
  first | exact @CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent | exact CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent | (intros; apply CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent <;> assumption)

end
