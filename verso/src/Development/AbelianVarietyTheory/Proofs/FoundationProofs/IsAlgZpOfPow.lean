import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvOfFintype
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5

noncomputable section

namespace GlobalTheory.Glue.EvTwist

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def part (N i : ℤ) (a : Lau p) : Lau p where
  coeff r := if r % N = i then a.coeff r else 0
  isPWO_support' := a.isPWO_support.mono (fun r hr h => hr (by simp [h]))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem part_coeff (N i : ℤ) (a : Lau p) (r : ℤ) :
    (part N i a).coeff r = if r % N = i then a.coeff r else 0 := rfl

def contr (N : ℤ) (hN : 0 < N) (b : Lau p) : Lau p where
  coeff j := b.coeff (N * j)
  isPWO_support' := by
    refine Set.IsWF.isPWO (BddBelow.wellFoundedOn_lt ⟨-|b.order|, fun j hj => ?_⟩)
    have h : b.order ≤ N * j := HahnSeries.order_le_of_coeff_ne_zero hj
    have h1 := neg_abs_le b.order
    have h2 := abs_nonneg b.order
    by_contra hc
    push_neg at hc
    nlinarith

/- English proof (translation)
Establish `hN' : (0 : ℤ) < N` using `by exact_mod_cast hN`. Establish `h0` using `Int.emod_nonneg r hN'.ne'`. Establish `h1` using `Int.emod_lt_of_pos r hN'`. Rewrite using `[Finset.sum_eq_single (⟨(r % (N : ℤ)).toNat, by omega⟩ : Fin N)]`. Rewrite using `[if_pos (by simp only; omega)]`.

Introduce `i _ hi`. Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hi (Fin.ext (by simp only; omega))`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem sum_ite {M : Type} [AddCommMonoid M] (N : ℕ) (hN : 0 < N) (r : ℤ) (f : ℕ → M) :
    ∑ i : Fin N, (if r % (N : ℤ) = ((i : ℕ) : ℤ) then f i else 0) = f (r % (N : ℤ)).toNat := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h0 := Int.emod_nonneg r hN'.ne'
  have h1 := Int.emod_lt_of_pos r hN'
  rw [Finset.sum_eq_single (⟨(r % (N : ℤ)).toNat, by omega⟩ : Fin N)]
  · rw [if_pos (by simp only; omega)]
  · intro i _ hi
    rw [if_neg]
    intro h
    exact hi (Fin.ext (by simp only; omega))
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Assemble the required witnesses or components as `⟨Polynomial.X ^ N - 1, by simpa using Polynomial.X_pow_sub_C_ne_zero hN (1 : ℤ_[p]), by simp [h]⟩`.
-/
theorem isAlgZp_of_pow {z : Ω} {N : ℕ} (hN : 0 < N) (h : z ^ N = 1) : IsAlgZp p z :=
  ⟨Polynomial.X ^ N - 1, by simpa using Polynomial.X_pow_sub_C_ne_zero hN (1 : ℤ_[p]), by simp [h]⟩

/- English proof (translation)
The claim follows from `IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)`.
-/
theorem isInt_of_pow {z : Ω} {N : ℕ} (hN : 0 < N) (h : z ^ N = 1) : IsInt p z :=
  IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)

end GlobalTheory.Glue.EvTwist
