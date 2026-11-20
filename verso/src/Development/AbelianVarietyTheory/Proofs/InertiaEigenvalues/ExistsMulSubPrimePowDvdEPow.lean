import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.BK

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem exists_mul_sub_pow_dvd_of_dvd_sub : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M m : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X → ∃ (N : ℕ) (r : bk.S), bk.E ^ m ∣ q * r - (l : bk.S) ^ N := by
  intro l _ K bk M m q hq
  obtain ⟨w, hw⟩ := bk.coeff_zero
  obtain ⟨t, ht⟩ := hq
  set P : bk.S := ((bk.Ep.divX : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) with hP
  have hE : bk.E = X * P + (l : bk.S) * C (w : Wq l bk.a) := by
    have h := Polynomial.X_mul_divX_add bk.Ep
    have h2 := congrArg (fun p : Polynomial (Wq l bk.a) => (p : (Wq l bk.a)⟦X⟧)) h
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C, hw, map_mul,
      map_natCast] at h2
    change (bk.Ep : (Wq l bk.a)⟦X⟧) = _
    rw [← h2, hP]
    congr 2
    rw [← map_natCast (Polynomial.C (R := Wq l bk.a)), Polynomial.coe_C, map_natCast]
  have hu : C (w : Wq l bk.a) * C ((w⁻¹ : (Wq l bk.a)ˣ) : Wq l bk.a) = (1 : bk.S) := by
    rw [← map_mul, Units.mul_inv, map_one]
  set c' : bk.S := C ((w⁻¹ : (Wq l bk.a)ˣ) : Wq l bk.a)
  set a : bk.S := (l : bk.S) ^ (M + 1)
  set h₁ : bk.S := -((l : bk.S) ^ M + t * P) * c'
  set b : bk.S := bk.E * h₁
  have hqr : q * (-c' * P) = a + b := by
    simp only [a, b, h₁]
    linear_combination (-c' * P) * ht + (c' * (l : bk.S) ^ M) * hE + (l : bk.S) ^ (M + 1) * hu
  have key := geom_sum₂_mul a (-b) m
  rw [sub_neg_eq_add] at key
  refine ⟨(M + 1) * m, (-c' * P) * ∑ i ∈ Finset.range m, a ^ i * (-b) ^ (m - 1 - i), -((-h₁) ^ m), ?_⟩
  rw [pow_mul, ← mul_assoc, hqr, mul_comm (a + b), key]
  simp only [b]
  rw [neg_pow, mul_pow, neg_pow h₁]
  ring

end GlobalTheory.BSP.BK
