import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

/- English proof (translation)
Introduce `N m _hm`. Use `⟨fun i => ((i : ℕ) : ℝ), fun i => (Lagrange.basis (Finset.univ : Finset (Fin (N + 1))) (fun j => ((j : ℕ) : ℂ)) i).coeff m, ?_⟩` and prove the remaining obligations. Introduce `q hq`. Establish `hinj : Set.InjOn (fun j : Fin (N + 1) => ((j : ℕ) : ℂ)) ((Finset.univ : Finset (Fin (N + 1))) : Set (Fin (N + 1)))`. Introduce `a _ b _ hab`.

Simplify using `only at hab`. Conclude with `Fin.ext (by exact_mod_cast hab)`. Establish `hdeg : q.degree < ((Finset.univ : Finset (Fin (N + 1))).card : WithBot ℕ)`. Rewrite using `[Finset.card_univ, Fintype.card_fin]`. Conclude with `lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hq) (by exact_mod_cast Nat.lt_succ_self N)`.

Establish `h` using `Lagrange.eq_interpolate hinj hdeg`. Use `conv_rhs => rw [h]`. Rewrite using `[Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_C_mul]`.

Simplify using `only [Complex.ofReal_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coefficient_interpolation_holds : CoeffInterp := by
  intro N m _hm
  refine ⟨fun i => ((i : ℕ) : ℝ),
    fun i => (Lagrange.basis (Finset.univ : Finset (Fin (N + 1))) (fun j => ((j : ℕ) : ℂ)) i).coeff m, ?_⟩
  intro q hq
  have hinj : Set.InjOn (fun j : Fin (N + 1) => ((j : ℕ) : ℂ)) ((Finset.univ : Finset (Fin (N + 1))) : Set (Fin (N + 1))) := by
    intro a _ b _ hab
    simp only at hab
    exact Fin.ext (by exact_mod_cast hab)
  have hdeg : q.degree < ((Finset.univ : Finset (Fin (N + 1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hq) (by exact_mod_cast Nat.lt_succ_self N)
  have h := Lagrange.eq_interpolate hinj hdeg
  conv_rhs => rw [h]
  rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.coeff_C_mul]
  simp only [Complex.ofReal_natCast]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
