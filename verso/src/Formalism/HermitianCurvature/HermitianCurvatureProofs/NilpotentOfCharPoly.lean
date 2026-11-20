import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartSysWOfPartsOf

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix Polynomial
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `n M h`. Establish `hmon` using `Matrix.charpoly_monic M`. Establish `hdeg : M.charpoly.natDegree = n`. Rewrite using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Establish `hX : M.charpoly = (X : ℂ[X]) ^ n`.

Use extensionality with `i`. Rewrite using `[Polynomial.coeff_X_pow]`. Break down `lt_trichotomy i n with hi | hi | hi` into its components or cases. Rewrite using `[if_neg (by omega)]`. Use `h (n - i) (by omega) (by omega)` as an intermediate fact.

Rewrite `this` using `[show n - (n - i) = i by omega]`. Then use the resulting hypothesis. Rewrite using `[if_pos hi]`. Establish `h1` using `hmon.coeff_natDegree`. Rewrite `h1` using `[hdeg]`. Rewrite using `[hi]`.

Conclude with `h1`. Rewrite using `[if_neg (by omega)]`. Conclude with `Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Use `Matrix.aeval_self_charpoly M` as an intermediate fact.

Rewrite `this` using `[hX, map_pow, Polynomial.aeval_X]`. Then use the resulting hypothesis.
-/
theorem nilpotent_of_char_poly : NilOfCharpoly := by
  intro n M h
  have hmon := Matrix.charpoly_monic M
  have hdeg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hX : M.charpoly = (X : ℂ[X]) ^ n := by
    ext i
    rw [Polynomial.coeff_X_pow]
    rcases lt_trichotomy i n with hi | hi | hi
    · rw [if_neg (by omega)]
      have := h (n - i) (by omega) (by omega)
      rwa [show n - (n - i) = i by omega] at this
    · rw [if_pos hi]
      have h1 := hmon.coeff_natDegree
      rw [hdeg] at h1
      rw [hi]; exact h1
    · rw [if_neg (by omega)]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  refine ⟨n, ?_⟩
  have := Matrix.aeval_self_charpoly M
  rwa [hX, map_pow, Polynomial.aeval_X] at this

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
