import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Formalism.DoubleCosetMeasures.LatticeCoset

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem

/- English proof (translation)
Establish `hq1 : 1 < Fintype.card k` using `Fintype.one_lt_card`. Establish `hq0 : (Fintype.card k : ℝ) ≠ 0`. Establish `: 0 < Fintype.card k` using `by omega`. Conclude with `this.ne'` after adjusting the coercions. Establish `hconst : (Fintype.card k : ℝ) ^ (r * r) = ∏ _j ∈ Finset.Icc 1 r, (Fintype.card k : ℝ) ^ r`.

Rewrite using `[Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, ← pow_mul]`. Rewrite using `[Matrix.card_GL_field, Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => ((Fintype.card k ^ r - Fintype.card k ^ i : ℕ) : ℝ)) r, hconst, Formalism.MainNotions.ZetaProductPairs.qE, ← Finset.prod_mul_distrib]`. Use `Finset.prod_nbij' (fun i => r - i) (fun j => r - j) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `i hi`. Use `Finset.mem_range.mp hi` as an intermediate fact.

Conclude with `Finset.mem_Icc.mpr (by omega)`. Introduce `j hj`. Use `Finset.mem_Icc.mp hj` as an intermediate fact. Conclude with `Finset.mem_range.mpr (by omega)`. Introduce `i hi`.

Use `Finset.mem_range.mp hi` as an intermediate fact. Use `show r - (r - i) = i`. Use linear arithmetic over natural numbers and integers. Introduce `j hj`. Use `Finset.mem_Icc.mp hj` as an intermediate fact.

Use `show r - (r - j) = j`. Use linear arithmetic over natural numbers and integers. Introduce `i hi`. Establish `hir : i < r` using `Finset.mem_range.mp hi`. Establish `hle : Fintype.card k ^ i ≤ Fintype.card k ^ r` using `Nat.pow_le_pow_right (by omega) hir.le`.

Rewrite using `[Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]`. Use `congr 1`. Establish `hcast : (-((r - i : ℕ) : ℤ)) = (i : ℤ) - (r : ℤ)`. Rewrite using `[Nat.cast_sub hir.le]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hcast, zpow_sub₀ hq0, zpow_natCast, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.
-/
theorem card_GL_eq_pow_mul_qE (k : Type) [Field k] [Fintype k] (r : ℕ) :
    (Nat.card (GL (Fin r) k) : ℝ)
      = (Fintype.card k : ℝ) ^ (r * r) * Formalism.MainNotions.ZetaProductPairs.qE (Fintype.card k : ℝ) 1 r := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hq0 : (Fintype.card k : ℝ) ≠ 0 := by
    have : 0 < Fintype.card k := by omega
    exact_mod_cast this.ne'
  have hconst : (Fintype.card k : ℝ) ^ (r * r)
      = ∏ _j ∈ Finset.Icc 1 r, (Fintype.card k : ℝ) ^ r := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, ← pow_mul]
  rw [Matrix.card_GL_field, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range
      (fun i => ((Fintype.card k ^ r - Fintype.card k ^ i : ℕ) : ℝ)) r,
    hconst, Formalism.MainNotions.ZetaProductPairs.qE, ← Finset.prod_mul_distrib]
  refine Finset.prod_nbij' (fun i => r - i) (fun j => r - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr (by omega)
  · intro j hj
    have := Finset.mem_Icc.mp hj
    exact Finset.mem_range.mpr (by omega)
  · intro i hi
    have := Finset.mem_range.mp hi
    show r - (r - i) = i
    omega
  · intro j hj
    have := Finset.mem_Icc.mp hj
    show r - (r - j) = j
    omega
  · intro i hi
    have hir : i < r := Finset.mem_range.mp hi
    have hle : Fintype.card k ^ i ≤ Fintype.card k ^ r :=
      Nat.pow_le_pow_right (by omega) hir.le
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
    congr 1
    have hcast : (-((r - i : ℕ) : ℤ)) = (i : ℤ) - (r : ℤ) := by
      rw [Nat.cast_sub hir.le]; ring
    rw [hcast, zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    field_simp

end GlobalTheory.Mem
