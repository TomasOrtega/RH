import Formalism.LocalToGlobal.Columns.TwQLevU
import Formalism.LocalToGlobal.Columns.ChainTwZero

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Val

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, s, hs, hsa⟩`. Establish `h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1` using `le_antisymm (P.valuation_le_one s) (not_lt.1 fun hlt => hs ((P.valuation_lt_one_iff_mem s).1 hlt))`. Establish `h2` using `congrArg (P.valuation E) hsa`. Rewrite `h2` using `[map_mul, h1, one_mul]`.

Rewrite using `[h2]`. Conclude with `P.valuation_le_one r`. Introduce `h`. Take `⟨r, s, hs, hsa⟩` from `qsp_frac (P := P) a h`. Conclude with `⟨r, s, hs, by rw [mul_comm]; exact hsa⟩`.
-/
theorem qth_intAt_iff (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, hsa⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 :=
      le_antisymm (P.valuation_le_one s)
        (not_lt.1 fun hlt => hs ((P.valuation_lt_one_iff_mem s).1 hlt))
    have h2 := congrArg (P.valuation E) hsa
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact P.valuation_le_one r
  · intro h
    obtain ⟨r, s, hs, hsa⟩ := qsp_frac (P := P) a h
    exact ⟨r, s, hs, by rw [mul_comm]; exact hsa⟩

/- English proof (translation)
Distinguish the cases in `hx : P.valuation E x = 0`. Conclude with `⟨0, by rw [hx]; exact zero_le'⟩`. Use `⟨(WithZero.log (P.valuation E x)).toNat, ?_⟩ conv_lhs => rw [← WithZero.exp_log hx]` and prove the remaining obligations. Conclude with `WithZero.exp_le_exp.2 (Int.self_le_toNat _)`.
-/
theorem qth_exists_bound (x : E) : ∃ k : ℕ, P.valuation E x ≤ WithZero.exp (k : ℤ) := by
  by_cases hx : P.valuation E x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · refine ⟨(WithZero.log (P.valuation E x)).toNat, ?_⟩
    conv_lhs => rw [← WithZero.exp_log hx]
    exact WithZero.exp_le_exp.2 (Int.self_le_toNat _)

/- English proof (translation)
Use `choose k hk using fun ij : Fin m × Fin m => qth_exists_bound P (M ij.1 ij.2)`. Use `⟨Finset.univ.sup k, fun i j => (hk (i, j)).trans ?_⟩` and prove the remaining obligations. Conclude with `WithZero.exp_le_exp.2 (Nat.cast_le.2 (Finset.le_sup (f := k) (Finset.mem_univ (i, j))))`.
-/
theorem qth_bound {m : ℕ} (M : Matrix (Fin m) (Fin m) E) : ∃ a : ℕ, ∀ i j, P.valuation E (M i j) ≤ WithZero.exp (a : ℤ) := by
  choose k hk using fun ij : Fin m × Fin m => qth_exists_bound P (M ij.1 ij.2)
  refine ⟨Finset.univ.sup k, fun i j => (hk (i, j)).trans ?_⟩
  exact WithZero.exp_le_exp.2 (Nat.cast_le.2 (Finset.le_sup (f := k) (Finset.mem_univ (i, j))))

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Valuation.map_sum_le _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, WithZero.exp_add]`. Use `mul_le_mul' ?_ (hB k j)` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`.

Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, WithZero.exp_add]`. Conclude with `mul_le_mul' (hA i l) (hZ l k)`.
-/
theorem qth_conj_le {m : ℕ} (A Z B : Matrix (Fin m) (Fin m) E) (a b N : ℤ)
    (hA : ∀ i j, P.valuation E (A i j) ≤ WithZero.exp a) (hZ : ∀ i j, P.valuation E (Z i j) ≤ WithZero.exp (-N))
    (hB : ∀ i j, P.valuation E (B i j) ≤ WithZero.exp b) (i j : Fin m) :
    P.valuation E ((A * Z * B) i j) ≤ WithZero.exp (a + -N + b) := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul, WithZero.exp_add]
  refine mul_le_mul' ?_ (hB k j)
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' (hA i l) (hZ l k)

end Val

end Formalism.L2.Col
