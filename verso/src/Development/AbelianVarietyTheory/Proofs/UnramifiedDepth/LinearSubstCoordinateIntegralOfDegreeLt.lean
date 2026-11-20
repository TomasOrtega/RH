import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupCoordinatesPullbackLinearTangentBasisStatement

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

/- English proof (translation)
Introduce `C _ V d I J _ _ G S t ht N e he μ hμ c`. Establish `hz : ∀ b j, V.Ge 0 (S.co (Sum.elim (e j) (0 : J → C)) b)` using `fun b j => S.co_int (fun n => by`. Consider the cases of `n with`. Consider the case `inl x => exact he j x`. Consider the case `inr κ => exact VF.Ge.zero 0) b`.

Take `⟨h0, h1, -⟩` from `GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis C V d I J G S t ht (Fin N) e (fun b j => S.co (Sum.elim (e j) (0 : J → C)) b) (fun c k b => if k = 0 then (if c = b then 1 else 0) else S.co (S.cur c k) b) (fun j x => (S.co_spec (Sum.elim (e j) (0 : J → C)) x).sy …`. Establish `hk' : k ≠ 0` using `by omega`. Simplify using `only [if_neg hk', Sys.al, S.cur_zero_inl]`. Conclude with `(S.co_spec (S.cur c k) x).symm)`. Establish `h2` using `h1 c μ`.

Rewrite `h2` using `[Finset.sum_range_succ', Finset.sum_eq_zero, zero_add]`. Simplify using `only [if_true, pow_zero, pow_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ] at h2`. Rewrite using `[h2, map_sum]`. Use `VF.Ge.sum fun j _ => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]`.

Use `(hz c j).mul_int ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `VF.Ge.one`. Conclude with `VF.Ge.zero 0`. Introduce `s _`.

Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_of_lt_order, mul_zero]`. Use `lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (h0 b))` and prove the remaining obligations. Establish `: V.l ≤ V.l ^ (s + 1)` using `Nat.le_self_pow (Nat.succ_ne_zero s) _`. Conclude with `lt_of_lt_of_le hμ this` after adjusting the coercions.
-/
theorem linPull_coord_int_of_degree_lt :
    ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (e : Fin N → I → C), (∀ j x, V.Ge 0 (e j x)) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l → ∀ c, V.Ge 0 (MvPowerSeries.coeff μ (linPull e (t c))) := by
  intro C _ V d I J _ _ G S t ht N e he μ hμ c
  have hz : ∀ b j, V.Ge 0 (S.co (Sum.elim (e j) (0 : J → C)) b) := fun b j =>
    S.co_int (fun n => by
      cases n with
      | inl x => exact he j x
      | inr κ => exact VF.Ge.zero 0) b
  obtain ⟨h0, h1, -⟩ := GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis C V d I J G S t ht (Fin N) e
    (fun b j => S.co (Sum.elim (e j) (0 : J → C)) b)
    (fun c k b => if k = 0 then (if c = b then 1 else 0) else S.co (S.cur c k) b)
    (fun j x => (S.co_spec (Sum.elim (e j) (0 : J → C)) x).symm)
    (fun c b => by simp)
    (fun c k x hk => by
      have hk' : k ≠ 0 := by omega
      simp only [if_neg hk', Sys.al, S.cur_zero_inl]
      exact (S.co_spec (S.cur c k) x).symm)
  have h2 := h1 c μ
  rw [Finset.sum_range_succ', Finset.sum_eq_zero, zero_add] at h2
  · simp only [if_true, pow_zero, pow_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ] at h2
    rw [h2, map_sum]
    refine VF.Ge.sum fun j _ => ?_
    rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    refine (hz c j).mul_int ?_
    split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  · intro s _
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [MvPowerSeries.coeff_of_lt_order, mul_zero]
    refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (h0 b))
    have : V.l ≤ V.l ^ (s + 1) := Nat.le_self_pow (Nat.succ_ne_zero s) _
    exact_mod_cast lt_of_lt_of_le hμ this

end GlobalTheory.MainTerm
