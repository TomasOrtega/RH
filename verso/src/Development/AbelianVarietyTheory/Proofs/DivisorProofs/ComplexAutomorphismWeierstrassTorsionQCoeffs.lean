import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.CoeffConj

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
/- English proof (translation)
Simplify using `[_root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.dg, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]`.
-/
private theorem vmul_dg_apply_zero_and_one {N : ℕ} (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ) :
    _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) 0 = x 0 ∧
      _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) 1 = (a : ZMod N) * x 1 := by
  simp [_root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.dg, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
/- English proof (translation)
Unfold `_root_.GlobalTheory.WpFam.cG`. Apply the tactic sequence `split_ifs <;> simp [map_ofNat]`.
-/
private theorem ringEquiv_cG_eq (N : ℕ) (g : ℂ ≃+* ℂ) (k : ℕ) :
    g (_root_.GlobalTheory.WpFam.cG N k) = _root_.GlobalTheory.WpFam.cG N k := by
  unfold _root_.GlobalTheory.WpFam.cG
  split_ifs <;> simp [map_ofNat]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
/- English proof (translation)
Take `⟨h0, h1⟩` from `vmul_dg_apply_zero_and_one x a`. Unfold `_root_.GlobalTheory.WpFam.ZetaAct at hg`. Unfold `_root_.GlobalTheory.WpFam.cSum`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[h0, h1]`. Simplify using `only [map_mul, map_pow, map_natCast, map_add, apply_ite g, map_zero, hs, hg]`. Rewrite using `[mul_neg, mul_left_comm (a : ZMod N)]`.
-/
private theorem ringEquiv_cSum_eq_cSum_vmul_dg (N : ℕ) (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ)
    (hg : _root_.GlobalTheory.WpFam.ZetaAct g N a) (e : ℕ) (s : ℂ) (hs : g s = s) (x : Fin 2 → ZMod N)
    (k : ℕ) :
    g (_root_.GlobalTheory.WpFam.cSum N e s x k) =
      _root_.GlobalTheory.WpFam.cSum N e s (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
  obtain ⟨h0, h1⟩ := vmul_dg_apply_zero_and_one x a
  unfold _root_.GlobalTheory.WpFam.ZetaAct at hg
  unfold _root_.GlobalTheory.WpFam.cSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [h0, h1]
  simp only [map_mul, map_pow, map_natCast, map_add, apply_ite g, map_zero, hs, hg]
  rw [mul_neg, mul_left_comm (a : ZMod N)]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in

/- English proof (translation)
Introduce `N _ g a hg x k`. Take `⟨h0, h1⟩` from `vmul_dg_apply_zero_and_one x a`. Establish `hζ` using `hg`. Unfold `_root_.GlobalTheory.WpFam.ZetaAct at hζ`. Establish `hG` using `ringEquiv_cG_eq N g k`.

Establish `hB : g (_root_.GlobalTheory.WpFam.cB N x k) = _root_.GlobalTheory.WpFam.cB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k`. Unfold `_root_.GlobalTheory.WpFam.cB`. Break down `eq_or_ne k 0 with rfl | hk` into its components or cases. Simplify using `only [if_true, h0, h1] split_ifs`. Simplify using `only [map_div₀, map_pow, map_sub, map_one, hζ]`.

Conclude with `map_zero g`. Simplify using `only [hk, if_false]`. Conclude with `ringEquiv_cSum_eq_cSum_vmul_dg N g a hg 1 1 (map_one g) x k`. Establish `hD : g (_root_.GlobalTheory.WpFam.cD N x k) = _root_.GlobalTheory.WpFam.cD N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k`. Unfold `_root_.GlobalTheory.WpFam.cD`.

Break down `eq_or_ne k 0 with rfl | hk` into its components or cases. Simplify using `only [if_true, h0, h1] split_ifs`. Simplify using `only [map_div₀, map_pow, map_sub, map_add, map_mul, map_one, hζ]`. Conclude with `map_zero g`. Simplify using `only [hk, if_false]`.

Conclude with `ringEquiv_cSum_eq_cSum_vmul_dg N g a hg 2 (-1) (by simp) x k`. Use `⟨hB, hD, hG, ?_⟩` and prove the remaining obligations. Establish `hzero` using `(_root_.GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x (_root_.GlobalTheory.WpFam.dg a)`. Unfold `_root_.GlobalTheory.WpFam.cP`. Distinguish the cases in `hx : x = 0`.

Rewrite using `[if_pos hx, if_pos (hzero.2 hx), map_zero]`. Establish `hx' : _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) ≠ 0` using `fun h => hx (hzero.1 h)`. Simplify using `only [hx, hx', if_false, map_sub, hB, hG]`.
-/
theorem _root_.GlobalTheory.WpFam.CoeffConj.main : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.ZetaAct g N a → ∀ (x : Fin 2 → ZMod N) (k : ℕ), g (_root_.GlobalTheory.WpFam.cB N x k) = _root_.GlobalTheory.WpFam.cB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k ∧ g (_root_.GlobalTheory.WpFam.cD N x k) = _root_.GlobalTheory.WpFam.cD N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k ∧ g (_root_.GlobalTheory.WpFam.cG N k) = _root_.GlobalTheory.WpFam.cG N k ∧ g (_root_.GlobalTheory.WpFam.cP N x k) = _root_.GlobalTheory.WpFam.cP N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
  intro N _ g a hg x k
  obtain ⟨h0, h1⟩ := vmul_dg_apply_zero_and_one x a
  have hζ := hg
  unfold _root_.GlobalTheory.WpFam.ZetaAct at hζ
  have hG := ringEquiv_cG_eq N g k
  have hB : g (_root_.GlobalTheory.WpFam.cB N x k) =
      _root_.GlobalTheory.WpFam.cB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
    unfold _root_.GlobalTheory.WpFam.cB
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [if_true, h0, h1]
      split_ifs
      · simp only [map_div₀, map_pow, map_sub, map_one, hζ]
      · exact map_zero g
    · simp only [hk, if_false]
      exact ringEquiv_cSum_eq_cSum_vmul_dg N g a hg 1 1 (map_one g) x k
  have hD : g (_root_.GlobalTheory.WpFam.cD N x k) =
      _root_.GlobalTheory.WpFam.cD N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
    unfold _root_.GlobalTheory.WpFam.cD
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [if_true, h0, h1]
      split_ifs
      · simp only [map_div₀, map_pow, map_sub, map_add, map_mul, map_one, hζ]
      · exact map_zero g
    · simp only [hk, if_false]
      exact ringEquiv_cSum_eq_cSum_vmul_dg N g a hg 2 (-1) (by simp) x k
  refine ⟨hB, hD, hG, ?_⟩
  have hzero := (_root_.GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x (_root_.GlobalTheory.WpFam.dg a)
  unfold _root_.GlobalTheory.WpFam.cP
  by_cases hx : x = 0
  · rw [if_pos hx, if_pos (hzero.2 hx), map_zero]
  · have hx' : _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) ≠ 0 := fun h => hx (hzero.1 h)
    simp only [hx, hx', if_false, map_sub, hB, hG]

end GlobalTheory.WpFam.CoeffConj
