import Mathlib
import Formalism.DistinguishedUnitIdeals.CoprimeProd

noncomputable section

namespace Formalism.ExponentWindows

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `h1` using `hU _ ih`. Establish `e0 : (γ ^ (n + 1)) w = γ ((γ ^ n) w)` using `by rw [pow_succ']; rfl`.

Establish `e : (γ ^ (n + 1)) w - w = γ ((γ ^ n) w - w) + (γ w - w)`. Rewrite using `[e0, map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `U.add_mem h1 hw`.
-/
theorem pow_apply_sub_mem {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (γ : Module.End R M) (U : Submodule R M) (hU : ∀ u ∈ U, γ u ∈ U) (w : M)
    (hw : γ w - w ∈ U) (n : ℕ) : (γ ^ n) w - w ∈ U := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := hU _ ih
    have e0 : (γ ^ (n + 1)) w = γ ((γ ^ n) w) := by rw [pow_succ']; rfl
    have e : (γ ^ (n + 1)) w - w = γ ((γ ^ n) w - w) + (γ w - w) := by
      rw [e0, map_sub]; abel
    rw [e]
    exact U.add_mem h1 hw

/- English proof (translation)
Proceed by induction on `P using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Establish `e : Polynomial.aeval γ (p + q) w - (p + q).eval 1 • w = (Polynomial.aeval γ p w - p.eval 1 • w) + (Polynomial.aeval γ q w - q.eval 1 • w)`. Rewrite using `[map_add, LinearMap.add_apply, Polynomial.eval_add, add_smul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `U.add_mem hp hq`. Consider the case `monomial n a`. Establish `e : Polynomial.aeval γ (Polynomial.monomial n a) w - (Polynomial.monomial n a).eval 1 • w = a • ((γ ^ n) w - w)`. Rewrite using `[Polynomial.aeval_monomial, Polynomial.eval_monomial, one_pow, mul_one, smul_sub]`.

Use `congr 1`. Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `simp [Module.algebraMap_end_apply]`. Rewrite using `[e]`.

Conclude with `U.smul_mem a (pow_apply_sub_mem γ U hU w hw n)`.
-/
theorem aeval_apply_sub_eval_one_mem {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (γ : Module.End R M) (U : Submodule R M) (hU : ∀ u ∈ U, γ u ∈ U) (w : M)
    (hw : γ w - w ∈ U) (P : Polynomial R) :
    Polynomial.aeval γ P w - P.eval 1 • w ∈ U := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    have e : Polynomial.aeval γ (p + q) w - (p + q).eval 1 • w =
        (Polynomial.aeval γ p w - p.eval 1 • w) + (Polynomial.aeval γ q w - q.eval 1 • w) := by
      rw [map_add, LinearMap.add_apply, Polynomial.eval_add, add_smul]; abel
    rw [e]
    exact U.add_mem hp hq
  | monomial n a =>
    have e : Polynomial.aeval γ (Polynomial.monomial n a) w - (Polynomial.monomial n a).eval 1 • w =
        a • ((γ ^ n) w - w) := by
      rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, one_pow, mul_one, smul_sub]
      congr 1
      all_goals first
        | rfl
        | simp [Module.algebraMap_end_apply]
    rw [e]
    exact U.smul_mem a (pow_apply_sub_mem γ U hU w hw n)

/- English proof (translation)
Introduce `R M _ _ _ γ U hU P w hw`. Conclude with `aeval_apply_sub_eval_one_mem γ U hU w hw P`.
-/
theorem aeval_sub_eval_one_smul_mem : KillerShift := by
  intro R M _ _ _ γ U hU P w hw
  exact aeval_apply_sub_eval_one_mem γ U hU w hw P

/- English proof (translation)
Introduce `k V _ _ _ γ U hU Q₀ hQ hkill w hw`. Establish `hm` using `aeval_apply_sub_eval_one_mem γ U hU w hw Q₀`. Use `set c := Q₀.eval 1 with hc`. Use `set x := Polynomial.aeval γ Q₀ w with hx`. Use `⟨c⁻¹ • x, w - c⁻¹ • x, ?_, ?_, by abel⟩` and prove the remaining obligations.

Establish `h` using `hkill w`. Rewrite `h` using `[map_mul, map_sub, Polynomial.aeval_X, map_one]`. Express the relevant statement in the definitionally equal form `(γ - 1) x = 0 at h`. Rewrite `h` using `[LinearMap.sub_apply]`. Express the relevant statement in the definitionally equal form `γ x - x = 0 at h`.

Rewrite using `[map_smul, sub_eq_zero.mp h]`. Establish `e : w - c⁻¹ • x = (-c⁻¹) • (x - c • w)`. Rewrite using `[smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hQ, neg_smul, neg_smul, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `U.smul_mem _ hm`.
-/
theorem exists_fixed_add_of_sub_mem : InvConst := by
  intro k V _ _ _ γ U hU Q₀ hQ hkill w hw
  have hm := aeval_apply_sub_eval_one_mem γ U hU w hw Q₀
  set c := Q₀.eval 1 with hc
  set x := Polynomial.aeval γ Q₀ w with hx
  refine ⟨c⁻¹ • x, w - c⁻¹ • x, ?_, ?_, by abel⟩
  · have h := hkill w
    rw [map_mul, map_sub, Polynomial.aeval_X, map_one] at h
    change (γ - 1) x = 0 at h
    rw [LinearMap.sub_apply] at h
    change γ x - x = 0 at h
    rw [map_smul, sub_eq_zero.mp h]
  · have e : w - c⁻¹ • x = (-c⁻¹) • (x - c • w) := by
      rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hQ, neg_smul, neg_smul, one_smul]; abel
    rw [e]
    exact U.smul_mem _ hm

end Formalism.ExponentWindows
