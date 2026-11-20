import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormTranslateSubLineDerivLe

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SliceTaylor

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_` and prove the remaining obligations. Consider the cases of `i with`. Consider the case `inl i => simpa [padL] using norm_le_pi_norm h i`. Consider the case `inr j => simp [padL]`.
-/
theorem norm_padL_le {κ κ' : Type} [Fintype κ] [Fintype κ'] (h : κ → V) :
    ‖(padL (κ' := κ') h : κ ⊕ κ' → V)‖ ≤ ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simpa [padL] using norm_le_pi_norm h i
  | inr j => simp [padL]

/- English proof (translation)
Use `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_` and prove the remaining obligations. Rewrite using `[one_mul]`. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_` and prove the remaining obligations. Consider the cases of `i with`. Consider the case `inl i => simp [inrL]`.

Consider the case `inr j => simpa [inrL] using norm_le_pi_norm y j`.
-/
theorem norm_inrL_le (κ κ' : Type) [Fintype κ] [Fintype κ'] :
    ‖(inrL (V := V) κ κ')‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simp [inrL]
  | inr j => simpa [inrL] using norm_le_pi_norm y j

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_` and prove the remaining obligations. Use `norm_le_pi_norm ((Sum.elim x y : κ ⊕ κ' → V) + s • padL h) (Sum.inr j)` as an intermediate fact. Simplify using `only [Pi.add_apply, Pi.smul_apply, padL, Sum.elim_inr, Pi.zero_apply, smul_zero, add_zero] at this`. Conclude with `this`.
-/
theorem norm_le_norm_elim_add {κ κ' : Type} [Fintype κ] [Fintype κ'] (x h : κ → V) (y : κ' → V) (s : ℝ) :
    ‖y‖ ≤ ‖(Sum.elim x y : κ ⊕ κ' → V) + s • padL h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have := norm_le_pi_norm ((Sum.elim x y : κ ⊕ κ' → V) + s • padL h) (Sum.inr j)
  simp only [Pi.add_apply, Pi.smul_apply, padL, Sum.elim_inr, Pi.zero_apply, smul_zero, add_zero] at this
  exact this

/- English proof (translation)
Establish `e1 : (⇑(pd a g)) = fun y => fderiv ℝ g y a` using `by funext y; exact pd_apply a g y`. Establish `hd : Differentiable ℝ (iteratedFDeriv ℝ n g)` using `g.smooth'.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)`. Establish `e : iteratedFDeriv ℝ n (pd a g) w = fderiv ℝ (iteratedFDeriv ℝ n g) w a`. Use extensionality with `m`. Rewrite using `[e1, ← GlobalTheory.SchwartzTranslate.fderiv_iteratedFDeriv_apply_comm a n g g.smooth']`.

Use `((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => X) ℂ m).hasFDerivAt.comp w (hd w).hasFDerivAt).fderiv` as an intermediate fact. Establish `e2 : (fun y => iteratedFDeriv ℝ n g y m) = (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => X) ℂ m) ∘ iteratedFDeriv ℝ n g` using `rfl`. Rewrite using `[e2, this]`. Both sides reduce to the same expression. Rewrite using `[e, ← norm_fderiv_iteratedFDeriv, mul_comm]`.

Conclude with `(fderiv ℝ (iteratedFDeriv ℝ n g) w).le_opNorm a`.
-/
theorem norm_iteratedFDeriv_pd_le {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a : X) (g : SchwartzMap X ℂ) (n : ℕ) (w : X) :
    ‖iteratedFDeriv ℝ n (pd a g) w‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ (n + 1) g w‖ := by
  have e1 : (⇑(pd a g)) = fun y => fderiv ℝ g y a := by funext y; exact pd_apply a g y
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    g.smooth'.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
  have e : iteratedFDeriv ℝ n (pd a g) w = fderiv ℝ (iteratedFDeriv ℝ n g) w a := by
    ext m
    rw [e1, ← GlobalTheory.SchwartzTranslate.fderiv_iteratedFDeriv_apply_comm a n g g.smooth']
    have := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => X) ℂ m).hasFDerivAt.comp
      w (hd w).hasFDerivAt).fderiv
    have e2 : (fun y => iteratedFDeriv ℝ n g y m) =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => X) ℂ m) ∘ iteratedFDeriv ℝ n g := rfl
    rw [e2, this]
    rfl
  rw [e, ← norm_fderiv_iteratedFDeriv, mul_comm]
  exact (fderiv ℝ (iteratedFDeriv ℝ n g) w).le_opNorm a

/- English proof (translation)
Use function extensionality and compare the values at `i`. Consider the cases of `i with`. Consider the case `inl i => simp [padL]`. Consider the case `inr j => simp [padL]`.
-/
theorem elim_add_padL {κ κ' : Type} [Fintype κ] [Fintype κ'] (x h : κ → V) (y : κ' → V) :
    (Sum.elim (x + h) y : κ ⊕ κ' → V) = Sum.elim x y + padL h := by
  funext i
  cases i with
  | inl i => simp [padL]
  | inr j => simp [padL]

/- English proof (translation)
Use `set a : κ ⊕ κ' → V := padL (κ' := κ') h with ha`. Use `set f1 := pd a f with hf1`. Use `set f2 := pd a f1 with hf2`. Use `set M := ‖h‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f with hM`. Use `SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun y => ?_` and prove the remaining obligations.

Establish `hnn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞` using `by exact_mod_cast le_top`. Establish `c0 : ContDiff ℝ ∞ f` using `f.smooth'`. Establish `c1 : ContDiff ℝ ∞ f1` using `f1.smooth'`. Establish `e1 : (fun z => fderiv ℝ f z a) = ⇑f1` using `by funext z; exact (pd_apply a f z).symm`. Establish `e2 : (fun z => fderiv ℝ f1 z a) = ⇑f2` using `by funext z; exact (pd_apply a f1 z).symm`.

Use `set G : (κ ⊕ κ' → V) → ℂ := fun w => f (w + a) - f w - f1 w with hG`. Establish `cG : ContDiff ℝ ∞ G` using `((c0.comp (contDiff_id.add contDiff_const)).sub c0).sub c1`. Use `set c : κ ⊕ κ' → V := Sum.elim x 0 with hc`. Establish `efun : ⇑(sliceR f (x + h) - sliceR f x - sliceR f1 x) = (fun u => G (u + c)) ∘ ⇑(inrL (V` using `V) κ κ') := by`. Use function extensionality and compare the values at `y'`.

Establish `hy : (Sum.elim x y' : κ ⊕ κ' → V) = inrL κ κ' y' + c`. Rewrite using `[add_comm]`. Conclude with `congrFun (elim_eq_add x) y'`. Simplify using `only [SchwartzMap.sub_apply, sliceR_apply, Function.comp_apply, hG, ← hy, elim_add_padL, ha]`. Establish `cGc : ContDiff ℝ ∞ (fun u => G (u + c))` using `cG.comp (contDiff_id.add contDiff_const)`.

Establish `eit : iteratedFDeriv ℝ n ⇑(sliceR f (x + h) - sliceR f x - sliceR f1 x) y = (iteratedFDeriv ℝ n f (Sum.elim x y + a) - iteratedFDeriv ℝ n f (Sum.elim x y) - iteratedFDeriv ℝ n f1 (Sum.elim x y)).compContinuousLinearMap (fun _ => inrL (V` using `V) κ κ') := by`. Establish `hy : inrL (V` using `V) κ κ' y + c = Sum.elim x y := by`. Rewrite using `[add_comm]`. Conclude with `(congrFun (elim_eq_add x) y).symm`. Rewrite using `[efun, ContinuousLinearMap.iteratedFDeriv_comp_right _ cGc _ hnn, iteratedFDeriv_comp_add_right, hy]`.

Use `congr 1`. Establish `ct : ContDiff ℝ ∞ (fun z => f (z + a))` using `c0.comp (contDiff_id.add contDiff_const)`. Express the relevant statement in the definitionally equal form `iteratedFDeriv ℝ n (((fun z => f (z + a)) - ⇑f) - ⇑f1) _ = _`. Rewrite using `[iteratedFDeriv_sub_apply (f := (fun z => f (z + a)) - ⇑f) (g := ⇑f1) ((ct.sub c0).of_le hnn).contDiffAt (c1.of_le hnn).contDiffAt, iteratedFDeriv_sub_apply (ct.of_le hnn).contDiffAt (c0.of_le hnn).contDiffAt, iteratedFDeriv_comp_add_right]`. Rewrite using `[eit]`.

Use `set z : κ ⊕ κ' → V := Sum.elim x y with hz`. Establish `key` using `GlobalTheory.SchwartzTranslate.taylor_two (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f (z + s • a)) (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f1 (z + s • a)) (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f2 (z + s • a)) (fun s => by`. Use `GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line a n f c0 z s` as an intermediate fact. Rewrite `this` using `[e1]`. Conclude with `this.const_smul (‖y‖ ^ k))`.

Use the proof step `(fun s => by`. Use `GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line a n f1 c1 z s` as an intermediate fact. Rewrite `this` using `[e2]`. Conclude with `this.const_smul (‖y‖ ^ k))`. Use `M`.

Use the proof step `(fun s _ => by set w := z + s • a`. Establish `hyw : ‖y‖ ≤ ‖w‖` using `norm_le_norm_elim_add x h y s`. Establish `b1` using `norm_iteratedFDeriv_pd_le a f1 n w`. Establish `b2` using `norm_iteratedFDeriv_pd_le a f (n + 1) w`. Establish `hah : ‖a‖ ≤ ‖h‖` using `norm_padL_le h`.

Establish `hS` using `SchwartzMap.le_seminorm ℂ k (n + 2) f w`. Establish `hb : ‖iteratedFDeriv ℝ n f2 w‖ ≤ ‖h‖ ^ 2 * ‖iteratedFDeriv ℝ (n + 2) f w‖`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_smul, Real.norm_of_nonneg (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [zero_smul, add_zero, one_smul, one_pow, mul_one] at key`. Rewrite `key` using `[← smul_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Use `mul_le_of_le_one_right (norm_nonneg _) ?_` and prove the remaining obligations.

Conclude with `Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => norm_inrL_le κ κ')`. Use `_ ≤ M := key`.
-/
theorem seminorm_slice_taylor_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (k n : ℕ) (x h : κ → V) :
    SchwartzMap.seminorm ℂ k n (sliceR f (x + h) - sliceR f x - sliceR (pd (padL (κ' := κ') h) f) x) ≤
      ‖h‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f := by
  set a : κ ⊕ κ' → V := padL (κ' := κ') h with ha
  set f1 := pd a f with hf1
  set f2 := pd a f1 with hf2
  set M := ‖h‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f with hM
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun y => ?_
  have hnn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have c0 : ContDiff ℝ ∞ f := f.smooth'
  have c1 : ContDiff ℝ ∞ f1 := f1.smooth'
  have e1 : (fun z => fderiv ℝ f z a) = ⇑f1 := by funext z; exact (pd_apply a f z).symm
  have e2 : (fun z => fderiv ℝ f1 z a) = ⇑f2 := by funext z; exact (pd_apply a f1 z).symm
  set G : (κ ⊕ κ' → V) → ℂ := fun w => f (w + a) - f w - f1 w with hG
  have cG : ContDiff ℝ ∞ G :=
    ((c0.comp (contDiff_id.add contDiff_const)).sub c0).sub c1
  set c : κ ⊕ κ' → V := Sum.elim x 0 with hc
  have efun : ⇑(sliceR f (x + h) - sliceR f x - sliceR f1 x)
      = (fun u => G (u + c)) ∘ ⇑(inrL (V := V) κ κ') := by
    funext y'
    have hy : (Sum.elim x y' : κ ⊕ κ' → V) = inrL κ κ' y' + c := by
      rw [add_comm]; exact congrFun (elim_eq_add x) y'
    simp only [SchwartzMap.sub_apply, sliceR_apply, Function.comp_apply, hG, ← hy,
      elim_add_padL, ha]
  have cGc : ContDiff ℝ ∞ (fun u => G (u + c)) := cG.comp (contDiff_id.add contDiff_const)
  have eit : iteratedFDeriv ℝ n ⇑(sliceR f (x + h) - sliceR f x - sliceR f1 x) y
      = (iteratedFDeriv ℝ n f (Sum.elim x y + a) - iteratedFDeriv ℝ n f (Sum.elim x y)
          - iteratedFDeriv ℝ n f1 (Sum.elim x y)).compContinuousLinearMap
          (fun _ => inrL (V := V) κ κ') := by
    have hy : inrL (V := V) κ κ' y + c = Sum.elim x y := by
      rw [add_comm]; exact (congrFun (elim_eq_add x) y).symm
    rw [efun, ContinuousLinearMap.iteratedFDeriv_comp_right _ cGc _ hnn, iteratedFDeriv_comp_add_right, hy]
    congr 1
    have ct : ContDiff ℝ ∞ (fun z => f (z + a)) := c0.comp (contDiff_id.add contDiff_const)
    change iteratedFDeriv ℝ n (((fun z => f (z + a)) - ⇑f) - ⇑f1) _ = _
    rw [iteratedFDeriv_sub_apply (f := (fun z => f (z + a)) - ⇑f) (g := ⇑f1) ((ct.sub c0).of_le hnn).contDiffAt (c1.of_le hnn).contDiffAt,
      iteratedFDeriv_sub_apply (ct.of_le hnn).contDiffAt (c0.of_le hnn).contDiffAt,
      iteratedFDeriv_comp_add_right]
  rw [eit]
  set z : κ ⊕ κ' → V := Sum.elim x y with hz
  have key := GlobalTheory.SchwartzTranslate.taylor_two (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f (z + s • a))
    (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f1 (z + s • a))
    (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f2 (z + s • a))
    (fun s => by
      have := GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line a n f c0 z s
      rw [e1] at this
      exact this.const_smul (‖y‖ ^ k))
    (fun s => by
      have := GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line a n f1 c1 z s
      rw [e2] at this
      exact this.const_smul (‖y‖ ^ k))
    M
    (fun s _ => by
      set w := z + s • a
      have hyw : ‖y‖ ≤ ‖w‖ := norm_le_norm_elim_add x h y s
      have b1 := norm_iteratedFDeriv_pd_le a f1 n w
      have b2 := norm_iteratedFDeriv_pd_le a f (n + 1) w
      have hah : ‖a‖ ≤ ‖h‖ := norm_padL_le h
      have hS := SchwartzMap.le_seminorm ℂ k (n + 2) f w
      have hb : ‖iteratedFDeriv ℝ n f2 w‖ ≤ ‖h‖ ^ 2 * ‖iteratedFDeriv ℝ (n + 2) f w‖ := by
        calc ‖iteratedFDeriv ℝ n f2 w‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ (n + 1) f1 w‖ := b1
          _ ≤ ‖a‖ * (‖a‖ * ‖iteratedFDeriv ℝ (n + 1 + 1) f w‖) := by gcongr
          _ ≤ ‖h‖ * (‖h‖ * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by gcongr
          _ = _ := by ring
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n f2 w‖
          ≤ ‖w‖ ^ k * (‖h‖ ^ 2 * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by gcongr
        _ = ‖h‖ ^ 2 * (‖w‖ ^ k * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by ring
        _ ≤ M := by rw [hM]; gcongr) 1 (by simp)
  simp only [zero_smul, add_zero, one_smul, one_pow, mul_one] at key
  rw [← smul_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at key
  calc ‖y‖ ^ k * ‖(iteratedFDeriv ℝ n f (z + a) - iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f1 z).compContinuousLinearMap
          (fun _ => inrL (V := V) κ κ')‖
      ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ n f (z + a) - iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f1 z‖ := by
        gcongr
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        refine mul_le_of_le_one_right (norm_nonneg _) ?_
        exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => norm_inrL_le κ κ')
    _ ≤ M := key

end GlobalTheory.SliceTaylor
