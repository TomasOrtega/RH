import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivFsum

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `hσ : ∀ k : Fin (M + 1), Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ = Equiv.swap 0 c.succ (e k).succ` using `fun k => Equiv.Perm.decomposeFin_symm_apply_succ e c.succ k`. Establish `hG : AnalyticAt ℂ (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ => fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) 0` using `analyticAt_fderiv_apply _ 0 _ (analyticAt_determinant_power_zero_int _ t)`. Establish `e1` using `icompL (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ => fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) phiF phiF_add phiF_smul 0 0 phiF_zero hG (M + 1) (fun k => Matrix.single k (Equiv.swap 0 c.succ (e k).succ) 1) (fun k => Matrix.single k.succ (Equiv.Perm.decom …`. Rewrite using `[← e1]`. Establish `hev : (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ => fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) ∘ phiF =ᶠ[𝓝 0] fsum t c` using `by filter_upwards [ev_piF (M + 1)] with X hX`.

Conclude with `fderiv_determinant_power_column_sum t X hX c`. Rewrite using `[(hev.iteratedFDeriv ℂ (M + 1)).eq_of_nhds]`. Establish `h0 : (1 + piF (0 : Matrix (Fin (M + 1)) (Fin (M + 1 + 1)) ℂ)).det ≠ 0`. Simplify using `[piF_zero]`. Rewrite using `[ipeel (fsum t c) 0 (analyticAt_fsum t c 0 h0) M _ (e.symm c)]`.

Use `beta_reduce`. Establish `hu0 : Equiv.swap 0 c.succ (e (e.symm c)).succ = 0` using `by simp`. Rewrite using `[hu0]`. Establish `hev2 : (fun y => fderiv ℂ (fsum t c) y (Matrix.single (e.symm c) 0 1)) =ᶠ[𝓝 0] (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ => (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) ∘ piF` using `by filter_upwards [ev_piF (M + 1)] with y hy`. Simplify using `[fderiv_fsum t c (e.symm c) y hy]`.

Use `erw [(hev2.iteratedFDeriv ℂ M).eq_of_nhds]`. Establish `hK : AnalyticAt ℂ (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ => fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) 0` using `analyticAt_fderiv_apply _ 0 _ (analyticAt_determinant_power_zero_int _ t)`. Establish `hK' : AnalyticAt ℂ (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ => (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) 0` using `analyticAt_const.mul hK`. Establish `hne : ∀ k : Fin M, Equiv.swap 0 c.succ (e ((e.symm c).succAbove k)).succ = (e ((e.symm c).succAbove k)).succ`. Introduce `k`.

Establish `h1 : e ((e.symm c).succAbove k) ≠ c`. Introduce `h`. Establish `h2` using `congrArg e.symm h`. Rewrite `h2` using `[Equiv.symm_apply_apply]`. Conclude with `Fin.succAbove_ne _ _ h2`.

Conclude with `Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => h1 (Fin.succ_injective _ h))`. Use `erw [icompL (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ => (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) piF piF_add piF_smul 0 0 piF_zero hK' M (fun k => Matrix.single ((e.symm c).succAbove k) (Equiv.swap 0 c.succ (e ((e.symm c).succAbove k)).succ) 1) (fu …`. Rewrite using `[iconst_mul _ 0 (-1) hK]`. Rewrite using `[ipeel (H (M + 1) t) 0 (analyticAt_determinant_power_zero_int _ t) M (fun k => Matrix.single k (e k) 1) (e.symm c)]`. Use `clear e1 hev hev2 hK' hne hσ hG h0 hu0 hK`.

Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem iterated_derivative_column_case_int (t : ℤ) (M : ℕ) (e : Equiv.Perm (Fin (M + 1))) (c : Fin (M + 1)) :
    iteratedFDeriv ℂ (M + 1) (fun y => fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) 0
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ) 1) =
      -iteratedFDeriv ℂ (M + 1) (H (M + 1) t) 0 (fun k => Matrix.single k (e k) 1) := by
  have hσ : ∀ k : Fin (M + 1), Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ =
      Equiv.swap 0 c.succ (e k).succ :=
    fun k => Equiv.Perm.decomposeFin_symm_apply_succ e c.succ k
  have hG : AnalyticAt ℂ (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ =>
      fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) 0 :=
    analyticAt_fderiv_apply _ 0 _ (analyticAt_determinant_power_zero_int _ t)
  have e1 := icompL (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ =>
      fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) phiF phiF_add phiF_smul 0 0
    phiF_zero hG (M + 1)
    (fun k => Matrix.single k (Equiv.swap 0 c.succ (e k).succ) 1)
    (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ) 1)
    (fun i => by rw [phiF_single, hσ])
  rw [← e1]
  have hev : (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ =>
      fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) ∘ phiF =ᶠ[𝓝 0] fsum t c := by
    filter_upwards [ev_piF (M + 1)] with X hX
    exact fderiv_determinant_power_column_sum t X hX c
  rw [(hev.iteratedFDeriv ℂ (M + 1)).eq_of_nhds]
  have h0 : (1 + piF (0 : Matrix (Fin (M + 1)) (Fin (M + 1 + 1)) ℂ)).det ≠ 0 := by
    simp [piF_zero]
  rw [ipeel (fsum t c) 0 (analyticAt_fsum t c 0 h0) M _ (e.symm c)]
  beta_reduce
  have hu0 : Equiv.swap 0 c.succ (e (e.symm c)).succ = 0 := by simp
  rw [hu0]
  have hev2 : (fun y => fderiv ℂ (fsum t c) y (Matrix.single (e.symm c) 0 1)) =ᶠ[𝓝 0]
      (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
        (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) ∘ piF := by
    filter_upwards [ev_piF (M + 1)] with y hy
    simp [fderiv_fsum t c (e.symm c) y hy]
  erw [(hev2.iteratedFDeriv ℂ M).eq_of_nhds]
  have hK : AnalyticAt ℂ (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
      fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) 0 :=
    analyticAt_fderiv_apply _ 0 _ (analyticAt_determinant_power_zero_int _ t)
  have hK' : AnalyticAt ℂ (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
      (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) 0 :=
    analyticAt_const.mul hK
  have hne : ∀ k : Fin M, Equiv.swap 0 c.succ (e ((e.symm c).succAbove k)).succ =
      (e ((e.symm c).succAbove k)).succ := by
    intro k
    have h1 : e ((e.symm c).succAbove k) ≠ c := by
      intro h
      have h2 := congrArg e.symm h
      rw [Equiv.symm_apply_apply] at h2
      exact Fin.succAbove_ne _ _ h2
    exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => h1 (Fin.succ_injective _ h))
  erw [icompL (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
      (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1))
    piF piF_add piF_smul 0 0 piF_zero hK' M
    (fun k => Matrix.single ((e.symm c).succAbove k)
      (Equiv.swap 0 c.succ (e ((e.symm c).succAbove k)).succ) 1)
    (fun k => Matrix.single ((e.symm c).succAbove k) (e ((e.symm c).succAbove k)) 1)
    (fun k => by rw [hne, piF_single_succ])]
  rw [iconst_mul _ 0 (-1) hK]
  rw [ipeel (H (M + 1) t) 0 (analyticAt_determinant_power_zero_int _ t) M (fun k => Matrix.single k (e k) 1) (e.symm c)]
  clear e1 hev hev2 hK' hne hσ hG h0 hu0 hK
  simp
  rfl

end PositivityTheory.Rg.Sw.LVs.CK
