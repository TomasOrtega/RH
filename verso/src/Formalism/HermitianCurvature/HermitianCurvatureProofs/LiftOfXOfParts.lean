import Formalism.HermitianCurvature.StatementTL

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

noncomputable section

/- English proof (translation)
Introduce `hZ _hC hX Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 hD Y`. Take `⟨_, _, hAct, hQQ, _, _, _, hLS⟩` from `hD`. Take `⟨B0, _, hB⟩` from `hX Wp Wq P Bs X`. Take `⟨hFB, hEq, hRad⟩` from `hB Y`. Use `set E := xFib Bs B0 (Y + ((P.k : ℂ) - 2) / 2) with hE`.

Use `set s : ℂ := M.sgn P l0 with hs`. Establish `hx : st.x Y = L.GGi * st.QQ Y 1 1`. Rewrite using `[hLS.tau, ← mul_assoc, L.GGi_GG, one_mul]`. Establish `hx1 : (st.x Y).1 = X.fn 5 * (s • X.t Y 1 1)`. Rewrite using `[hx, hQQ Y, hAct.2.2.2.2.2.2.2.2.2.2.2.1]`.

Both sides reduce to the same expression. Use `hZ Wp Wq P Bs 0 0 0 0 (fun _ => s) E (st.x Y) ?_ hFB ?_ ?_` and prove the remaining obligations. Use `⟨MvPolynomial.C s, by simp, fun g => by simp⟩` and prove the remaining obligations. Introduce `p hp g hg J`. Simplify using `only [pow_zero, mul_one, smul_apply]`.

Rewrite using `[hEq p hp g hg J, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]`. Introduce `Φ x hx'`. Simplify using `only [pow_zero, mul_one, smul_apply]`. Rewrite using `[hx1, Module.End.mul_apply, X.fn_apply 5 _ x hx', LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hRad Φ x hx', smul_smul, smul_smul]`. Establish `hG : (0 : ℝ) < Q.GGl P.k P.r Bs.z Bs.z' x.2` using `hx'.2.2`.

Simplify using `only [Q.fnVal]`. Use `congr 1`. Establish `hG' : ((Q.GGl P.k P.r Bs.z Bs.z' x.2 : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hG.ne'`. Clear the denominators using the available nonvanishing facts.
-/
theorem lift_of_x_of_parts : TL.LiftXOfParts := by
  intro hZ _hC hX Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 hD Y
  obtain ⟨_, _, hAct, hQQ, _, _, _, hLS⟩ := hD
  obtain ⟨B0, _, hB⟩ := hX Wp Wq P Bs X
  obtain ⟨hFB, hEq, hRad⟩ := hB Y
  set E := xFib Bs B0 (Y + ((P.k : ℂ) - 2) / 2) with hE
  set s : ℂ := M.sgn P l0 with hs
  have hx : st.x Y = L.GGi * st.QQ Y 1 1 := by
    rw [hLS.tau, ← mul_assoc, L.GGi_GG, one_mul]
  have hx1 : (st.x Y).1 = X.fn 5 * (s • X.t Y 1 1) := by
    rw [hx, hQQ Y, hAct.2.2.2.2.2.2.2.2.2.2.2.1]
    rfl
  refine hZ Wp Wq P Bs 0 0 0 0 (fun _ => s) E (st.x Y) ?_ hFB ?_ ?_
  · refine ⟨MvPolynomial.C s, by simp, fun g => by simp⟩
  · intro p hp g hg J
    simp only [pow_zero, mul_one, smul_apply]
    rw [hEq p hp g hg J, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro Φ x hx'
    simp only [pow_zero, mul_one, smul_apply]
    rw [hx1, Module.End.mul_apply, X.fn_apply 5 _ x hx', LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
      Pi.smul_apply, hRad Φ x hx', smul_smul, smul_smul]
    have hG : (0 : ℝ) < Q.GGl P.k P.r Bs.z Bs.z' x.2 := hx'.2.2
    simp only [Q.fnVal]
    congr 1
    have hG' : ((Q.GGl P.k P.r Bs.z Bs.z' x.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
    field_simp

end

end Formalism.FourierDecayAlt.P
