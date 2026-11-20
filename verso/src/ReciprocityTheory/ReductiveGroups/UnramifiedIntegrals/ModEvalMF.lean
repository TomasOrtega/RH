import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Simplify using `[qm, Function.Periodic.qParam]`.
-/
theorem qm_eq_qParam (m : ℕ) (τ : ℍ) : qm m τ = Function.Periodic.qParam (m : ℝ) τ := by
  simp [qm, Function.Periodic.qParam]

/- English proof (translation)
Rewrite using `[qm_eq_qParam]`. Conclude with `Function.Periodic.norm_qParam_lt_one (by exact_mod_cast hm) τ.im_pos`.
-/
theorem qm_norm_lt_one {m : ℕ} (hm : 0 < m) (τ : ℍ) : ‖qm m τ‖ < 1 := by
  rw [qm_eq_qParam]
  exact Function.Periodic.norm_qParam_lt_one (by exact_mod_cast hm) τ.im_pos

/- English proof (translation)
Establish `hlog : Real.log ‖x‖ < 0` using `Real.log_neg h0 h1`. Establish `hmR : (0 : ℝ) < m` using `by exact_mod_cast hm`. Establish `him : 0 < (Function.Periodic.invQParam (m : ℝ) x).im`. Rewrite using `[Function.Periodic.im_invQParam]`. Use `mul_pos_of_neg_of_neg ?_ hlog` and prove the remaining obligations.

Conclude with `div_neg_of_neg_of_pos (by linarith) (by positivity)`. Use `⟨⟨_, him⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[qm_eq_qParam]`. Conclude with `Function.Periodic.qParam_right_inv hmR.ne' (norm_pos_iff.mp h0)`.
-/
theorem qm_surj {m : ℕ} (hm : 0 < m) {x : ℂ} (h0 : 0 < ‖x‖) (h1 : ‖x‖ < 1) : ∃ τ : ℍ, qm m τ = x := by
  have hlog : Real.log ‖x‖ < 0 := Real.log_neg h0 h1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have him : 0 < (Function.Periodic.invQParam (m : ℝ) x).im := by
    rw [Function.Periodic.im_invQParam]
    refine mul_pos_of_neg_of_neg ?_ hlog
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  refine ⟨⟨_, him⟩, ?_⟩
  rw [qm_eq_qParam]
  exact Function.Periodic.qParam_right_inv hmR.ne' (norm_pos_iff.mp h0)

/- English proof (translation)
Establish `hm' : (m : ℂ) ≠ 0` using `by exact_mod_cast hm.ne'`. Rewrite using `[qm, qm, ← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem qm_pow {m : ℕ} (hm : 0 < m) (τ : ℍ) : qm m τ ^ m = qm 1 τ := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [qm, qm, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/- English proof (translation)
Simplify using `using qm_eq_qParam 1 τ`.
-/
theorem qm_one_eq (τ : ℍ) : qm 1 τ = Function.Periodic.qParam 1 τ := by
  simpa using qm_eq_qParam 1 τ

/- English proof (translation)
Establish `ha' : (a : ℂ) ≠ 0` using `by exact_mod_cast ha.ne'`. Establish `he' : (e : ℂ) ≠ 0` using `by exact_mod_cast he.ne'`. Rewrite using `[qm, qm, zetaC, pt_coe ha he, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qm_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    qm 1 (pt a b e τ) = zetaC e ^ b * qm (a * e) τ ^ (a ^ 2) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  rw [qm, qm, zetaC, pt_coe ha he, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/- English proof (translation)
Take `⟨g, hg⟩` from `hf`. Establish `hgf : (⇑g : ℍ → ℂ) = f` using `funext hg`. Establish `h` using `ModularForm.hasSum_qExpansion (f := g) one_pos one_mem_strictPeriods_SL τ`. Rewrite `h` using `[hgf, ← qm_one_eq]`. Conclude with `h`.
-/
theorem IsMF.hasSum {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (τ : ℍ) :
    HasSum (fun n => PowerSeries.coeff n (qExpansion 1 f) * qm 1 τ ^ n) (f τ) := by
  obtain ⟨g, hg⟩ := hf
  have hgf : (⇑g : ℍ → ℂ) = f := funext hg
  have h := ModularForm.hasSum_qExpansion (f := g) one_pos one_mem_strictPeriods_SL τ
  rw [hgf, ← qm_one_eq] at h
  exact h

/- English proof (translation)
Apply `conv_of_hasSum` to reduce the goal to its premises. Introduce `x hx`. Distinguish the cases in `h0 : x = 0`. Substitute `h0` using the available equality. Conclude with `(hasSum_single 0 fun n hn => by simp [zero_pow hn]).summable`.

Take `⟨τ, hτ⟩` from `qm_surj one_pos (norm_pos_iff.mpr h0) hx`. Rewrite using `[← hτ]`. Conclude with `(hf.hasSum τ).summable`.
-/
theorem IsMF.conv {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) : Conv (qExpansion 1 f) := by
  apply conv_of_hasSum
  intro x hx
  by_cases h0 : x = 0
  · subst h0
    exact (hasSum_single 0 fun n hn => by simp [zero_pow hn]).summable
  · obtain ⟨τ, hτ⟩ := qm_surj one_pos (norm_pos_iff.mpr h0) hx
    rw [← hτ]
    exact (hf.hasSum τ).summable

/- English proof (translation)
Conclude with `(hf.hasSum τ).tsum_eq`.
-/
theorem IsMF.ev_eq {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (τ : ℍ) : ev (qExpansion 1 f) (qm 1 τ) = f τ := by
  exact (hf.hasSum τ).tsum_eq

end ReciprocityTheory.ChartRestriction.L1
