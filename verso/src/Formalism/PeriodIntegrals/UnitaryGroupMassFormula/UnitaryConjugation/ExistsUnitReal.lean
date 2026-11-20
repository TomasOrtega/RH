import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryConjugation.TransferStep

noncomputable section

namespace PI.UConjT

open ComplexConjugate

/- English proof (translation)
Establish an intermediate fact. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem exists_unit_real {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (w e : E) (hw : w ≠ 0) :
    ∃ c : ℂ, ‖c • w‖ = 1 ∧ (inner ℂ (c • w) e).im = 0 := by
  set z : ℂ := inner ℂ w e with hzdef
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  by_cases hz : z = 0
  · refine ⟨((‖w‖⁻¹ : ℝ) : ℂ), ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      field_simp
    · rw [inner_smul_left, ← hzdef, hz]; simp
  · have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    refine ⟨z * ((‖z‖⁻¹ * ‖w‖⁻¹ : ℝ) : ℂ), ?_, ?_⟩
    · rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      field_simp
    · rw [inner_smul_left, ← hzdef]
      simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, map_mul]
      ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem onbReal : OnbReal := by
  intro m
  induction m with
  | zero =>
    intro E _ _ _ _ T _ e
    exact ⟨fun i => i.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0,
      fun i => i.elim0⟩
  | succ m ih =>
    intro E _ _ _ hm T hT e
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hm
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw0 : w ≠ 0 := hw.2
    obtain ⟨c, hc1, hcre⟩ := exists_unit_real w e hw0
    set v : E := c • w with hv
    have hv0 : v ≠ 0 := by
      intro h
      rw [h, norm_zero] at hc1
      exact zero_ne_one hc1
    have hTv : T v = μ • v := by
      rw [hv, map_smul, hw.apply_eq_smul, smul_comm c μ w]
    have hvv : inner ℂ v v = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hc1]; simp
    have hμ0 : μ ≠ 0 := by
      intro h0
      have h1 := hT v v
      rw [hTv, h0, zero_smul, inner_zero_left, hvv] at h1
      exact zero_ne_one h1
    set K : Submodule ℂ E := (ℂ ∙ v)ᗮ with hK
    have : Fact (Module.finrank ℂ E = m + 1) := ⟨hm⟩
    have hKdim : Module.finrank ℂ K = m := Submodule.finrank_orthogonal_span_singleton hv0
    have hTK : ∀ x ∈ K, T x ∈ K := by
      intro x hx
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
      have h1 := hT v x
      rw [hTv, inner_smul_left, hx] at h1
      exact (mul_eq_zero.mp h1).resolve_left (by simpa using hμ0)
    let T' : K →ₗ[ℂ] K := T.restrict hTK
    have hT' : ∀ x y : K, inner ℂ (T' x) (T' y) = inner ℂ x y := by
      intro x y
      simp only [Submodule.coe_inner, T', LinearMap.coe_restrict_apply]
      exact hT x y
    set a : ℂ := inner ℂ v e with ha
    have he'K : e - a • v ∈ K := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
        hvv, mul_one, ha, sub_self]
    obtain ⟨b', hb'o, hb'e, hb'r⟩ := ih K hKdim T' hT' ⟨e - a • v, he'K⟩
    have hperp : ∀ i, inner ℂ (b' i : E) v = 0 := fun i =>
      (Submodule.mem_orthogonal_singleton_iff_inner_left).mp (b' i).2
    have hperp' : ∀ i, inner ℂ v (b' i : E) = 0 := fun i =>
      (Submodule.mem_orthogonal_singleton_iff_inner_right).mp (b' i).2
    refine ⟨(Fin.cons v (fun i => (b' i : E)) : Fin (m + 1) → E), ?_, ?_, ?_⟩
    · rw [orthonormal_iff_ite] at hb'o ⊢
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp [hc1]
      · simp only [Fin.cons_zero, Fin.cons_succ, hperp']
        simp [(Fin.succ_ne_zero j).symm]
      · simp only [Fin.cons_zero, Fin.cons_succ, hperp]
        simp [Fin.succ_ne_zero i]
      · simp only [Fin.cons_succ, Fin.succ_inj]
        rw [← Submodule.coe_inner]
        exact hb'o i j
    · intro i
      refine Fin.cases ⟨μ, by simpa using hTv⟩ (fun i => ?_) i
      obtain ⟨d, hd⟩ := hb'e i
      refine ⟨d, ?_⟩
      have h2 := congrArg Subtype.val hd
      simpa [T', LinearMap.coe_restrict_apply] using h2
    · intro i
      refine Fin.cases (by simpa using hcre) (fun i => ?_) i
      simp only [Fin.cons_succ]
      have hi := hb'r i
      rw [Submodule.coe_inner] at hi
      have h3 : inner ℂ (b' i : E) e = inner ℂ (b' i : E) (e - a • v) := by
        rw [inner_sub_right, inner_smul_right, hperp i, mul_zero, sub_zero]
      rw [h3]
      exact hi

end PI.UConjT
