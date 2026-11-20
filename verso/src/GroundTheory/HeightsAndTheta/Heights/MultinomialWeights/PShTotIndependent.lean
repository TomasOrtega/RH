import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

variable (d : IndexData)

def shTotForm (a b : Fin d.f → ℚ) : MvPolynomial (Idx d) ℚ :=
  ∑ τ : Fin d.f, (C (a τ) * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), X (τ, i) +
    C (b τ) * ∑ i : Fin d.N, X (τ, i))

/- English proof (translation)
The claim follows from `(IsHomogeneous.sum _ _ _ (fun p _ => isHomogeneous_C_mul_X (u p) p)).neg`.
-/
theorem lineClass_isHomogeneous (u : Idx d → ℚ) : (lineClass d u).IsHomogeneous 1 :=
  (IsHomogeneous.sum _ _ _ (fun p _ => isHomogeneous_C_mul_X (u p) p)).neg

/- English proof (translation)
Rewrite using `[mem_homogeneousSubmodule]`. Simplify using `using (lineClass_isHomogeneous d u).pow (d.D + 1)`.
-/
theorem lineClass_pow_mem (u : Idx d → ℚ) : lineClass d u ^ (d.D + 1) ∈ topSpace d := by
  rw [mem_homogeneousSubmodule]
  simpa using (lineClass_isHomogeneous d u).pow (d.D + 1)

/- English proof (translation)
Simplify using `only [shTotForm, map_sum, map_add, map_mul, eval_C, eval_X]`. Rewrite using `[Finset.sum_eq_single τ]`. Simplify using `[Finset.mem_filter]`. Introduce `τ' _ hne`. Simplify using `[hne]`.

Simplify using the standard rewrite rules.
-/
theorem eval_shTotForm_single (a b : Fin d.f → ℚ) (τ : Fin d.f) (i : Fin d.N) :
    eval (fun p => if p = (τ, i) then (1 : ℚ) else 0) (shTotForm d a b) =
      (if i.val < d.j then a τ else 0) + b τ := by
  simp only [shTotForm, map_sum, map_add, map_mul, eval_C, eval_X]
  rw [Finset.sum_eq_single τ]
  · simp [Finset.mem_filter]
  · intro τ' _ hne
    simp [hne]
  · simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shOn_apply (τ : Fin d.f) (F : topSpace d) : shOn d τ F = shiftFl d τ F := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem totOn_apply (τ : Fin d.f) (F : topSpace d) : totOn d τ F = totalFl d τ F := rfl

/- English proof (translation)
Take `⟨c, hc, hdeg⟩` from `hC d`. Establish `hD : ((d.D + 1 : ℕ) : ℚ) ≠ 0` using `by positivity`. Establish `hval : ∀ u : Idx d → ℚ, eval u (degPoly d * shTotForm d a b) = 0`. Introduce `u`. Establish `h1` using `LinearMap.congr_fun hab ⟨_, lineClass_pow_mem d u⟩`.

Simplify using `only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, shOn_apply, totOn_apply, hSh d, hTot d] at h1`. Rewrite using `[eval_mul, hEval, shTotForm]`. Simplify using `only [map_sum, map_add, map_mul, eval_C, eval_X]`. Establish `h2 : -((d.D + 1 : ℕ) : ℚ) * (degAt d u * ∑ τ : Fin d.f, (a τ * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), u (τ, i) + b τ * ∑ i : Fin d.N, u (τ, i))) = 0`. Rewrite using `[← h1, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl (fun τ _ => by ring)`. Conclude with `(mul_eq_zero.mp h2).resolve_left (neg_ne_zero.mpr hD)`. Establish `hzero : degPoly d * shTotForm d a b = 0` using `MvPolynomial.funext (fun u => by rw [hval u, map_zero])`. Rewrite `hzero` using `[hdeg, mul_assoc]`. Establish `hform : shTotForm d a b = 0`.

Break down `mul_eq_zero.mp hzero with h | h` into its components or cases. Conclude with `absurd (C_eq_zero.mp h) hc.ne'`. Conclude with `(mul_eq_zero.mp h).resolve_left (RestTerms.Flag.blockVandermonde_ne_zero _ _)`. Establish `hb : ∀ τ, b τ = 0`. Introduce `τ`.

Establish `h` using `eval_shTotForm_single d a b τ ⟨d.N - 1, by have := d.two_le_N; omega⟩`. Rewrite `h` using `[hform, map_zero, if_neg (by have := d.j_lt_N; simp; omega), zero_add]`. Conclude with `h.symm`. Use `⟨funext fun τ => ?_, funext hb⟩` and prove the remaining obligations. Establish `h` using `eval_shTotForm_single d a b τ ⟨0, by have := d.two_le_N; omega⟩`.

Rewrite `h` using `[hform, map_zero, if_pos (by have := d.one_le_j; simp; omega), hb τ, add_zero]`. Conclude with `h.symm`.
-/
theorem shTot_relation_trivial (hSh : ShOfPower.Statement) (hTot : TotOfPower.Statement)
    (hEval : DegPolyEval.Statement) (hC : CFlPos.Statement) (a b : Fin d.f → ℚ)
    (hab : ∑ τ, a τ • shOn d τ + ∑ τ, b τ • totOn d τ = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨c, hc, hdeg⟩ := hC d
  have hD : ((d.D + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hval : ∀ u : Idx d → ℚ, eval u (degPoly d * shTotForm d a b) = 0 := by
    intro u
    have h1 := LinearMap.congr_fun hab ⟨_, lineClass_pow_mem d u⟩
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply, smul_eq_mul, shOn_apply, totOn_apply, hSh d, hTot d] at h1
    rw [eval_mul, hEval, shTotForm]
    simp only [map_sum, map_add, map_mul, eval_C, eval_X]
    have h2 : -((d.D + 1 : ℕ) : ℚ) * (degAt d u * ∑ τ : Fin d.f,
        (a τ * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), u (τ, i) +
          b τ * ∑ i : Fin d.N, u (τ, i))) = 0 := by
      rw [← h1, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun τ _ => by ring)
    exact (mul_eq_zero.mp h2).resolve_left (neg_ne_zero.mpr hD)
  have hzero : degPoly d * shTotForm d a b = 0 :=
    MvPolynomial.funext (fun u => by rw [hval u, map_zero])
  rw [hdeg, mul_assoc] at hzero
  have hform : shTotForm d a b = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd (C_eq_zero.mp h) hc.ne'
    · exact (mul_eq_zero.mp h).resolve_left (RestTerms.Flag.blockVandermonde_ne_zero _ _)
  have hb : ∀ τ, b τ = 0 := by
    intro τ
    have h := eval_shTotForm_single d a b τ ⟨d.N - 1, by have := d.two_le_N; omega⟩
    rw [hform, map_zero, if_neg (by have := d.j_lt_N; simp; omega), zero_add] at h
    exact h.symm
  refine ⟨funext fun τ => ?_, funext hb⟩
  have h := eval_shTotForm_single d a b τ ⟨0, by have := d.two_le_N; omega⟩
  rw [hform, map_zero, if_pos (by have := d.one_le_j; simp; omega), hb τ, add_zero] at h
  exact h.symm

/- English proof (translation)
Introduce `d hf`. Establish `key` using `shTot_relation_trivial d hSh hTot hEval hC`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`.

Establish `h` using `key (fun τ => g (Sum.inl τ)) (fun τ => g (Sum.inr τ)) (by simpa [Fintype.sum_sum_type] using hg)`. Introduce and unpack `(τ | τ)`. Conclude with `congrFun h.1 τ`. Conclude with `congrFun h.2 τ`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `g hg`. Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Finset.smul_sum] at hg`. Establish `h` using `key (fun _ => g 0) (fun _ => g 1) hg`. Introduce `i`. Use `fin_cases i`.

Conclude with `congrFun h.1 ⟨0, hf⟩`. Conclude with `congrFun h.2 ⟨0, hf⟩`.
-/
theorem ShTotIndependent.proof (hSh : ShOfPower.Statement) (hTot : TotOfPower.Statement)
    (hEval : DegPolyEval.Statement) (hC : CFlPos.Statement) : ShTotIndependent.Statement := by
  intro d hf
  have key := shTot_relation_trivial d hSh hTot hEval hC
  refine ⟨?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have h := key (fun τ => g (Sum.inl τ)) (fun τ => g (Sum.inr τ))
      (by simpa [Fintype.sum_sum_type] using hg)
    rintro (τ | τ)
    · exact congrFun h.1 τ
    · exact congrFun h.2 τ
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Finset.smul_sum] at hg
    have h := key (fun _ => g 0) (fun _ => g 1) hg
    intro i
    fin_cases i
    · exact congrFun h.1 ⟨0, hf⟩
    · exact congrFun h.2 ⟨0, hf⟩

end GroundTheory.Heights₂.Heights.TheoremB
