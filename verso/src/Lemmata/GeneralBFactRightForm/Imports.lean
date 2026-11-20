import Mathlib

namespace Bl.general_b_fact_right_form

/- English proof (translation)
Introduce `R V _ _ _ _ r e w he α β hα hβ hw he'`. Use `choose B hB using fun a => (Submodule.mem_span_range_iff_exists_fun R).1 (hw a)`. Use `choose A hA using fun l => (Submodule.mem_span_range_iff_exists_fun R).1 (he' l)`. Establish `hAB : Matrix.of A * Matrix.of B = (α * β) • (1 : Matrix (Fin r) (Fin r) R)`. Use extensionality with `l m`.

Establish `h1 : ∑ j, (Matrix.of A * Matrix.of B) l j • e j = (α * β) • e l`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, mul_smul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.smul_sum, hB]`. Simplify using `only [smul_comm _ β, ← Finset.smul_sum, hA]`.

Establish `h2 : ∑ j, ((α * β) • (1 : Matrix (Fin r) (Fin r) R)) l j • e j = (α * β) • e l`. Simplify using `[Matrix.smul_apply, Matrix.one_apply, ite_smul]`. Establish `h3 : ∑ j, ((Matrix.of A * Matrix.of B) l j - ((α * β) • (1 : Matrix (Fin r) (Fin r) R)) l j) • e j = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, h1, h2, sub_self]`. Conclude with `sub_eq_zero.1 (Fintype.linearIndependent_iff.1 he _ h3 m)`.

Establish `hdet : (Matrix.of B).det ≠ 0`. Introduce `h`. Establish `h4` using `congrArg Matrix.det hAB`. Rewrite `h4` using `[Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `pow_ne_zero _ (mul_ne_zero hα hβ) h4.symm`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `hv : Matrix.vecMul c (Matrix.of B) = 0`. Establish `h5 : ∑ j, (Matrix.vecMul c (Matrix.of B)) j • e j = 0`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.sum_smul, mul_smul]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.smul_sum, hB, smul_comm _ β]`. Rewrite using `[hc, smul_zero]`. Use function extensionality and compare the values at `j`. Conclude with `Fintype.linearIndependent_iff.1 he _ h5 j`.

Introduce `i`. Assume the negation of the conclusion as `hi`. Conclude with `hdet (Matrix.exists_vecMul_eq_zero_iff.1 ⟨c, fun h0 => hi (congrFun h0 i), hv⟩)`.
-/
theorem goal1 :
  ∀ {R V : Type} [inst : CommRing.{0} R] [IsDomain.{0} R] [inst_2 : AddCommGroup.{0} V] [inst_3 : Module.{0, 0} R V]
  {r : Nat} (e w : Fin r → V),
  LinearIndependent.{0, 0, 0} R e →
    ∀ {α β : R},
      Ne.{1} α 0 →
        Ne.{1} β 0 →
          (∀ (a : Fin r),
              Membership.mem.{0, 0} (Submodule.span.{0, 0} R (Set.range.{0, 1} e)) (HSMul.hSMul.{0, 0, 0} β (w a))) →
            (∀ (l : Fin r),
                Membership.mem.{0, 0} (Submodule.span.{0, 0} R (Set.range.{0, 1} w)) (HSMul.hSMul.{0, 0, 0} α (e l))) →
              LinearIndependent.{0, 0, 0} R w := by
  intro R V _ _ _ _ r e w he α β hα hβ hw he'
  classical
  choose B hB using fun a => (Submodule.mem_span_range_iff_exists_fun R).1 (hw a)
  choose A hA using fun l => (Submodule.mem_span_range_iff_exists_fun R).1 (he' l)
  have hAB : Matrix.of A * Matrix.of B = (α * β) • (1 : Matrix (Fin r) (Fin r) R) := by
    ext l m
    have h1 : ∑ j, (Matrix.of A * Matrix.of B) l j • e j = (α * β) • e l := by
      simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hB]
      simp only [smul_comm _ β, ← Finset.smul_sum, hA]
    have h2 : ∑ j, ((α * β) • (1 : Matrix (Fin r) (Fin r) R)) l j • e j = (α * β) • e l := by
      simp [Matrix.smul_apply, Matrix.one_apply, ite_smul]
    have h3 : ∑ j, ((Matrix.of A * Matrix.of B) l j - ((α * β) • (1 : Matrix (Fin r) (Fin r) R)) l j) • e j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h1, h2, sub_self]
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 he _ h3 m)
  have hdet : (Matrix.of B).det ≠ 0 := by
    intro h
    have h4 := congrArg Matrix.det hAB
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h4
    exact pow_ne_zero _ (mul_ne_zero hα hβ) h4.symm
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hv : Matrix.vecMul c (Matrix.of B) = 0 := by
    have h5 : ∑ j, (Matrix.vecMul c (Matrix.of B)) j • e j = 0 := by
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hB, smul_comm _ β]
      rw [hc, smul_zero]
    funext j
    exact Fintype.linearIndependent_iff.1 he _ h5 j
  intro i
  by_contra hi
  exact hdet (Matrix.exists_vecMul_eq_zero_iff.1 ⟨c, fun h0 => hi (congrFun h0 i), hv⟩)

end Bl.general_b_fact_right_form
