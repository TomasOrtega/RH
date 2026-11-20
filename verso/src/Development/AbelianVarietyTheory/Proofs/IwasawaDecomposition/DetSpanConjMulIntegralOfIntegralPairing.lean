import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory

/- English proof (translation)
Establish `hc : ∀ a : 𝓞 E, IsCMField.complexConj E (a : E) ∈ (algebraMap (𝓞 E) E).range` using `fun a => ⟨IsCMField.ringOfIntegersComplexConj E a, IsCMField.coe_ringOfIntegersComplexConj E a⟩`. Introduce `x hx y hy`. Unfold `GlobalTheory.BetaEx.detSpan at hx hy`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨v, hv, rfl⟩` from `(GlobalTheory.BetaEx.mem_detSet M x).1 hx`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨w, hw, rfl⟩` from `(GlobalTheory.BetaEx.mem_detSet M' y).1 hy`. Use `choose A hA using fun i k => h (v i) (hv i) (w k) (hw k)`.

Use `⟨(Matrix.of A).det, ?_⟩` and prove the remaining obligations. Establish `e1 : IsCMField.complexConj E v.det = ((IsCMField.complexConj E : E →+* E).mapMatrix v).det`. Rewrite using `[← RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[RingHom.map_det, e1, ← Matrix.det_transpose w, ← Matrix.det_mul]`.

Use `congr 1`. Use extensionality with `i k`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hA]`. Both sides reduce to the same expression. Consider the case `zero => simpa using Subring.zero_mem _`.

Consider the case `add a b _ _ ha hb => rw [mul_add]`. Conclude with `Subring.add_mem _ ha hb`. Consider the case `smul a b _ hb`. Rewrite using `[Algebra.smul_def, mul_left_comm]`. Conclude with `Subring.mul_mem _ ⟨a, rfl⟩ hb`.

Consider the case `zero => simpa using Subring.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add, add_mul]`. Conclude with `Subring.add_mem _ ha hb`. Consider the case `smul a b _ hb`. Rewrite using `[Algebra.smul_def, map_mul, mul_assoc]`.

Conclude with `Subring.mul_mem _ (hc a) hb`.
-/
theorem detSpan_conj_mul_mem_range (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (M M' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ v ∈ M, ∀ w ∈ M', ∑ j, IsCMField.complexConj E (v j) * w j ∈ (algebraMap (𝓞 E) E).range) :
    ∀ x ∈ GlobalTheory.BetaEx.detSpan M, ∀ y ∈ GlobalTheory.BetaEx.detSpan M',
      IsCMField.complexConj E x * y ∈ (algebraMap (𝓞 E) E).range := by
  have hc : ∀ a : 𝓞 E, IsCMField.complexConj E (a : E) ∈ (algebraMap (𝓞 E) E).range := fun a =>
    ⟨IsCMField.ringOfIntegersComplexConj E a, IsCMField.coe_ringOfIntegersComplexConj E a⟩
  intro x hx y hy
  unfold GlobalTheory.BetaEx.detSpan at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet M x).1 hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet M' y).1 hy
      choose A hA using fun i k => h (v i) (hv i) (w k) (hw k)
      refine ⟨(Matrix.of A).det, ?_⟩
      have e1 : IsCMField.complexConj E v.det
          = ((IsCMField.complexConj E : E →+* E).mapMatrix v).det := by
        rw [← RingHom.map_det]; rfl
      rw [RingHom.map_det, e1, ← Matrix.det_transpose w, ← Matrix.det_mul]
      congr 1
      ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
        Matrix.transpose_apply, hA]
      rfl
    | zero => simpa using Subring.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Subring.add_mem _ ha hb
    | smul a b _ hb =>
      rw [Algebra.smul_def, mul_left_comm]
      exact Subring.mul_mem _ ⟨a, rfl⟩ hb
  | zero => simpa using Subring.zero_mem _
  | add a b _ _ ha hb => rw [map_add, add_mul]; exact Subring.add_mem _ ha hb
  | smul a b _ hb =>
    rw [Algebra.smul_def, map_mul, mul_assoc]
    exact Subring.mul_mem _ (hc a) hb

end GlobalTheory
