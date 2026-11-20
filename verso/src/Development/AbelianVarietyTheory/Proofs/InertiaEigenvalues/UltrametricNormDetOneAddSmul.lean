import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommOfBezout
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.UnitDiscAlg

def unitBallSubring (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] : Subring E where
  carrier := {t | ‖t‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

/- English proof (translation)
Use `set O := unitBallSubring E`. Set `y : Matrix (Fin n) (Fin n) O` to `fun i j => ⟨x i j, hx i j⟩`. Set `w : O` to `⟨ϖ, hϖ.le⟩`. Establish `hmap : O.subtype.mapMatrix (1 + w • y) = 1 + ϖ • x`. Rewrite using `[map_add, map_one]`.

Use `congr 1`. Establish `hdet : (1 + ϖ • x).det = ((1 + w • y).det : E)`. Rewrite using `[← hmap, ← RingHom.map_det]`. Both sides reduce to the same expression. Establish `hq : (Ideal.Quotient.mk (Ideal.span {w})) (1 + w • y).det = 1`.

Rewrite using `[RingHom.map_det, map_add, map_one]`. Establish `: (Ideal.Quotient.mk (Ideal.span {w})).mapMatrix (w • y) = 0`. Use extensionality with `i j`. Simplify using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`. Rewrite using `[this, add_zero, Matrix.det_one]`.

Establish `hmem : (1 + w • y).det - 1 ∈ Ideal.span {w}`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, hq, map_one, sub_self]`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hmem`. Establish `hc' : ((1 + w • y).det : E) - 1 = (c : E) * ϖ`. Use `congrArg Subtype.val hc` as an intermediate fact.

Simplify `this.symm` using `[w]`. Establish `hlt : ‖(1 + ϖ • x).det - 1‖ < 1`. Rewrite using `[hdet, hc', norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `key : (1 + ϖ • x).det = 1 + ((1 + ϖ • x).det - 1)` using `by ring`.

Rewrite using `[key, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne')]`. Simplify using `[hlt.le]`.
-/
theorem norm_det_one_add_smul (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
    (x : Matrix (Fin n) (Fin n) E) (ϖ : E) (hϖ : ‖ϖ‖ < 1) (hx : ∀ i j, ‖x i j‖ ≤ 1) :
    ‖(1 + ϖ • x).det‖ = 1 := by
  set O := unitBallSubring E
  let y : Matrix (Fin n) (Fin n) O := fun i j => ⟨x i j, hx i j⟩
  let w : O := ⟨ϖ, hϖ.le⟩
  have hmap : O.subtype.mapMatrix (1 + w • y) = 1 + ϖ • x := by
    rw [map_add, map_one]
    congr 1
  have hdet : (1 + ϖ • x).det = ((1 + w • y).det : E) := by
    rw [← hmap, ← RingHom.map_det]; rfl
  have hq : (Ideal.Quotient.mk (Ideal.span {w})) (1 + w • y).det = 1 := by
    rw [RingHom.map_det, map_add, map_one]
    have : (Ideal.Quotient.mk (Ideal.span {w})).mapMatrix (w • y) = 0 := by
      ext i j
      simp [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    rw [this, add_zero, Matrix.det_one]
  have hmem : (1 + w • y).det - 1 ∈ Ideal.span {w} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hq, map_one, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hc' : ((1 + w • y).det : E) - 1 = (c : E) * ϖ := by
    have := congrArg Subtype.val hc
    simpa [w] using this.symm
  have hlt : ‖(1 + ϖ • x).det - 1‖ < 1 := by
    rw [hdet, hc', norm_mul]
    calc ‖(c : E)‖ * ‖ϖ‖ ≤ 1 * ‖ϖ‖ := mul_le_mul_of_nonneg_right c.2 (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hϖ
  have key : (1 + ϖ • x).det = 1 + ((1 + ϖ • x).det - 1) := by ring
  rw [key, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne')]
  simp [hlt.le]

end GlobalTheory.UnitDiscAlg
