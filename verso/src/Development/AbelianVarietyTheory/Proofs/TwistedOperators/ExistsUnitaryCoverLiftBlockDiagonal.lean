import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

/- English proof (translation)
Introduce `U hU V hV`. Establish `hU1` using `Matrix.mem_unitaryGroup_iff.1 hU`. Establish `hU2` using `Matrix.mem_unitaryGroup_iff'.1 hU`. Establish `hV1` using `Matrix.mem_unitaryGroup_iff.1 hV`. Establish `hV2` using `Matrix.mem_unitaryGroup_iff'.1 hV`.

Rewrite `hU1`, `hU2`, `hV1`, `hV2` using `[star_eq_conjTranspose]`. Set `g : GL (Ix p q) ℂ` to `⟨Matrix.fromBlocks U 0 0 V, Matrix.fromBlocks Uᴴ 0 0 Vᴴ, by simp [Matrix.fromBlocks_multiply, hU1, hV1], by simp [Matrix.fromBlocks_multiply, hU2, hV2]⟩`. Establish `hg : g ∈ Formalism.UG.Upq p q` using `by show (Matrix.fromBlocks U 0 0 V : Mat p q)ᴴ * Formalism.UG.Jpq p q * Matrix.fromBlocks U 0 0 V = Formalism.UG.Jpq p q`. Simplify using `[Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU2, hV2]`. Take `⟨w, hw⟩` from `IsAlgClosed.exists_pow_nat_eq ((g : GL (Ix p q) ℂ) : Mat p q).det (show 0 < 2 by norm_num)`.

Establish `hdet : ((g : GL (Ix p q) ℂ) : Mat p q).det ≠ 0` using `Matrix.GeneralLinearGroup.det_ne_zero g`. Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`. Conclude with `hdet (by rw [← hw]; simp)`. Take `⟨k, ⟨hk, -⟩, -⟩` from `T.bij g hg (Units.mk0 w hw0) hw`.

Establish `hm : matG T k = Matrix.fromBlocks U 0 0 V`. Unfold `matG`. Rewrite using `[hk]`. Use `⟨k, ?_, hm⟩` and prove the remaining obligations. Use `show IsKC (matG T k)`.

Rewrite using `[hm]`. Introduce `a b hab`. Apply the tactic sequence `cases a <;> cases b <;> simp_all [sameBlock]`.
-/
theorem exists_lift_blocks (p q : ℕ) (T : GrpData p q) :
    ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      ∃ k ∈ T.Kset, matG T k = Matrix.fromBlocks U 0 0 V := by
  intro U hU V hV
  have hU1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hU2 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hV1 := Matrix.mem_unitaryGroup_iff.1 hV
  have hV2 := Matrix.mem_unitaryGroup_iff'.1 hV
  rw [star_eq_conjTranspose] at hU1 hU2 hV1 hV2
  let g : GL (Ix p q) ℂ :=
    ⟨Matrix.fromBlocks U 0 0 V, Matrix.fromBlocks Uᴴ 0 0 Vᴴ,
      by simp [Matrix.fromBlocks_multiply, hU1, hV1],
      by simp [Matrix.fromBlocks_multiply, hU2, hV2]⟩
  have hg : g ∈ Formalism.UG.Upq p q := by
    show (Matrix.fromBlocks U 0 0 V : Mat p q)ᴴ * Formalism.UG.Jpq p q * Matrix.fromBlocks U 0 0 V
      = Formalism.UG.Jpq p q
    simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU2, hV2]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((g : GL (Ix p q) ℂ) : Mat p q).det
    (show 0 < 2 by norm_num)
  have hdet : ((g : GL (Ix p q) ℂ) : Mat p q).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hw]; simp)
  obtain ⟨k, ⟨hk, -⟩, -⟩ := T.bij g hg (Units.mk0 w hw0) hw
  have hm : matG T k = Matrix.fromBlocks U 0 0 V := by
    unfold matG; rw [hk]
  refine ⟨k, ?_, hm⟩
  show IsKC (matG T k)
  rw [hm]
  intro a b hab
  cases a <;> cases b <;> simp_all [sameBlock]

end GlobalTheory.PolarU
