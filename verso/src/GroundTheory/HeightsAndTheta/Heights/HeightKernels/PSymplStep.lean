import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

/- English proof (translation)
Introduce `n B G hG hGpd hind`. Take `⟨ρsq, hleast, hpos, hle, P₁, hP₁, hP₁e⟩` from `h1 n G hG hGpd`. Take `⟨hHmem, hHpd, hcomp, -⟩` from `h2 (n + 1) P₁ G hP₁ hG hGpd`. Establish `hHe : symplGram P₁ G (Sum.inl 0) (Sum.inl 0) ≠ 0`. Rewrite using `[hP₁e]`.

Conclude with `hpos.ne'`. Take `⟨Q, hQ, hQB⟩` from `hind (symplReduce (symplGram P₁ G)) (h3 n _ hHmem hHe) (h4 n _ hHpd)`. Take `⟨Q', hQ', hQ'e, hQ'det⟩` from `h5 n (symplGram P₁ G) Q hHe hQ`. Use `⟨ρsq, hleast, hpos, hle, Q' * P₁, Submonoid.mul_mem _ hQ' hP₁, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcomp Q', hQ'e, hP₁e]`.

Rewrite using `[hcomp Q', hQ'det, hP₁e]`. Conclude with `mul_le_mul_of_nonneg_left hQB hpos.le`.
-/
theorem SymplStep.proof (h1 : SymplFirstRow.Statement) (h2 : SymplGramMem.Statement)
    (h3 : SymplReduceMem.Statement) (h4 : SymplReducePosDef.Statement)
    (h5 : SymplReduceStep.Statement) : SymplStep.Statement := by
  intro n B G hG hGpd hind
  obtain ⟨ρsq, hleast, hpos, hle, P₁, hP₁, hP₁e⟩ := h1 n G hG hGpd
  obtain ⟨hHmem, hHpd, hcomp, -⟩ := h2 (n + 1) P₁ G hP₁ hG hGpd
  have hHe : symplGram P₁ G (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
    rw [hP₁e]; exact hpos.ne'
  obtain ⟨Q, hQ, hQB⟩ :=
    hind (symplReduce (symplGram P₁ G)) (h3 n _ hHmem hHe) (h4 n _ hHpd)
  obtain ⟨Q', hQ', hQ'e, hQ'det⟩ := h5 n (symplGram P₁ G) Q hHe hQ
  refine ⟨ρsq, hleast, hpos, hle, Q' * P₁, Submonoid.mul_mem _ hQ' hP₁, ?_, ?_⟩
  · rw [hcomp Q', hQ'e, hP₁e]
  · rw [hcomp Q', hQ'det, hP₁e]
    exact mul_le_mul_of_nonneg_left hQB hpos.le

end GroundTheory.Heights₂.Heights
