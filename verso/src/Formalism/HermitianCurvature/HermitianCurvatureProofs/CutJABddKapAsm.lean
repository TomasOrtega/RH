import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddGen

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Take `⟨K, hK, hR⟩` from `hR`. Use `⟨K, hK, ?_⟩` and prove the remaining obligations. Introduce `Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b hb`. Take `⟨κ, rfl⟩` from `hb`. Take `⟨c, ca, hadj, hc, hca, he, hea, hbc, hbca, hbig⟩` from `hR Cc Cb hCc hCb E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ κ`.

Use `⟨SSn.orderZeroDifferentialOperator S v c ca hadj, SSn.order_zero_operator_order, ⟨?_, ?_⟩, ?_, fun J hJ => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `Tm hTm`. Simplify using `only [SSn.orderZeroDifferentialOperator, List.mem_singleton] at hTm`. Substitute `hTm` using the available equality. Conclude with `⟨hc, hca⟩`.

Introduce `p hp f' _ g hg`. Rewrite using `[SSn.order_zero_operator_apply, SSn.order_zero_operator_apply]`. Conclude with `he p hp g hg.1 _`. Introduce `Tm hTm ε hε m`. Simplify using `only [SSn.orderZeroDifferentialOperator, List.mem_singleton] at hTm`.

Substitute `hTm` using the available equality. Take `⟨C1, h1⟩` from `hbc ε hε m`. Take `⟨C2, h2⟩` from `hbca ε hε m`. Use `⟨max C1 C2, fun u w hu hw hl g hg hG => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m)` using `Real.rpow_nonneg (Real.sqrt_nonneg _) _`.

Rewrite using `[zero_add]`. Conclude with `(h1 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)`. Establish `hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m)` using `Real.rpow_nonneg (Real.sqrt_nonneg _) _`. Rewrite using `[zero_add]`. Conclude with `(h2 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)`.

Rewrite using `[SSn.order_zero_operator_apply]`. Conclude with `SSn.equivariant_coefficient_preserves_forms hc he hJ`. Rewrite using `[SSn.order_zero_operator_adjoint]`. Conclude with `SSn.equivariant_coefficient_preserves_forms hca hea hJ`. Rewrite using `[SSn.order_zero_operator_apply]`.

Conclude with `trJ_kap_of_bigCell S T v e κ c hbig J`.
-/
theorem jABddKapQQ_of_kapRealiser (hR : KapRealiser) : JABddKapQQ := by
  obtain ⟨K, hK, hR⟩ := hR
  refine ⟨K, hK, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b hb
  obtain ⟨κ, rfl⟩ := hb
  obtain ⟨c, ca, hadj, hc, hca, he, hea, hbc, hbca, hbig⟩ :=
    hR Cc Cb hCc hCb E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ κ
  refine ⟨SSn.orderZeroDifferentialOperator S v c ca hadj, SSn.order_zero_operator_order, ⟨?_, ?_⟩, ?_, fun J hJ => ⟨?_, ?_, ?_⟩⟩
  · intro Tm hTm
    simp only [SSn.orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    exact ⟨hc, hca⟩
  · intro p hp f' _ g hg
    rw [SSn.order_zero_operator_apply, SSn.order_zero_operator_apply]
    exact he p hp g hg.1 _
  · intro Tm hTm ε hε m
    simp only [SSn.orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    obtain ⟨C1, h1⟩ := hbc ε hε m
    obtain ⟨C2, h2⟩ := hbca ε hε m
    refine ⟨max C1 C2, fun u w hu hw hl g hg hG => ⟨?_, ?_⟩⟩
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h1 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h2 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  · rw [SSn.order_zero_operator_apply]; exact SSn.equivariant_coefficient_preserves_forms hc he hJ
  · rw [SSn.order_zero_operator_adjoint]; exact SSn.equivariant_coefficient_preserves_forms hca hea hJ
  · rw [SSn.order_zero_operator_apply]
    exact trJ_kap_of_bigCell S T v e κ c hbig J

/- English proof (translation)
The claim follows from `jABddKapQQ_of_kapRealiser (kapRealiser_of_typeProj hB hG hP)`.
-/
theorem jABddKapQQ_of_typeProj (hB : DatumBd) (hG : SSn.SSnGeom) (hP : TypeProj) : JABddKapQQ :=
  jABddKapQQ_of_kapRealiser (kapRealiser_of_typeProj hB hG hP)

end

end Formalism.FourierDecayAlt.P.CutMP.JA
