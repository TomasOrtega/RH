import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Langlands
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.NearDat
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RhoLe
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.KillComp

open NumberField

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Prove the second alternative.

Extract witnesses or component facts from the available result. Prove the first alternative. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.BW.funKill :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.FunKill E := by
  intro E _ _ _ S n ρ C hC
  obtain ⟨B, hB⟩ := far E n C hC
  obtain ⟨D₀, hfin, hD₀⟩ := nearDat E S n ρ B
  refine ⟨{d ∈ D₀ | 2 ≤ d.len}, hfin.subset (Set.sep_subset _ _), fun d hd => hd.2, ?_⟩
  intro φ w F G hφ hSφ hw hK hSw hF hD hG hsum
  refine (langlands E S n ρ w hw hK hSw).2 ?_
  intro k d hd hlen
  refine killComp E S n C φ w F G hC hφ hSφ hw hF hG hsum k d ?_
  by_cases hfar : ∃ τ i, B < ‖d.lam τ i‖
  · exact Or.inr fun ψ hψ hSψ => hB S d ψ hψ hSψ hfar
  · push_neg at hfar
    obtain ⟨d', hd', hl, hk⟩ := hD₀ d hd hfar
    exact Or.inl (hk F hF (hD d' ⟨hd', hl ▸ hlen⟩))
