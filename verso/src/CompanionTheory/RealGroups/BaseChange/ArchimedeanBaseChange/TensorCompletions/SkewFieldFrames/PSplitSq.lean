import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.TensorCompl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3

/- English proof (translation)
Introduce `E _ _ _ s d hs hcs hd w hw`. Establish `hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom` using `⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _, fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩`. Take `⟨u, hne, hu⟩` from `hw`. Establish `hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E` using `E) (w.under (𝓞 (maximalRealSubfield E))) := ⟨u, w, hne, congrArg HeightOneSpectrum.asIdeal hu, rfl⟩`. Take `⟨τ, -⟩` from `GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hcm hv rfl`.

Use `⟨τ s, ?_⟩` and prove the remaining obligations. Establish `key : τ (algebraMap (maximalRealSubfield E) E d) = τ s * τ s` using `by rw [hd, pow_two, map_mul]`. Conclude with `(τ.commutes d).symm.trans key`.
-/
theorem splitSq_pf (h1 : TensorCompl) : SplitSq := by
  intro E _ _ _ s d hs hcs hd w hw
  have hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  obtain ⟨u, hne, hu⟩ := hw
  have hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) :=
    ⟨u, w, hne, congrArg HeightOneSpectrum.asIdeal hu, rfl⟩
  obtain ⟨τ, -⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hcm hv rfl
  refine ⟨τ s, ?_⟩
  have key : τ (algebraMap (maximalRealSubfield E) E d) = τ s * τ s := by rw [hd, pow_two, map_mul]
  exact (τ.commutes d).symm.trans key

end CompanionTheory.Rg.BcB.G3

end
