import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc

namespace GlobalTheory.KFinLoc

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB v`. Establish `hUn` using `hB.unram`. Establish `hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E` using `E) v := by`. Use `GlobalTheory.LFun.isUnram_iff.2 fun w _ => ?_` and prove the remaining obligations. Conclude with `Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)`.

Break down `GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hs | hi` into its components or cases. Use `left`. Take `⟨w, w', hne, h1, h2⟩` from `GlobalTheory.LFun.isSplit_iff.1 hs`. Conclude with `⟨(GlobalTheory.AdelicU.existsUnique_splitPrime_eq hB.cm hne h1 h2).exists.choose⟩`. Conclude with `Or.inr hi`.
-/
theorem split_or_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w := by
  intro F E _ _ _ _ _ σ B hB v
  have hUn := hB.unram
  have hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
    refine GlobalTheory.LFun.isUnram_iff.2 fun w _ => ?_
    exact Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hs | hi
  · left
    obtain ⟨w, w', hne, h1, h2⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    exact ⟨(GlobalTheory.AdelicU.existsUnique_splitPrime_eq hB.cm hne h1 h2).exists.choose⟩
  · exact Or.inr hi

end GlobalTheory.KFinLoc
