import Formalism.LocalToGlobal.Columns.ChainOneB
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OneCosetSharp

namespace Formalism.L2.Col

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `k _ _ ψ₀ χ k₀ m t j n' c n _ hr h hne`. Take `⟨h1, h2, h3, h4, h5, h6, h7, h8⟩` from `hr`. Conclude with `(support_oneCoset k ψ₀ χ k₀ m t j n' c n h1 h2 h3 h4 h5 h6 h7 h8).1 h hne`. Introduce `k _ _ ψ₀ χ k₀ m t j n' c n _ hr`.

Take `⟨h1, h2, h3, h4, h5, h6, h7, h8⟩` from `hr`. Conclude with `(support_oneCoset k ψ₀ χ k₀ m t j n' c n h1 h2 h3 h4 h5 h6 h7 h8).2`.
-/
theorem residueFieldUnfolding_claims_hold : ResidueFieldUnfoldingSupport ∧ ResidueFieldUnfoldingNonzero := by
  refine ⟨?_, ?_⟩
  · intro k _ _ ψ₀ χ k₀ m t j n' c n _ hr h hne
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
    exact (support_oneCoset k ψ₀ χ k₀ m t j n' c n h1 h2 h3 h4 h5 h6 h7 h8).1 h hne
  · intro k _ _ ψ₀ χ k₀ m t j n' c n _ hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
    exact (support_oneCoset k ψ₀ χ k₀ m t j n' c n h1 h2 h3 h4 h5 h6 h7 h8).2

end Formalism.L2.Col
