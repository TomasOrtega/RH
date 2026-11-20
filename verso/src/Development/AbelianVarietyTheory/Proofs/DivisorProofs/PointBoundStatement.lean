import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeReadBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeSemiFibrationExistsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps

set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt
  GlobalTheory.HeightParts

namespace GlobalTheory.HeightParts

/- English proof (translation)
Assemble the required witnesses or components as `⟨hr.1.trans hC, fun τ k hk => (hr.2 τ k hk).imp fun _ hW => ⟨hW.1, hW.2.1, hW.2.2.trans hC⟩⟩`.
-/
theorem readsAt_mono {D : D7} {O : Setup D} {m : ∀ c, Mets (O.Φ.C c) (cxSt D.what₂.LL)} {y : Pt O.s} {K : Type} [Field K]
    [NumberField K] {g : ℕ} {h : HermFam K (Fin g → K)} {L : Submodule (𝓞 K) (Fin g → K)} {C C' : ℝ}
    (hr : ReadsAt O m y h L C) (hC : C ≤ C') : ReadsAt O m y h L C' :=
  ⟨hr.1.trans hC, fun τ k hk => (hr.2 τ k hk).imp fun _ hW => ⟨hW.1, hW.2.1, hW.2.2.trans hC⟩⟩

/- English proof (translation)
Introduce `p2 pH ts`. Unfold `PtBd OnObj`. Introduce `D O hc hN A T H hr`. Take `⟨C₁, h₁⟩` from `GlobalTheory.T.lie_lattice_read_bound p2 pH D O hc hN A T H hr`. Take `⟨C₀, h₀⟩` from `GlobalTheory.T.lie_lattice_semi_fibration_exists p2 pH ts D O hc hN A T H hr`.

Use `⟨max (max C₀ C₁) 1, le_max_right _ _, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨K, i1, i2, L, h, hL, F, h', r, ε, q, hF, hE⟩` from `h₀ _ ((le_max_left _ _).trans (le_max_left _ _)) y hy`. Conclude with `⟨K, i1, i2, F, h', h, L, r, ε, q, hF, readsAt_mono (h₁ y K L h hL) ((le_max_right _ _).trans (le_max_left _ _)), hE⟩`.
-/
theorem ptBd_holds : Hypotheses2 → HypothesesH → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.TorusSaturated → PtBd := by
  intro p2 pH ts
  unfold PtBd OnObj
  intro D O hc hN A T H hr
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.lie_lattice_read_bound p2 pH D O hc hN A T H hr
  obtain ⟨C₀, h₀⟩ := GlobalTheory.T.lie_lattice_semi_fibration_exists p2 pH ts D O hc hN A T H hr
  refine ⟨max (max C₀ C₁) 1, le_max_right _ _, fun y hy => ?_⟩
  obtain ⟨K, i1, i2, L, h, hL, F, h', r, ε, q, hF, hE⟩ := h₀ _ ((le_max_left _ _).trans (le_max_left _ _)) y hy
  exact ⟨K, i1, i2, F, h', h, L, r, ε, q, hF,
    readsAt_mono (h₁ y K L h hL) ((le_max_right _ _).trans (le_max_left _ _)), hE⟩

end GlobalTheory.HeightParts

end
