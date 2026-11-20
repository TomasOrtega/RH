import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdicCompleteOfEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationTopEqBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationLTorsionFree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeNatDividesLPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationFg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIdealIsPrime
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIdealQuotientChain
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLPowMemSpanOfNotMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIsAdicComplete
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationLAdicClosed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCBase

/- English proof (translation)
Unfold `CrystallineSemistableComparison.Pb.pdP`. Use `Ideal.span_mono ?_` and prove the remaining obligations. Introduce and unpack `z ⟨L, hL, hs, rfl⟩`. Conclude with `⟨L, hL, h.trans hs, rfl⟩`.
-/
theorem dividedPowerFiltration_anti {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {k s : ℕ} (h : k ≤ s) :
    pdP δ s ≤ pdP δ k := by
  unfold CrystallineSemistableComparison.Pb.pdP
  refine Ideal.span_mono ?_
  rintro z ⟨L, hL, hs, rfl⟩
  exact ⟨L, hL, h.trans hs, rfl⟩

/- English proof (translation)
Introduce `l hl K M h k hk s hks`. Establish `H` using `GlobalTheory.CompanionTheory.LatCHyp.hyp_k l k hk`. Use `show CrystallineSemistableComparison.Pb.LatBase (CrystallineSemistableComparison.Pb.Lat.γ (CrystallineSemistableComparison.Pb.Lat.fk l k) (CrystallineSemistableComparison.xi0 l) l M (h.hc k)) l s`. Use `⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `le_bot_iff.mp ((dividedPowerFiltration_anti _ hks).trans (GlobalTheory.CompanionTheory.LatNil.dividedPowerFiltration_eq_bot _ _ l M k H (h.hc k)).le)`.

Conclude with `GlobalTheory.CompanionTheory.Lat.quot_pdP_no_torsion _ _ l M k H (h.hc k)`. Conclude with `GlobalTheory.CompanionTheory.LatticeUnit.natCast_dvd_pow _ _ l M k H`. Conclude with `GlobalTheory.CompanionTheory.LatFG.dividedPowerFiltration_fg _ _ l M k H (h.hc k)`. Conclude with `GlobalTheory.CompanionTheory.LatPrime.I_isPrime _ _ l M k H`. Conclude with `GlobalTheory.CompanionTheory.LatVal.val _ _ l M k H`.

Conclude with `GlobalTheory.CompanionTheory.Lat.pow_mem_span_sup_I _ _ l M k H`. Conclude with `GlobalTheory.CompanionTheory.LatCpl.isAdicComplete_A M H`. Conclude with `GlobalTheory.CompanionTheory.LatClosed.closed _ _ l M k H (h.hc k)`.
-/
theorem latBase_lev : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ), 1 ≤ k → ∀ s, k ≤ s → LatBase (lev h k).γ l s := by
  intro l hl K M h k hk s hks
  have H := GlobalTheory.CompanionTheory.LatCHyp.hyp_k l k hk
  show CrystallineSemistableComparison.Pb.LatBase (CrystallineSemistableComparison.Pb.Lat.γ (CrystallineSemistableComparison.Pb.Lat.fk l k) (CrystallineSemistableComparison.xi0 l) l M (h.hc k)) l s
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_bot_iff.mp ((dividedPowerFiltration_anti _ hks).trans
      (GlobalTheory.CompanionTheory.LatNil.dividedPowerFiltration_eq_bot _ _ l M k H (h.hc k)).le)
  · exact GlobalTheory.CompanionTheory.Lat.quot_pdP_no_torsion _ _ l M k H (h.hc k)
  · exact GlobalTheory.CompanionTheory.LatticeUnit.natCast_dvd_pow _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatFG.dividedPowerFiltration_fg _ _ l M k H (h.hc k)
  · exact GlobalTheory.CompanionTheory.LatPrime.I_isPrime _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatVal.val _ _ l M k H
  · exact GlobalTheory.CompanionTheory.Lat.pow_mem_span_sup_I _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatCpl.isAdicComplete_A M H
  · exact GlobalTheory.CompanionTheory.LatClosed.closed _ _ l M k H (h.hc k)

end GlobalTheory.CompanionTheory.LatCBase
