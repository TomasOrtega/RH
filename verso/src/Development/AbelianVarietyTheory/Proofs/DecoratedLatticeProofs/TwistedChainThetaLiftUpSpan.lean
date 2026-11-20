import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMultiplicitySpaceLevelOfKFiniteTensorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepRealThetaRuleOfNodesFarApartStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardMultiplicityCuspidalRealTypeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepWeilExponentsFockVacuumStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.ChainTw.UpSpanTw

variable {D : D7}

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[mem_multT]`. Use `Submodule.span_mono ?_ hx` and prove the remaining obligations. Introduce `T hT`. Conclude with `⟨hT.aut, hT.cusp, fun v k hk => absurd hk (Set.notMem_empty k), hT.equiv, hT.cont⟩`.
-/
theorem multT_le_noLevel {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) : MultT θ M J χ ≤ MultT θ M ∅ 1 := by
  intro x hx
  rw [mem_multT] at hx ⊢
  refine Submodule.span_mono ?_ hx
  intro T hT
  exact ⟨hT.aut, hT.cusp, fun v k hk => absurd hk (Set.notMem_empty k), hT.equiv, hT.cont⟩

/- English proof (translation)
Establish `h1 : Complex.normSq z = 1` using `by rw [Complex.normSq_eq_norm_sq, hz]; norm_num`. Rewrite using `[Complex.inv_def, h1, inv_one, Complex.ofReal_one, mul_one, Complex.conj_conj]`.
-/
theorem conj_inv_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : conj z⁻¹ = z := by
  have h1 : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [Complex.inv_def, h1, inv_one, Complex.ofReal_one, mul_one, Complex.conj_conj]

/- English proof (translation)
Introduce `h1 h2 h3 h4 D hLL hgap c w hw k hk s s' hs hs' p hp u φ v _hv`. Establish `hc` using `hw.com`. Take `⟨hwe, hvac⟩` from `GlobalTheory.T.twisted_chain_step_weil_exponents_fock_vacuum D hgap c w hw k hk s s' hs hs' p hp hk`. Take `⟨hr, hL0, hfl⟩` from `hs`. Take `⟨hr', hL1, hfl'⟩` from `hs'`.

Establish `hpar` using `GlobalTheory.T.chainPar_of_nodeGap' D hgap ⟨k, hk⟩`. Take `⟨T, hTK, hKT, hL⟩` from `GlobalTheory.T.thetaLift_upward_multiplicity_cuspidal_realType h1 h2 h3 h4 D ⟨k, hk⟩ s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ p.ω p.f hfl.par hfl'.par hc.inf hpar hwe hvac s.ν s.fd hfl.haar hfl.fund`. Take `⟨F', hF', hint⟩` from `hL _ (multT_le_noLevel c.θ s.M _ _ u.2)`. Establish `hlaw : ∀ P v', ∀ κ ∈ Lev.levG s'.V s'.β s'.L, ∀ g, F' (T P v') (g * κ) = Lev.levChi s'.V s'.β s'.L κ * F' (T P v') g`. Introduce `P v' κ hκ g`.

Rewrite using `[← (hint P v' (g * κ)).2, ← (hint P v' g).2, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)` and prove the remaining obligations. Establish `hω : thetaKO p.ω g' (g * κ) (ptOf c.ψ c.θ s.M s'.M p.f P) = (Lev.levChi s'.V s'.β s'.L κ)⁻¹ * thetaKO p.ω g' g (ptOf c.ψ c.θ s.M s'.M p.f P)`. Establish `hm : ((g', g * κ) : GA D s.V × GA D s'.V) = (g', g) * (1, κ)` using `by simp`. Establish `h2` using `(hLL hgap c w hw k hk s s' ⟨hr, hL0, hfl⟩ ⟨hr', hL1, hfl'⟩ p hp P).2 κ hκ`.

Simplify using `only [thetaKO]`. Rewrite using `[hm, map_mul, Module.End.mul_apply]`. Use `erw [h2]`. Rewrite using `[map_smul]`. Both sides reduce to the same expression.

Simplify using `only`. Rewrite using `[hω, map_mul, conj_inv_of_norm_one (GlobalTheory.ChainOnto.LevelFacts.levChi_norm s'.β s'.L κ), mul_assoc]`. Establish `hCC : F' ∈ s'.CC c`. Use `GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s'.V s'.par s'.M c.θ hc.inf _ _ ?_ F' hF' ?_` and prove the remaining obligations. Introduce `κ hκ`.

Conclude with `hκ.1`. Introduce `w' hw' κ hκ g`. Establish `hx` using `hKT hw'`. Use `clear hw'`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨P, v', _, rfl⟩` from `hx`. Conclude with `hlaw P v' κ hκ g`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp only [map_add, Pi.add_apply, hx, hy, mul_add]`.

Consider the case `smul a x _ hx => simp only [map_smul, Pi.smul_apply, smul_eq_mul, hx]`. Expand and normalize the polynomial expressions, which then agree. Establish `hup : p.up φ (PiLocalization₂.val u v) = F' (T φ v)`. Use function extensionality and compare the values at `h`. Conclude with `(hint φ v h).2`.

Rewrite using `[hup]`. Conclude with `Submodule.subset_span ⟨⟨F', hCC⟩, T φ v, hTK φ v, rfl⟩`.
-/
theorem upSpanQ_of : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, LevelLawQ D → UpSpanQ D := by
  intro h1 h2 h3 h4 D hLL hgap c w hw k hk s s' hs hs' p hp u φ v _hv
  have hc := hw.com
  obtain ⟨hwe, hvac⟩ := GlobalTheory.T.twisted_chain_step_weil_exponents_fock_vacuum D hgap c w hw k hk s s' hs hs' p hp hk
  obtain ⟨hr, hL0, hfl⟩ := hs
  obtain ⟨hr', hL1, hfl'⟩ := hs'
  have hpar := GlobalTheory.T.chainPar_of_nodeGap' D hgap ⟨k, hk⟩
  obtain ⟨T, hTK, hKT, hL⟩ := GlobalTheory.T.thetaLift_upward_multiplicity_cuspidal_realType h1 h2 h3 h4 D ⟨k, hk⟩ s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ p.ω p.f
    hfl.par hfl'.par hc.inf hpar hwe hvac s.ν s.fd hfl.haar hfl.fund
  obtain ⟨F', hF', hint⟩ := hL _ (multT_le_noLevel c.θ s.M _ _ u.2)
  have hlaw : ∀ P v', ∀ κ ∈ Lev.levG s'.V s'.β s'.L, ∀ g,
      F' (T P v') (g * κ) = Lev.levChi s'.V s'.β s'.L κ * F' (T P v') g := by
    intro P v' κ hκ g
    rw [← (hint P v' (g * κ)).2, ← (hint P v' g).2, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
    have hω : thetaKO p.ω g' (g * κ) (ptOf c.ψ c.θ s.M s'.M p.f P) =
        (Lev.levChi s'.V s'.β s'.L κ)⁻¹ * thetaKO p.ω g' g (ptOf c.ψ c.θ s.M s'.M p.f P) := by
      have hm : ((g', g * κ) : GA D s.V × GA D s'.V) = (g', g) * (1, κ) := by simp
      have h2 := (hLL hgap c w hw k hk s s' ⟨hr, hL0, hfl⟩ ⟨hr', hL1, hfl'⟩ p hp P).2 κ hκ
      simp only [thetaKO]
      rw [hm, map_mul, Module.End.mul_apply]
      erw [h2]
      rw [map_smul]
      rfl
    simp only
    rw [hω, map_mul, conj_inv_of_norm_one (GlobalTheory.ChainOnto.LevelFacts.levChi_norm s'.β s'.L κ), mul_assoc]
  have hCC : F' ∈ s'.CC c := by
    refine GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s'.V s'.par s'.M c.θ hc.inf _ _ ?_ F' hF' ?_
    · intro κ hκ
      exact hκ.1
    · intro w' hw' κ hκ g
      have hx := hKT hw'
      clear hw'
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨P, v', _, rfl⟩ := hx
        exact hlaw P v' κ hκ g
      | zero => simp
      | add x y _ _ hx hy => simp only [map_add, Pi.add_apply, hx, hy, mul_add]
      | smul a x _ hx => simp only [map_smul, Pi.smul_apply, smul_eq_mul, hx]; ring
  have hup : p.up φ (PiLocalization₂.val u v) = F' (T φ v) := by
    funext h
    exact (hint φ v h).2
  rw [hup]
  exact Submodule.subset_span ⟨⟨F', hCC⟩, T φ v, hTK φ v, rfl⟩

/- English proof (translation)
The claim follows from `upSpanQ_of`.
-/
example : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, LevelLawQ D → UpSpanQ D := upSpanQ_of

end GlobalTheory.ChainTw.UpSpanTw
