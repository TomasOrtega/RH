import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMultiplicitySpaceLevelOfKFiniteTensorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepRealThetaRuleOfNodesFarApartStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepWeilDatumNonzeroFockVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardMultiplicityCuspidalRealTypeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

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
Introduce `h1 h2 h3 h4 D hLF hLL hgap c hc k hk s s' hs hs' p hp u φ v _hv`. Establish `hLF'` using `hLF c hc (k + 1) (Nat.succ_le_of_lt hk) s' hs'`. Use `beta_reduce at hLF'`. Take `⟨hwe, hvac⟩` from `GlobalTheory.T.thetaChainStep_weilDatum_nonzero_fockVacuum D hgap c hc k hk s s' hs hs' p hp hk`. Establish `hpar` using `GlobalTheory.T.chainPar_of_nodeGap' D hgap ⟨k, hk⟩`.

Take `⟨T, hTK, hKT, hL⟩` from `GlobalTheory.T.thetaLift_upward_multiplicity_cuspidal_realType h1 h2 h3 h4 D ⟨k, hk⟩ s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ p.ω p.f hs.par hs'.par hc.inf hpar hwe hvac s.ν s.fd hs.haar hs.fund`. Take `⟨F', hF', hint⟩` from `hL _ (multT_le_noLevel c.θ s.M _ _ u.2)`. Establish `hlaw : ∀ P v', ∀ κ ∈ Lev.levG s'.V s'.β s'.L, ∀ g, F' (T P v') (g * κ) = Lev.levChi s'.V s'.β s'.L κ * F' (T P v') g`. Introduce `P v' κ hκ g`. Rewrite using `[← (hint P v' (g * κ)).2, ← (hint P v' g).2, ← integral_const_mul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)` and prove the remaining obligations. Establish `hω : thetaKO p.ω g' (g * κ) (ptOf c.ψ c.θ s.M s'.M p.f P) = (Lev.levChi s'.V s'.β s'.L κ)⁻¹ * thetaKO p.ω g' g (ptOf c.ψ c.θ s.M s'.M p.f P)`. Establish `hm : ((g', g * κ) : GA D s.V × GA D s'.V) = (g', g) * (1, κ)` using `by simp`. Establish `h2` using `(hLL hgap c hc k hk s s' hs hs' p hp P).2 κ hκ`. Simplify using `only [thetaKO]`.

Rewrite using `[hm, map_mul, Module.End.mul_apply]`. Use `erw [h2]`. Rewrite using `[map_smul]`. Both sides reduce to the same expression. Simplify using `only`.

Rewrite using `[hω, map_mul, conj_inv_of_norm_one (hLF'.2.2.2.2.2 κ hκ), mul_assoc]`. Establish `hCC : F' ∈ s'.CC c`. Use `GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s'.V s'.par s'.M c.θ hc.inf _ _ ?_ F' hF' ?_` and prove the remaining obligations. Introduce `κ hκ`. Conclude with `(Subgroup.mem_inf.1 hκ).1`.

Introduce `w hw κ hκ g`. Establish `hx` using `hKT hw`. Use `clear hw`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨P, v', _, rfl⟩` from `hx`. Conclude with `hlaw P v' κ hκ g`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp only [map_add, Pi.add_apply, hx, hy, mul_add]`. Consider the case `smul a x _ hx => simp only [map_smul, Pi.smul_apply, smul_eq_mul, hx]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hup : p.up φ (PiLocalization₂.val u v) = F' (T φ v)`. Use function extensionality and compare the values at `h`. Conclude with `(hint φ v h).2`. Rewrite using `[hup]`.

Conclude with `Submodule.subset_span ⟨⟨F', hCC⟩, T φ v, hTK φ v, rfl⟩`.
-/
theorem upSpan_of : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.ChainOnto.LevFacts D → GlobalTheory.ChainOnto.LevelLaw D → GlobalTheory.ChainOnto.UpSpan D := by
  intro h1 h2 h3 h4 D hLF hLL hgap c hc k hk s s' hs hs' p hp u φ v _hv
  have hLF' := hLF c hc (k + 1) (Nat.succ_le_of_lt hk) s' hs'
  beta_reduce at hLF'
  obtain ⟨hwe, hvac⟩ := GlobalTheory.T.thetaChainStep_weilDatum_nonzero_fockVacuum D hgap c hc k hk s s' hs hs' p hp hk
  have hpar := GlobalTheory.T.chainPar_of_nodeGap' D hgap ⟨k, hk⟩
  obtain ⟨T, hTK, hKT, hL⟩ := GlobalTheory.T.thetaLift_upward_multiplicity_cuspidal_realType h1 h2 h3 h4 D ⟨k, hk⟩ s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ p.ω p.f
    hs.par hs'.par hc.inf hpar hwe hvac s.ν s.fd hs.haar hs.fund
  obtain ⟨F', hF', hint⟩ := hL _ (multT_le_noLevel c.θ s.M _ _ u.2)

  have hlaw : ∀ P v', ∀ κ ∈ Lev.levG s'.V s'.β s'.L, ∀ g,
      F' (T P v') (g * κ) = Lev.levChi s'.V s'.β s'.L κ * F' (T P v') g := by
    intro P v' κ hκ g
    rw [← (hint P v' (g * κ)).2, ← (hint P v' g).2, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
    have hω : thetaKO p.ω g' (g * κ) (ptOf c.ψ c.θ s.M s'.M p.f P) =
        (Lev.levChi s'.V s'.β s'.L κ)⁻¹ * thetaKO p.ω g' g (ptOf c.ψ c.θ s.M s'.M p.f P) := by
      have hm : ((g', g * κ) : GA D s.V × GA D s'.V) = (g', g) * (1, κ) := by simp
      have h2 := (hLL hgap c hc k hk s s' hs hs' p hp P).2 κ hκ
      simp only [thetaKO]
      rw [hm, map_mul, Module.End.mul_apply]
      erw [h2]
      rw [map_smul]
      rfl
    simp only
    rw [hω, map_mul, conj_inv_of_norm_one (hLF'.2.2.2.2.2 κ hκ), mul_assoc]
  have hCC : F' ∈ s'.CC c := by
    refine GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s'.V s'.par s'.M c.θ hc.inf _ _ ?_ F' hF' ?_
    · intro κ hκ
      exact (Subgroup.mem_inf.1 hκ).1
    · intro w hw κ hκ g
      have hx := hKT hw
      clear hw
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

end GlobalTheory.ChainOnto
