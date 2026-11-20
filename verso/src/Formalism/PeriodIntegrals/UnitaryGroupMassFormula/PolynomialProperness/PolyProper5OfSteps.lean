import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.PolyProperOfMx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.MXMulVecMid

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate

noncomputable section

namespace PI.PolynomialProperness

def PolyProper5 : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    IsMonomial (Zhat k r z z' γ) → ∃ C : ℝ,
      (∀ σ ∈ Sg k r z z' γ, ∀ s' ∈ Sset k r z',
        B.gN σ + B.gN s' ≤ C * B.gN (σ⁻¹ * γ * s') ^ (5 * (r + 1) ^ 2)) ∧
      (∀ s ∈ Sset k r z, ∀ σ' ∈ Sg' k r z z' γ,
        B.gN s + B.gN σ' ≤ C * B.gN (s⁻¹ * γ * σ') ^ (5 * (r + 1) ^ 2))

/- English proof (translation)
Introduce `k r z z' γ hstd hpos hmono`. Take `⟨CA, hA1, hA2⟩` from `hA k r z z' γ hmono`. Take `⟨Cc, hCc⟩` from `hC k r z z' γ hstd hpos`. Take `⟨Cf, hCf⟩` from `hF k r z`. Take `⟨Cf', hCf'⟩` from `hF k r z'`.

Establish `hγ : γ ∈ B.GV k r` using `hpos.1`. Take `⟨hmul, hinv⟩` from `hG k r`. Use `⟨(1 + B.gN γ⁻¹) * (|Cc| * (1 + (|Cf| + |Cf'|) * CA ^ 2) ^ 2), ?_, ?_⟩` and prove the remaining obligations. Introduce `σ hσ s' hs'`. Take `⟨hσG, v, hv, hvL, hσf⟩` from `hSg k r z z' γ hstd σ hσ`.

Take `⟨hs'G, u', hu, hsf⟩` from `hS k r z' hstd.2.2 s' hs'`. Establish `hg : σ⁻¹ * γ * s' ∈ B.GV k r` using `hmul _ (hmul _ (hinv σ hσG).2.1 _ hγ) _ hs'G`. Establish `hg1` using `(hN k r _ hg).2`. Establish `hZg` using `hZ k r z z' γ σ s' v u' hσG hs'G hσf hsf`. Take `⟨hbv, hbu⟩` from `hA1 v hv hvL u' hu _ hg1 hZg`.

Conclude with `bound_core hG hN hNF hγ hCf hCf' hCc σ s' v u' hσG hs'G hv hu hσf hsf hbv hbu`. Introduce `s hs σ' hσ'`. Take `⟨hsG, u, hu, hsf⟩` from `hS k r z hstd.2.1 s hs`. Take `⟨hσG, v', hv', hPv, hσf⟩` from `hSg' k r z z' γ hstd σ' hσ'`. Establish `hg : s⁻¹ * γ * σ' ∈ B.GV k r` using `hmul _ (hmul _ (hinv s hsG).2.1 _ hγ) _ hσG`.

Establish `hg1` using `(hN k r _ hg).2`. Establish `hZg` using `hZ k r z z' γ s σ' u v' hsG hσG hsf hσf`. Take `⟨hbu, hbv⟩` from `hA2 u hu v' hv' hPv _ hg1 hZg`. Conclude with `bound_core hG hN hNF hγ hCf hCf' hCc s σ' u v' hsG hσG hu hv' hsf hσf hbu hbv`.
-/
theorem polyProper5_of_steps (hG : GVGroup) (hN : NormInv) (hNF : GNFacts) (hF : FmulBound)
    (hZ : ZhatMove) (hS : FrameS) (hSg : FrameSg) (hSg' : FrameSg') (hA : UnitriangularInversePolynomialBound)
    (hC : CoreInst) : PolyProper5 := by
  intro k r z z' γ hstd hpos hmono
  obtain ⟨CA, hA1, hA2⟩ := hA k r z z' γ hmono
  obtain ⟨Cc, hCc⟩ := hC k r z z' γ hstd hpos
  obtain ⟨Cf, hCf⟩ := hF k r z
  obtain ⟨Cf', hCf'⟩ := hF k r z'
  have hγ : γ ∈ B.GV k r := hpos.1
  obtain ⟨hmul, hinv⟩ := hG k r
  refine ⟨(1 + B.gN γ⁻¹) * (|Cc| * (1 + (|Cf| + |Cf'|) * CA ^ 2) ^ 2), ?_, ?_⟩
  · intro σ hσ s' hs'
    obtain ⟨hσG, v, hv, hvL, hσf⟩ := hSg k r z z' γ hstd σ hσ
    obtain ⟨hs'G, u', hu, hsf⟩ := hS k r z' hstd.2.2 s' hs'
    have hg : σ⁻¹ * γ * s' ∈ B.GV k r := hmul _ (hmul _ (hinv σ hσG).2.1 _ hγ) _ hs'G
    have hg1 := (hN k r _ hg).2
    have hZg := hZ k r z z' γ σ s' v u' hσG hs'G hσf hsf
    obtain ⟨hbv, hbu⟩ := hA1 v hv hvL u' hu _ hg1 hZg
    exact bound_core hG hN hNF hγ hCf hCf' hCc σ s' v u' hσG hs'G hv hu hσf hsf hbv hbu
  · intro s hs σ' hσ'
    obtain ⟨hsG, u, hu, hsf⟩ := hS k r z hstd.2.1 s hs
    obtain ⟨hσG, v', hv', hPv, hσf⟩ := hSg' k r z z' γ hstd σ' hσ'
    have hg : s⁻¹ * γ * σ' ∈ B.GV k r := hmul _ (hmul _ (hinv s hsG).2.1 _ hγ) _ hσG
    have hg1 := (hN k r _ hg).2
    have hZg := hZ k r z z' γ s σ' u v' hsG hσG hsf hσf
    obtain ⟨hbu, hbv⟩ := hA2 u hu v' hv' hPv _ hg1 hZg
    exact bound_core hG hN hNF hγ hCf hCf' hCc s σ' u v' hsG hσG hu hv' hsf hσf hbu hbv

/- English proof (translation)
The claim follows from `polyProper5_of_steps gvGroup normInv gnFacts fmulBound zhatMove (frameS_of Formalism.FourierDecayAlt.P.unipotent_map_frame gvGroup) (frameSg_of Formalism.FourierDecayAlt.P.unipotent_map_frame (tauMem_of mxFacts TauN.neFacts) gvGroup) (frameSg'_of Formalism.FourierDecayAlt.P.unipo …`.
-/
theorem polyProper5 : PolyProper5 :=
  polyProper5_of_steps gvGroup normInv gnFacts fmulBound zhatMove
    (frameS_of Formalism.FourierDecayAlt.P.unipotent_map_frame gvGroup)
    (frameSg_of Formalism.FourierDecayAlt.P.unipotent_map_frame (tauMem_of mxFacts TauN.neFacts) gvGroup)
    (frameSg'_of Formalism.FourierDecayAlt.P.unipotent_map_frame (tauMem_of mxFacts TauN.neFacts) gvGroup)
    (unitriangular_inverse_bound second_order_norm_bound)
    (coreInst_of isoCore hpkInvol gnFacts frameInd)

end PI.PolynomialProperness
