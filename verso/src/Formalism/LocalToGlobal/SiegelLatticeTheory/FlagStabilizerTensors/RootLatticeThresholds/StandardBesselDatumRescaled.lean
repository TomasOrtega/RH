import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpNZTie
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairMeasScaleN
import Formalism.HermitianCurvature.StatementD

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames Formalism.L2.S.Pv.AmpNZTie

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ}

abbrev standardBesselDatumRescaled (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) (κ₀ : ENNReal) : LocBessel k r :=
  { stdL L ka hka with κN := κ₀ }

def gStd (ka : ℝ) (g : Mx k r) : Mx k r := cj k r ka⁻¹ 1 (tTi k r * g * tT k r)

def muStd (ka : ℝ) (μR : Measure (Mt k r)) : Measure (Mt k r) := (μR.map (cA k r)).map (cjT k r ka⁻¹ 1)

/- English proof (translation)
Use `show (a * b) • _ = a • (b • _)`. Rewrite using `[smul_smul]`.
-/
theorem haarLie_smul (S : Set (Mx k r)) (a b : ENNReal) : haarLie S (a * b) = a • haarLie S b := by
  show (a * b) • _ = a • (b • _)
  rw [smul_smul]

/- English proof (translation)
Take `⟨k0, rfl⟩ : ∃ k0, k = k0 + 1` from `⟨k - 1, by omega⟩`. Establish `hκ : (0 : ℝ) < ka⁻¹` using `inv_pos.2 hka`. Establish `hτ : (0 : ℝ) < 1` using `one_pos`. Use `set κs : ENNReal := L.κN * ENNReal.ofReal (deltaN (k0 + 1) r ka⁻¹ 1) with hκs`. Establish `hd : ENNReal.ofReal (deltaN (k0 + 1) r ka⁻¹ 1) ≠ 0` using `(ENNReal.ofReal_pos.mpr (deltaN_pos hκ hτ)).ne'`.

Establish `hs0 : κs ≠ 0` using `mul_ne_zero hN0 hd`. Establish `hs1 : κs ≠ ⊤` using `ENNReal.mul_ne_top hN1 ENNReal.ofReal_ne_top`. Use `set t : ENNReal := κ₀ / κs with ht`. Use `set g1 := tTi (k0 + 1) r * g * tT (k0 + 1) r with hg1`. Establish `hq1 : IsOrbQuot (turnL L ka) g1 (μR.map (cA (k0 + 1) r)) (ν.map (thP (k0 + 1) r))` using `isOrbQuot_turn L ka hq`.

Establish `hrel1 : IsRelStab (turnL L ka) g1` using `isRelStab_turn L ka hc hrel`. Establish `hqs : IsOrbQuot (stdL L ka hka) (gStd ka g) (muStd ka μR) ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1))` using `isOrbQuot_trD hκ hτ (turnL L ka) _ _ _ _ _ _ hq1`. Establish `hrels : IsRelStab (stdL L ka hka) (gStd ka g)` using `isRelStab_trD hκ hτ (turnL L ka) _ _ _ _ _ _ _ hrel1`. Establish `hNs : (standardBesselDatumRescaled L ka hka κ₀).μN = t • (stdL L ka hka).μN` using `by show haarLie (Nset (k0 + 1) r) κ₀ = t • haarLie (Nset (k0 + 1) r) κs`. Rewrite using `[← haarLie_smul, ht, ENNReal.div_mul_cancel hs0 hs1]`.

Establish `hP2 : pairMeas (standardBesselDatumRescaled L ka hka κ₀) = (t * t) • pairMeas (stdL L ka hka)` using `pairMeas_scaleN (L := stdL L ka hka) (L' := standardBesselDatumRescaled L ka hka κ₀) rfl rfl t hNs`. Establish `hq2 : IsOrbQuot (standardBesselDatumRescaled L ka hka κ₀) (gStd ka g) (muStd ka μR) ((t * t) • ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1)))` using `isOrbQuot_smul hqs _ hP2`. Establish `hrel2 : IsRelStab (standardBesselDatumRescaled L ka hka κ₀) (gStd ka g)` using `hrels`. Establish `hc2 : (standardBesselDatumRescaled L ka hka κ₀).c = cStd` using `stdL_c L ka hka`. Establish `hg2 : gStd ka g ∈ UH (Hpk (k0 + 1) r)` using `(cj_mem_UH_iff hκ hτ _).mpr (conjI_mem_UH hg)`.

Establish `hmem : ∀ x : Mt (k0 + 1) r, (Matrix.of (cjT (k0 + 1) r ka⁻¹ 1 (cA (k0 + 1) r x)) ∈ RStab (k0 + 1) r (gStd ka g)) ↔ Matrix.of x ∈ RStab (k0 + 1) r g`. Introduce `x`. Rewrite using `[of_cjT, of_cA]`. Conclude with `(cj_mem_RStab_iff hκ hτ _ _).trans (conjI_mem_RStab_iff g _)`. Establish `hconc2 : muStd ka μR {x | Matrix.of x ∉ RStab (k0 + 1) r (gStd ka g)} = 0`.

Unfold `muStd`. Rewrite using `[← cjE_coe hκ hτ, MeasurableEquiv.map_apply, ← cAE_coe, MeasurableEquiv.map_apply]`. Use `hconc using 2` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, cAE_coe, cjE_coe]`.

Conclude with `not_congr (hmem x)`. Establish `hne2 : muStd ka μR ≠ 0`. Unfold `muStd`. Rewrite using `[← cjE_coe hκ hτ, ← cAE_coe]`. Conclude with `(Measure.map_ne_zero_iff (cjE hκ hτ).measurable.aemeasurable).mpr ((Measure.map_ne_zero_iff (cAE (k0 + 1) r).measurable.aemeasurable).mpr hne)`.

Establish `: SFinite (muStd ka μR)` using `by unfold muStd; infer_instance`. Take `⟨θ, hθ, hint⟩` from `hcut`. Establish `hμ : B.μSS = pairMeas (standardBesselDatumRescaled L ka hka κ₀)` using `by show (B.μW.prod B.μN).prod (B.μW'.prod B.μN) = _`. Rewrite using `[hBW, hBN, hBW']`. Both sides reduce to the same expression.

Establish `hI : ∀ θ' : Formalism.FourierDecayAlt.B.SS (k0 + 1) r → ℝ, (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p) = fun p => θ' p • besselIntg (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g) p`. Introduce `θ'`. Use function extensionality and compare the values at `p`. Conclude with `congrArg (fun X => θ' p • X) (Formalism.MainNotions.BigCellDensity.integrand_eq (standardBesselDatumRescaled L ka hka κ₀) B hc2 hBz hBz' hBπ hBπ' (stdF L ka F) (gStd ka g) p)`. Establish `hW` using `Formalism.MainNotions.BigCellDensity.weil_L_gen (standardBesselDatumRescaled L ka hka κ₀) hc2 h0 h1 hg2 hrel2 hconc2 hne2 hq2 (stdF L ka F)`.

Establish `hfin : OrbInt (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g) ((t * t) • ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1))) = ((t * t).toReal : ℂ) • OrbInt L F g ν` using `by show OrbInt (stdL L ka hka) (stdF L ka F) (gStd ka g) ((t * t) • ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1))) = _`. Rewrite using `[gStd, OrbInt_trD hκ hτ (turnL L ka) _ _ _ _ _ _ _ (stdF L ka F) g1 (t * t) (ν.map (thP (k0 + 1) r))]`. Establish `hfe : (fun x => stdF L ka F (cj (k0 + 1) r ka⁻¹ 1 x)) = turnF L ka F`. Use function extensionality and compare the values at `x`. Use `show turnF L ka F (cjI (k0 + 1) r ka⁻¹ 1 (cj (k0 + 1) r ka⁻¹ 1 x)) = _`.

Rewrite using `[cjI_cj hκ hτ]`. Rewrite using `[hfe, OrbInt_turn L ka hc F g ν]`. Unfold `Formalism.FourierDecayAlt.D.orbJ`. Rewrite using `[dif_pos ⟨θ, hθ, hint⟩]`. Establish `hspec` using `(⟨θ, hθ, hint⟩ : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut B (gStd ka g) (muStd ka μR) θ ∧ Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p) B.μSS).choose_spec`.

Generalize the expression as in `(⟨θ, hθ, hint⟩ : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut B (gStd ka g) (muStd ka μR) θ ∧ Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p) B.μSS).choose = θ' at hspec ⊢`. Establish `hint' : Integrable (fun p => θ' p • besselIntg (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g) p) (pairMeas (standardBesselDatumRescaled L ka hka κ₀))`. Establish `h2` using `hspec.2`. Rewrite `h2` using `[hI θ', hμ]`. Conclude with `h2`.

Establish `hθ1 : ∀ p, Formalism.MainNotions.BigCellDensity.InPair (standardBesselDatumRescaled L ka hka κ₀) p → ∫ x, θ' (stabAct (gStd ka g) (Matrix.of x) p) ∂(muStd ka μR) = 1`. Introduce `p hp`. Use `hspec.1.2.2 p ?_` and prove the remaining obligations. Unfold `Formalism.FourierDecayAlt.B.RealPlaceData.inSS`. Rewrite using `[hBz, hBz']`.

Conclude with `hp`. Establish `e1 : (∫ p, θ' p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p ∂B.μSS) = ∫ p, θ' p • besselIntg (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g) p ∂(pairMeas (standardBesselDatumRescaled L ka hka κ₀))`. Rewrite using `[hμ]`. Conclude with `congrArg (fun f => ∫ p, f p ∂(pairMeas (standardBesselDatumRescaled L ka hka κ₀))) (hI θ')`. Conclude with `e1.trans ((hW θ' hθ1 hint').trans hfin)`.
-/
theorem orbJ_std (hk : 1 ≤ k) (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) (hc : L.c = ((2 * ka : ℝ) : ℂ))
    (hN0 : L.κN ≠ 0) (hN1 : L.κN ≠ ⊤) (κ₀ : ENNReal) (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤)
    (B : Formalism.FourierDecayAlt.B.RealPlaceData k r L.Wp L.Wq) (hBz : B.z = (stdL L ka hka).z) (hBz' : B.z' = (stdL L ka hka).z')
    (hBπ : B.π = (stdL L ka hka).π) (hBπ' : B.π' = (stdL L ka hka).π') (hBW : B.μW = (stdL L ka hka).μW)
    (hBW' : B.μW' = (stdL L ka hka).μW') (hBN : B.μN = haarLie (Nset k r) κ₀)
    (g : Mx k r) (hg : g ∈ UH (Hpk k r)) (hrel : IsRelStab L g) (μR : Measure (Mt k r)) [SFinite μR]
    (hconc : μR {x | Matrix.of x ∉ RStab k r g} = 0) (hne : μR ≠ 0) (ν : Measure (PairSp k r))
    (hq : IsOrbQuot L g μR ν) (F : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (hcut : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut B (gStd ka g) (muStd ka μR) θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p) B.μSS) :
    Formalism.FourierDecayAlt.D.orbJ B (gStd ka g) (muStd ka μR) (stdF L ka F) =
      (((κ₀ / (L.κN * ENNReal.ofReal (deltaN k r ka⁻¹ 1))) * (κ₀ / (L.κN * ENNReal.ofReal (deltaN k r ka⁻¹ 1)))).toReal
        : ℂ) • OrbInt L F g ν := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  have hκ : (0 : ℝ) < ka⁻¹ := inv_pos.2 hka
  have hτ : (0 : ℝ) < 1 := one_pos
  set κs : ENNReal := L.κN * ENNReal.ofReal (deltaN (k0 + 1) r ka⁻¹ 1) with hκs
  have hd : ENNReal.ofReal (deltaN (k0 + 1) r ka⁻¹ 1) ≠ 0 := (ENNReal.ofReal_pos.mpr (deltaN_pos hκ hτ)).ne'
  have hs0 : κs ≠ 0 := mul_ne_zero hN0 hd
  have hs1 : κs ≠ ⊤ := ENNReal.mul_ne_top hN1 ENNReal.ofReal_ne_top
  set t : ENNReal := κ₀ / κs with ht
  set g1 := tTi (k0 + 1) r * g * tT (k0 + 1) r with hg1

  have hq1 : IsOrbQuot (turnL L ka) g1 (μR.map (cA (k0 + 1) r)) (ν.map (thP (k0 + 1) r)) := isOrbQuot_turn L ka hq
  have hrel1 : IsRelStab (turnL L ka) g1 := isRelStab_turn L ka hc hrel

  have hqs : IsOrbQuot (stdL L ka hka) (gStd ka g) (muStd ka μR) ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1)) :=
    isOrbQuot_trD hκ hτ (turnL L ka) _ _ _ _ _ _ hq1
  have hrels : IsRelStab (stdL L ka hka) (gStd ka g) := isRelStab_trD hκ hτ (turnL L ka) _ _ _ _ _ _ _ hrel1

  have hNs : (standardBesselDatumRescaled L ka hka κ₀).μN = t • (stdL L ka hka).μN := by
    show haarLie (Nset (k0 + 1) r) κ₀ = t • haarLie (Nset (k0 + 1) r) κs
    rw [← haarLie_smul, ht, ENNReal.div_mul_cancel hs0 hs1]
  have hP2 : pairMeas (standardBesselDatumRescaled L ka hka κ₀) = (t * t) • pairMeas (stdL L ka hka) :=
    pairMeas_scaleN (L := stdL L ka hka) (L' := standardBesselDatumRescaled L ka hka κ₀) rfl rfl t hNs
  have hq2 : IsOrbQuot (standardBesselDatumRescaled L ka hka κ₀) (gStd ka g) (muStd ka μR)
      ((t * t) • ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1))) := isOrbQuot_smul hqs _ hP2
  have hrel2 : IsRelStab (standardBesselDatumRescaled L ka hka κ₀) (gStd ka g) := hrels
  have hc2 : (standardBesselDatumRescaled L ka hka κ₀).c = cStd := stdL_c L ka hka

  have hg2 : gStd ka g ∈ UH (Hpk (k0 + 1) r) := (cj_mem_UH_iff hκ hτ _).mpr (conjI_mem_UH hg)
  have hmem : ∀ x : Mt (k0 + 1) r, (Matrix.of (cjT (k0 + 1) r ka⁻¹ 1 (cA (k0 + 1) r x)) ∈ RStab (k0 + 1) r (gStd ka g)) ↔
      Matrix.of x ∈ RStab (k0 + 1) r g := by
    intro x
    rw [of_cjT, of_cA]
    exact (cj_mem_RStab_iff hκ hτ _ _).trans (conjI_mem_RStab_iff g _)
  have hconc2 : muStd ka μR {x | Matrix.of x ∉ RStab (k0 + 1) r (gStd ka g)} = 0 := by
    unfold muStd
    rw [← cjE_coe hκ hτ, MeasurableEquiv.map_apply, ← cAE_coe, MeasurableEquiv.map_apply]
    convert hconc using 2
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, cAE_coe, cjE_coe]
    exact not_congr (hmem x)
  have hne2 : muStd ka μR ≠ 0 := by
    unfold muStd
    rw [← cjE_coe hκ hτ, ← cAE_coe]
    exact (Measure.map_ne_zero_iff (cjE hκ hτ).measurable.aemeasurable).mpr
      ((Measure.map_ne_zero_iff (cAE (k0 + 1) r).measurable.aemeasurable).mpr hne)
  have : SFinite (muStd ka μR) := by unfold muStd; infer_instance

  obtain ⟨θ, hθ, hint⟩ := hcut
  have hμ : B.μSS = pairMeas (standardBesselDatumRescaled L ka hka κ₀) := by
    show (B.μW.prod B.μN).prod (B.μW'.prod B.μN) = _
    rw [hBW, hBN, hBW']
    rfl
  have hI : ∀ θ' : Formalism.FourierDecayAlt.B.SS (k0 + 1) r → ℝ,
      (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p) =
      fun p => θ' p • besselIntg (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g) p := by
    intro θ'
    funext p
    exact congrArg (fun X => θ' p • X)
      (Formalism.MainNotions.BigCellDensity.integrand_eq (standardBesselDatumRescaled L ka hka κ₀) B hc2 hBz hBz' hBπ hBπ' (stdF L ka F) (gStd ka g) p)
  have hW := Formalism.MainNotions.BigCellDensity.weil_L_gen (standardBesselDatumRescaled L ka hka κ₀) hc2 h0 h1 hg2 hrel2 hconc2 hne2 hq2 (stdF L ka F)
  have hfin : OrbInt (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g)
      ((t * t) • ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1))) = ((t * t).toReal : ℂ) • OrbInt L F g ν := by
    show OrbInt (stdL L ka hka) (stdF L ka F) (gStd ka g)
      ((t * t) • ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1))) = _
    rw [gStd, OrbInt_trD hκ hτ (turnL L ka) _ _ _ _ _ _ _ (stdF L ka F) g1 (t * t) (ν.map (thP (k0 + 1) r))]
    have hfe : (fun x => stdF L ka F (cj (k0 + 1) r ka⁻¹ 1 x)) = turnF L ka F := by
      funext x
      show turnF L ka F (cjI (k0 + 1) r ka⁻¹ 1 (cj (k0 + 1) r ka⁻¹ 1 x)) = _
      rw [cjI_cj hκ hτ]
    rw [hfe, OrbInt_turn L ka hc F g ν]
  unfold Formalism.FourierDecayAlt.D.orbJ
  rw [dif_pos ⟨θ, hθ, hint⟩]
  have hspec := (⟨θ, hθ, hint⟩ : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut B (gStd ka g) (muStd ka μR) θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p) B.μSS).choose_spec
  generalize (⟨θ, hθ, hint⟩ : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut B (gStd ka g) (muStd ka μR) θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p) B.μSS).choose = θ' at hspec ⊢
  have hint' : Integrable (fun p => θ' p • besselIntg (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g) p)
      (pairMeas (standardBesselDatumRescaled L ka hka κ₀)) := by
    have h2 := hspec.2
    rw [hI θ', hμ] at h2
    exact h2
  have hθ1 : ∀ p, Formalism.MainNotions.BigCellDensity.InPair (standardBesselDatumRescaled L ka hka κ₀) p →
      ∫ x, θ' (stabAct (gStd ka g) (Matrix.of x) p) ∂(muStd ka μR) = 1 := by
    intro p hp
    refine hspec.1.2.2 p ?_
    unfold Formalism.FourierDecayAlt.B.RealPlaceData.inSS
    rw [hBz, hBz']
    exact hp
  have e1 : (∫ p, θ' p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p ∂B.μSS) =
      ∫ p, θ' p • besselIntg (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g) p ∂(pairMeas (standardBesselDatumRescaled L ka hka κ₀)) := by
    rw [hμ]
    exact congrArg (fun f => ∫ p, f p ∂(pairMeas (standardBesselDatumRescaled L ka hka κ₀))) (hI θ')
  exact e1.trans ((hW θ' hθ1 hint').trans hfin)

end Formalism.L2.SG.Pf.Carrier.CarPinTor
