import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementH
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementE
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MkLeOfDenseRange
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.HasSubstBlock
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.GramFrameCompositionMvExpFact
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.JetsLin
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.MatrixFormDiagBlocksBlockEmbed
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.MulRing
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.LocNormFreeProof
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Inertia
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.AgreeOnAdjoin
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenCompatOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenFrameEOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Tensor
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenFinal
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.NormLtOne
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OrthogonalShapeOneLetter
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormLeOneOfQuad
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.IntegralOperatorTwoOrthogonal
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThmBGaussOrthOf
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OfClosedInt
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.GaussJetBounds.FinalB

noncomputable section

open scoped BigOperators
open Formalism.L2.Th1.H

namespace GlobalTheory.ThLoc.LocJets

section Jets

open scoped ComplexConjugate
open Formalism.L2.Th1.GD
open Formalism.L2.Th1.Top (IsLatH phC thetaZ)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.L2.Th1.A (logSer expSer)
open Formalism.L2.Th1.G (linSub toZ phSum betaPair)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair jetPairPoly minorProd)
open Formalism.L2.Th1.CM (omegaK)
open Formalism.L2.Th1.Top.CAux

/- English proof (translation)
Assemble the required witnesses or components as `⟨hcm.2.2.2.prime.squarefree, by have := hcm.2.2.1; omega, Formalism.L2.Th1.F.hasCMByScale dK _ lam hlam (Formalism.L2.Th1.F.cmPairHasCMBy a₀ b₀ c₀ dK ha hdK hcm.1 (Formalism.L2.Th1.H.CmData.odd_b a₀ b₀ c₀ dK hcm.1 hcm.2.2.1))⟩`.
-/
theorem data {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (hcm : CmOK a₀ b₀ c₀ dK) :
    Squarefree dK ∧ dK % 4 = 3 ∧ Formalism.L2.Th1.CM.HasCMBy dK (cmL a₀ b₀ dK ha hdK lam hlam) :=
  ⟨hcm.2.2.2.prime.squarefree, by have := hcm.2.2.1; omega,
    Formalism.L2.Th1.F.hasCMByScale dK _ lam hlam (Formalism.L2.Th1.F.cmPairHasCMBy a₀ b₀ c₀ dK ha hdK hcm.1
      (Formalism.L2.Th1.H.CmData.odd_b a₀ b₀ c₀ dK hcm.1 hcm.2.2.1))⟩

/- English proof (translation)
Use `(Formalism.L2.Th1.G.jets_in_norm_holds K X _).2 ?_` and prove the remaining obligations. Use `Formalism.L2.Th1.G.jetsIn_sum _ _ fun k _ => ?_` and prove the remaining obligations. Conclude with `Formalism.L2.Th1.G.jetsIn_mul (Formalism.L2.Th1.G.jetsIn_C (hr k)) ((Formalism.L2.Th1.G.jets_in_norm_holds K X _).1 (hsg k))`.
-/
theorem jets_comb {K : Type} [NormedField K] [IsUltrametricDist K] {X κ : Type} [Fintype κ] (r : κ → K)
    (sg : κ → MvPowerSeries X K) (hr : ∀ k, ‖r k‖ ≤ 1) (hsg : ∀ k, JetsIntegral (sg k)) :
    JetsIntegral (∑ k, MvPowerSeries.C (r k) * sg k) := by
  refine (Formalism.L2.Th1.G.jets_in_norm_holds K X _).2 ?_
  refine Formalism.L2.Th1.G.jetsIn_sum _ _ fun k _ => ?_
  exact Formalism.L2.Th1.G.jetsIn_mul (Formalism.L2.Th1.G.jetsIn_C (hr k))
    ((Formalism.L2.Th1.G.jets_in_norm_holds K X _).1 (hsg k))

/- English proof (translation)
Introduce `a₀ b₀ c₀ dK ha hdK lam hlam hcmok n _ _ h Λ hsd hst θ hθ p _ hd ι hW hLN κx _ r t N hr hN hpN ht J _ v H _ _ N0 N1 A u th q hth hPF`. Take `⟨-, hmod, hcm⟩` from `data ha hdK lam hlam hcmok`. Take `⟨hlp, hu, hph0⟩` from `frame (cmL a₀ b₀ dK ha hdK lam hlam) ι hW`. Establish `hSh` using `(Formalism.L2.Th1.Top.ShapeCM_of Formalism.L2.Th1.Top.CMDatum_proof) dK _ hmod hcm p hd ι hW`. Establish `h2 : p ≠ 2` using `ne_two hmod hd`.

Take `⟨g₁, ε, hiso, hidx, hidx', hε, hten⟩` from `hLN`. Take `⟨hv, hA, hq, hid⟩` from `hPF`. Take `⟨D, q0, hD, hq0, hfac, hgram⟩` from `hG a₀ b₀ c₀ dK ha hdK lam hlam hcmok n h Λ g₁ hiso p ι hidx J v hv`. Establish `hθn` using `(hI dK hmod p ι).1`. Generalize the expression as in `ι (Complex.I * ((Real.sqrt dK : ℝ) : ℂ)) = θ₀ at hgram hθn`.

Take `⟨Cm, q1, hCm, hq1, hfacC, hgramC⟩` from `hF ℂ_[p] (Fin 4 × n) n J ((Bool × H) × Fin N0 × Fin N1) (fun w w' => ι (g₁.symm (Pi.single w' 1) w)) D (fun i j => ι (v j i)) (fun j k => ι (hOK (cmL a₀ b₀ dK ha hdK lam hlam) h (v j) (v k))) θ₀ q0 A hD hq0 hA hfac hgram`. Establish `hd0 : 0 < ‖(dK : ℂ_[p])‖` using `norm_pos_iff.mpr (d_ne hmod)`. Establish `hθpos : 0 < ‖θ₀‖`. Rewrite using `[hθn]`. Conclude with `Real.rpow_pos_of_pos hd0 _`.

Establish `hθ0 : θ₀ ≠ 0` using `norm_pos_iff.mp hθpos`. Establish `hquot : ‖th / θ₀‖ ≤ 1`. Rewrite using `[norm_div, div_le_one hθpos, hθn]`. Conclude with `hth`. Establish `hq' : ∀ x y : Fin 4 × ((Bool × H) × Fin N0 × Fin N1), ‖q1 x y + (if x.1 = y.1 then (th / θ₀) * q x.2 y.2 else 0)‖ ≤ 1`.

Introduce `x y`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hq1 x y) ?_)` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ hquot (norm_nonneg _) (hq _ _)`.

Simplify using the standard rewrite rules. Establish `hgram' : ∀ x y : Fin 4 × ((Bool × H) × Fin N0 × Fin N1), ∑ w, Cm w x * Cm w y = (if x.1 = y.1 ∧ x.2.1.2 = y.2.1.2 ∧ x.2.2 = y.2.2 ∧ x.2.1.1 ≠ y.2.1.1 then u x.2.1.2 else 0) + θ₀ * (q1 x y + (if x.1 = y.1 then (th / θ₀) * q x.2 y.2 else 0))`. Introduce `x y`. Rewrite using `[hgramC x y]`. Distinguish the cases in `hxy : x.1 = y.1`.

Establish `e` using `hid x.2 y.2`. Simplify using `only [RingEquiv.coe_toRingHom] at e`. Simplify using `only [hxy, if_true, true_and]`. Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hxy, if_false, false_and, add_zero]`. Establish `key : ∀ k, ∃ sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p], JetsIntegral sg ∧ linSub (frameM (ι : ℂ →+* ℂ_[p]) v A) (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv (opU (matH h) (t k) θ))) = Formalism.DworkPowerSeriesWeights.mvExp ((-(Formalism.L2.Th1.C.jet (logSer (curv …`. Introduce `k`. Take `⟨G, hGi, hGe⟩` from `hT a₀ b₀ c₀ dK ha hdK lam hlam hcmok n h Λ hsd hst θ hθ p h2 ι hW g₁ ε hiso hidx hidx' hε hten (t k) N hN hpN (ht k)`.

Conclude with `hS ℂ_[p] _ _ _ dK hlp hu hph0 hSh (d_ne hmod) (norm_two h2) n _ _ G hGi hGe H N0 N1 (frameM (ι : ℂ →+* ℂ_[p]) v A) Cm u θ₀ _ hCm hfacC hθn.le hq' hgram'`. Use `choose sg hsg he using key`. Use `⟨hSh.1, ∑ k, MvPowerSeries.C (r k) * sg k, jets_comb r sg hr hsg, ?_⟩` and prove the remaining obligations. Unfold `thetaLin`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[he k]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shape_paired_of (hT : TensStd) (hG : GramTransfer) (hI : IotaOK) (hF : FrameCompose) (hS : ShapeLin) :
    ShapeLoc := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcmok n _ _ h Λ hsd hst θ hθ p _ hd ι hW hLN κx _ r t N hr hN hpN ht
    J _ v H _ _ N0 N1 A u th q hth hPF
  obtain ⟨-, hmod, hcm⟩ := data ha hdK lam hlam hcmok
  obtain ⟨hlp, hu, hph0⟩ := frame (cmL a₀ b₀ dK ha hdK lam hlam) ι hW
  have hSh := (Formalism.L2.Th1.Top.ShapeCM_of Formalism.L2.Th1.Top.CMDatum_proof) dK _ hmod hcm p hd ι hW
  have h2 : p ≠ 2 := ne_two hmod hd
  obtain ⟨g₁, ε, hiso, hidx, hidx', hε, hten⟩ := hLN
  obtain ⟨hv, hA, hq, hid⟩ := hPF
  obtain ⟨D, q0, hD, hq0, hfac, hgram⟩ :=
    hG a₀ b₀ c₀ dK ha hdK lam hlam hcmok n h Λ g₁ hiso p ι hidx J v hv
  have hθn := (hI dK hmod p ι).1
  generalize ι (Complex.I * ((Real.sqrt dK : ℝ) : ℂ)) = θ₀ at hgram hθn
  obtain ⟨Cm, q1, hCm, hq1, hfacC, hgramC⟩ :=
    hF ℂ_[p] (Fin 4 × n) n J ((Bool × H) × Fin N0 × Fin N1)
      (fun w w' => ι (g₁.symm (Pi.single w' 1) w)) D (fun i j => ι (v j i))
      (fun j k => ι (hOK (cmL a₀ b₀ dK ha hdK lam hlam) h (v j) (v k))) θ₀ q0 A hD hq0 hA hfac hgram
  have hd0 : 0 < ‖(dK : ℂ_[p])‖ := norm_pos_iff.mpr (d_ne hmod)
  have hθpos : 0 < ‖θ₀‖ := by
    rw [hθn]
    exact Real.rpow_pos_of_pos hd0 _
  have hθ0 : θ₀ ≠ 0 := norm_pos_iff.mp hθpos
  have hquot : ‖th / θ₀‖ ≤ 1 := by
    rw [norm_div, div_le_one hθpos, hθn]
    exact hth
  have hq' : ∀ x y : Fin 4 × ((Bool × H) × Fin N0 × Fin N1),
      ‖q1 x y + (if x.1 = y.1 then (th / θ₀) * q x.2 y.2 else 0)‖ ≤ 1 := by
    intro x y
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hq1 x y) ?_)
    split_ifs
    · rw [norm_mul]
      exact mul_le_one₀ hquot (norm_nonneg _) (hq _ _)
    · simp
  have hgram' : ∀ x y : Fin 4 × ((Bool × H) × Fin N0 × Fin N1), ∑ w, Cm w x * Cm w y =
      (if x.1 = y.1 ∧ x.2.1.2 = y.2.1.2 ∧ x.2.2 = y.2.2 ∧ x.2.1.1 ≠ y.2.1.1 then u x.2.1.2 else 0)
        + θ₀ * (q1 x y + (if x.1 = y.1 then (th / θ₀) * q x.2 y.2 else 0)) := by
    intro x y
    rw [hgramC x y]
    by_cases hxy : x.1 = y.1
    · have e := hid x.2 y.2
      simp only [RingEquiv.coe_toRingHom] at e
      simp only [hxy, if_true, true_and]
      rw [e]
      field_simp
      ring
    · simp only [hxy, if_false, false_and, add_zero]
  have key : ∀ k, ∃ sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p], JetsIntegral sg ∧
      linSub (frameM (ι : ℂ →+* ℂ_[p]) v A)
        (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv (opU (matH h) (t k) θ))) =
      Formalism.DworkPowerSeriesWeights.mvExp ((-(Formalism.L2.Th1.C.jet (logSer (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι))
        (phC p (cmL a₀ b₀ dK ha hdK lam hlam) ι) 2)) • betaPair H N0 N1 u) * sg := by
    intro k
    obtain ⟨G, hGi, hGe⟩ := hT a₀ b₀ c₀ dK ha hdK lam hlam hcmok n h Λ hsd hst θ hθ p h2 ι hW g₁ ε hiso hidx
      hidx' hε hten (t k) N hN hpN (ht k)
    exact hS ℂ_[p] _ _ _ dK hlp hu hph0 hSh (d_ne hmod) (norm_two h2) n _ _ G hGi hGe H N0 N1
      (frameM (ι : ℂ →+* ℂ_[p]) v A) Cm u θ₀ _ hCm hfacC hθn.le hq' hgram'
  choose sg hsg he using key
  refine ⟨hSh.1, ∑ k, MvPowerSeries.C (r k) * sg k, jets_comb r sg hr hsg, ?_⟩
  unfold thetaLin
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he k]
  ring

/- English proof (translation)
Introduce `a₀ b₀ c₀ dK ha hdK lam hlam hcmok n _ _ h Λ hsd hst θ hθ p _ h2 hd ι hW hLN κx _ r t N hr hN hpN ht J _ v hv ν _ A hA`. Take `⟨-, hmod, hcm⟩` from `data ha hdK lam hlam hcmok`. Take `⟨hlp, hu, hph0⟩` from `frame (cmL a₀ b₀ dK ha hdK lam hlam) ι hW`. Establish `hjets` using `(Formalism.L2.Th1.Top.JetsCM_of Formalism.L2.Th1.Top.CMDatum_proof) dK _ hmod hcm p h2 hd ι hW`. Take `⟨g₁, ε, hiso, hidx, hidx', hε, hten⟩` from `hLN`.

Take `⟨D, q0, hD, hq0, hfac, hgram⟩` from `hG a₀ b₀ c₀ dK ha hdK lam hlam hcmok n h Λ g₁ hiso p ι hidx J v hv`. Take `⟨Cm, q1, hCm, -, hfacC, -⟩` from `hF ℂ_[p] (Fin 4 × n) n J ν (fun w w' => ι (g₁.symm (Pi.single w' 1) w)) D (fun i j => ι (v j i)) (fun j k => ι (hOK (cmL a₀ b₀ dK ha hdK lam hlam) h (v j) (v k))) _ q0 A hD hq0 hA hfac hgram`. Establish `key : ∀ k, JetsIntegral (linSub (frameM (ι : ℂ →+* ℂ_[p]) v A) (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv (opU (matH h) (t k) θ))))`. Introduce `k`. Take `⟨G, hGi, hGe⟩` from `hT a₀ b₀ c₀ dK ha hdK lam hlam hcmok n h Λ hsd hst θ hθ p h2 ι hW g₁ ε hiso hidx hidx' hε hten (t k) N hN hpN (ht k)`.

Conclude with `hJ ℂ_[p] _ _ _ hlp hu hph0 hjets (norm_two h2) n _ _ G hGi hGe ν (frameM (ι : ℂ →+* ℂ_[p]) v A) Cm hCm hfacC`. Establish `hall : JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A))` using `jets_comb r _ hr key`. Conclude with `⟨hall, fun P hP => Formalism.DworkPowerSeriesWeights.intOp ℂ_[p] ν _ hall P hP⟩`.
-/
theorem jets_odd_of (hT : TensStd) (hG : GramTransfer) (hF : FrameCompose) (hJ : JetsLin) : IntOpLoc := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcmok n _ _ h Λ hsd hst θ hθ p _ h2 hd ι hW hLN κx _ r t N hr hN hpN ht
    J _ v hv ν _ A hA
  obtain ⟨-, hmod, hcm⟩ := data ha hdK lam hlam hcmok
  obtain ⟨hlp, hu, hph0⟩ := frame (cmL a₀ b₀ dK ha hdK lam hlam) ι hW
  have hjets := (Formalism.L2.Th1.Top.JetsCM_of Formalism.L2.Th1.Top.CMDatum_proof) dK _ hmod hcm p h2 hd ι hW
  obtain ⟨g₁, ε, hiso, hidx, hidx', hε, hten⟩ := hLN
  obtain ⟨D, q0, hD, hq0, hfac, hgram⟩ :=
    hG a₀ b₀ c₀ dK ha hdK lam hlam hcmok n h Λ g₁ hiso p ι hidx J v hv
  obtain ⟨Cm, q1, hCm, -, hfacC, -⟩ :=
    hF ℂ_[p] (Fin 4 × n) n J ν
      (fun w w' => ι (g₁.symm (Pi.single w' 1) w)) D (fun i j => ι (v j i))
      (fun j k => ι (hOK (cmL a₀ b₀ dK ha hdK lam hlam) h (v j) (v k))) _ q0 A hD hq0 hA hfac hgram
  have key : ∀ k, JetsIntegral (linSub (frameM (ι : ℂ →+* ℂ_[p]) v A)
        (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv (opU (matH h) (t k) θ)))) := by
    intro k
    obtain ⟨G, hGi, hGe⟩ := hT a₀ b₀ c₀ dK ha hdK lam hlam hcmok n h Λ hsd hst θ hθ p h2 ι hW g₁ ε hiso hidx
      hidx' hε hten (t k) N hN hpN (ht k)
    exact hJ ℂ_[p] _ _ _ hlp hu hph0 hjets (norm_two h2) n _ _ G hGi hGe ν
      (frameM (ι : ℂ →+* ℂ_[p]) v A) Cm hCm hfacC
  have hall : JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) :=
    jets_comb r _ hr key
  exact ⟨hall, fun P hP => Formalism.DworkPowerSeriesWeights.intOp ℂ_[p] ν _ hall P hP⟩

open Formalism.L2.Th1.H Formalism.L2.Th1.H.FormalGroupLawNegation in

/- English proof (translation)
Take `⟨S, hS⟩` from `(cosetRepsExist _ (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) hD.idx₁).1`. Establish `hNt'` using `smul_img_mem Λ g t (N : ℂ) hNt`. Establish `hF0 : AnalyticAt ℂ (opU (matH h) t θ) 0` using `opUAnalytic _ (matH h) t θ hθ.1 0 (Set.mem_univ _)`. Establish `hth : Differentiable ℂ (Formalism.L2.Th1.F.th0 L (ω₀ / 2))` using `(Formalism.L2.Th1.F.th0Basic L ω₀ hD.per hD.half).1`. Set `M : Matrix (Fin 4 × n) (Fin 4 × n) ℂ` to `LinearMap.toMatrix' (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))`.

Set `c : (Fin 4 × n → ℂ) → ℂ` to `fun x => ε * ((Real.sqrt (relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) : ℝ) : ℂ)⁻¹ * β x * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (stdH L (Fin 4 × n)) (g fun w => t w.2) x : ℂ))`. Set `f : (Fin 4 × n → ℂ) → Fin 4 × n → ℂ → ℂ` to `fun x w => Formalism.L2.Th1.F.opU L (g (fun w => t w.2) w + x w) (Formalism.L2.Th1.F.th0 L (ω₀ / 2))`. Establish `hf : ∀ x w, AnalyticAt ℂ (f x w) 0` using `fun x w => analyticAt_opU L _ hth`. Establish `hfun : (fun y => Formalism.L2.Th1.H.tens4 (opU (matH h) t θ) (M.mulVec y)) = fun y => ∑ x ∈ S, c x * prodFn (f x) y`. Use function extensionality and compare the values at `y`.

Rewrite using `[LinearMap.toMatrix'_mulVec]`. Conclude with `quadraticSemicharacter_identity_reformulated₂ L ω₀ n h Λ α β g hD ε θ hten S hS t y`. Establish `hT : linSubst M (Formalism.L2.Th1.E.tensor4 (taylorMv (opU (matH h) t θ))) = ∑ x ∈ S, MvPowerSeries.C (c x) * ∏ w, Formalism.InvariantFactorPaths.G7.at1 w (Formalism.L2.Th1.F.taylor0 (f x w))`. Rewrite using `[← taylorMvTens4 n _ hF0, ← taylorMvComp _ _ M _ (analyticAt_tens4 hF0), hfun, (taylorMv_sum taylorMvLinear S c _ fun x => analyticAt_prodFn (hf x)).2]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[taylorMvProd _ _ (hf x)]`. Use `⟨{x // x ∈ S}, inferInstance, fun x => ι (c x), fun x w => g (fun w => t w.2) w + (x : Fin 4 × n → ℂ) w, N * relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)), ?_, Nat.mul_pos hN (Nat.pos_of_ne_zero hD.idx₁), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Conclude with `norm_coeff ι _ _ hD.selfDual β hD.betaSemi _ hln ε hε _ _ N hN hNt' (hS.1 x x.2)`. Introduce `hd`.

Break down `(Nat.Prime.dvd_mul Fact.out).1 hd with h1 | h1` into its components or cases. Conclude with `hlN h1`. Conclude with `hln h1`. Introduce `x w`. Conclude with `trans_mem L _ _ _ N hNt' (hS.1 x x.2) w`.

Establish `e1 : linSub (fun w w' => ι (g.symm (Pi.single w' 1) w)) (Formalism.L2.Th1.G.tens4 (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv (opU (matH h) t θ)))) = linSubst (M.map (ι : ℂ →+* ℂ_[p])) (Formalism.L2.Th1.E.tensor4 (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv (opU (matH h) t θ …` using `rfl`. Rewrite using `[e1, ← map_tensor4, ← map_linSubst, hT, map_sumProd]`. Unfold `thetaZ Formalism.L2.Th1.E.thetaProd`. Conclude with `(Finset.sum_coe_sort S fun x => MvPowerSeries.C (ι (c x)) * ∏ w, Formalism.InvariantFactorPaths.G7.at1 w (PowerSeries.map (ι : ℂ →+* ℂ_[p]) (Formalism.L2.Th1.F.taylor0 (f x w)))).symm`.
-/
theorem tens_std (p : ℕ) [Fact p.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]) (ω₀ : ℂ)
    (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ)
    (β : (Fin 4 × n → ℂ) → ℂ) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (hD : StdData L ω₀ h Λ α β g)
    (hln : ¬ p ∣ relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)))
    (ε : ℂ) (hε : ‖ι ε‖ ≤ 1) (θ : (n → ℂ) → ℂ) (hθ : θ ∈ Th (matH h) α Λ)
    (hten : Formalism.L2.Th1.H.tens4 θ = ε • kernel4 L ω₀ Λ β g)
    (t : n → ℂ) (N : ℕ) (hN : 0 < N) (hlN : ¬ p ∣ N) (hNt : (N : ℂ) • t ∈ Λ) :
    ∃ (κ : Type) (_ : Fintype κ) (r : κ → ℂ_[p]) (s : κ → Fin 4 × n → ℂ) (N' : ℕ),
      (∀ k, ‖r k‖ ≤ 1) ∧ 0 < N' ∧ ¬ p ∣ N' ∧ (∀ k w, (N' : ℂ) * s k w ∈ L.lattice) ∧
      linSub (fun w w' => ι (g.symm (Pi.single w' 1) w))
          (Formalism.L2.Th1.G.tens4 (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv (opU (matH h) t θ)))) =
        thetaZ p L ι ω₀ r s := by
  classical
  obtain ⟨S, hS⟩ := (cosetRepsExist _ (stdLat L (Fin 4 × n))
    (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) hD.idx₁).1
  have hNt' := smul_img_mem Λ g t (N : ℂ) hNt
  have hF0 : AnalyticAt ℂ (opU (matH h) t θ) 0 := opUAnalytic _ (matH h) t θ hθ.1 0 (Set.mem_univ _)
  have hth : Differentiable ℂ (Formalism.L2.Th1.F.th0 L (ω₀ / 2)) := (Formalism.L2.Th1.F.th0Basic L ω₀ hD.per hD.half).1
  let M : Matrix (Fin 4 × n) (Fin 4 × n) ℂ :=
    LinearMap.toMatrix' (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))
  let c : (Fin 4 × n → ℂ) → ℂ := fun x =>
    ε * ((Real.sqrt (relIdx (stdLat L (Fin 4 × n))
              (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) : ℝ) : ℂ)⁻¹ * β x
            * Complex.exp (-(Real.pi : ℂ) * Complex.I
                * (altE (stdH L (Fin 4 × n)) (g fun w => t w.2) x : ℂ))
  let f : (Fin 4 × n → ℂ) → Fin 4 × n → ℂ → ℂ := fun x w =>
    Formalism.L2.Th1.F.opU L (g (fun w => t w.2) w + x w) (Formalism.L2.Th1.F.th0 L (ω₀ / 2))
  have hf : ∀ x w, AnalyticAt ℂ (f x w) 0 := fun x w => analyticAt_opU L _ hth
  have hfun : (fun y => Formalism.L2.Th1.H.tens4 (opU (matH h) t θ) (M.mulVec y)) =
      fun y => ∑ x ∈ S, c x * prodFn (f x) y := by
    funext y
    rw [LinearMap.toMatrix'_mulVec]
    exact quadraticSemicharacter_identity_reformulated₂ L ω₀ n h Λ α β g hD ε θ hten S hS t y
  have hT : linSubst M (Formalism.L2.Th1.E.tensor4 (taylorMv (opU (matH h) t θ))) =
      ∑ x ∈ S, MvPowerSeries.C (c x) * ∏ w, Formalism.InvariantFactorPaths.G7.at1 w (Formalism.L2.Th1.F.taylor0 (f x w)) := by
    rw [← taylorMvTens4 n _ hF0, ← taylorMvComp _ _ M _ (analyticAt_tens4 hF0), hfun,
      (taylorMv_sum taylorMvLinear S c _ fun x => analyticAt_prodFn (hf x)).2]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [taylorMvProd _ _ (hf x)]
  refine ⟨{x // x ∈ S}, inferInstance, fun x => ι (c x), fun x w => g (fun w => t w.2) w + (x : Fin 4 × n → ℂ) w,
    N * relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)),
    ?_, Nat.mul_pos hN (Nat.pos_of_ne_zero hD.idx₁), ?_, ?_, ?_⟩
  · intro x
    exact norm_coeff ι _ _ hD.selfDual β hD.betaSemi _ hln ε hε _ _ N hN hNt' (hS.1 x x.2)
  · intro hd
    rcases (Nat.Prime.dvd_mul Fact.out).1 hd with h1 | h1
    · exact hlN h1
    · exact hln h1
  · intro x w
    exact trans_mem L _ _ _ N hNt' (hS.1 x x.2) w
  · have e1 : linSub (fun w w' => ι (g.symm (Pi.single w' 1) w))
          (Formalism.L2.Th1.G.tens4 (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv (opU (matH h) t θ)))) =
        linSubst (M.map (ι : ℂ →+* ℂ_[p]))
          (Formalism.L2.Th1.E.tensor4 (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv (opU (matH h) t θ)))) := rfl
    rw [e1, ← map_tensor4, ← map_linSubst, hT, map_sumProd]
    unfold thetaZ Formalism.L2.Th1.E.thetaProd
    exact (Finset.sum_coe_sort S fun x => MvPowerSeries.C (ι (c x)) * ∏ w, Formalism.InvariantFactorPaths.G7.at1 w
      (PowerSeries.map (ι : ℂ →+* ℂ_[p]) (Formalism.L2.Th1.F.taylor0 (f x w)))).symm

/- English proof (translation)
Unfold `omegaK`. Rewrite using `[map_div₀, map_add, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_omegaK (d : ℕ) : conj (omegaK d) = (1 - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
  unfold omegaK
  rw [map_div₀, map_add, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofNat]
  ring

/- English proof (translation)
Introduce `hmem`. Establish `hw1 : (cmL a b d ha hd lam hlam).ω₁ = lam * (a : ℂ)` using `rfl`. Establish `hw2 : (cmL a b d ha hd lam hlam).ω₂ = lam * Formalism.L2.Th1.F.cmTheta b d` using `rfl`. Take `⟨x, y, e1⟩` from `PeriodPair.mem_lattice.mp hmem`. Rewrite `e1` using `[hw1, hw2]`.

Unfold `Formalism.L2.Th1.F.cmTheta at e1`. Use `set S : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hSdef`. Establish `f1 : (x : ℂ) * a + y * (((b : ℂ) + S) / 2) = (1 + (sg : ℂ) * S) / 2 * ((a : ℂ) / 2)`. Apply `mul_left_cancel₀ hlam` to reduce the goal to its premises. Take the linear combination `e1`.

Establish `key : ((4 * x * a + 2 * y * b - a : ℤ) : ℂ) + ((2 * y - sg * a : ℤ) : ℂ) * S = 0`. Use `push_cast`. Take the linear combination `4 * f1`. Take `⟨-, k2⟩` from `GramFrameMultiplicativityLemmas.indep_sqrt hd _ _ key`. Take `⟨k, hk⟩` from `hOK.2.1`.

Apply the tactic sequence `rcases hsg with h | h <;> subst h <;> omega`.
-/
theorem half_notMem {a : ℕ} {b c : ℤ} {d : ℕ} (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    (hOK : CmOK a b c d) (sg : ℤ) (hsg : sg = 1 ∨ sg = -1) :
    (1 + (sg : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ))) / 2 * (lam * (a : ℂ) / 2) ∉
      (cmL a b d ha hd lam hlam).lattice := by
  intro hmem
  have hw1 : (cmL a b d ha hd lam hlam).ω₁ = lam * (a : ℂ) := rfl
  have hw2 : (cmL a b d ha hd lam hlam).ω₂ = lam * Formalism.L2.Th1.F.cmTheta b d := rfl
  obtain ⟨x, y, e1⟩ := PeriodPair.mem_lattice.mp hmem
  rw [hw1, hw2] at e1
  unfold Formalism.L2.Th1.F.cmTheta at e1
  set S : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hSdef
  have f1 : (x : ℂ) * a + y * (((b : ℂ) + S) / 2) = (1 + (sg : ℂ) * S) / 2 * ((a : ℂ) / 2) := by
    apply mul_left_cancel₀ hlam
    linear_combination e1
  have key : ((4 * x * a + 2 * y * b - a : ℤ) : ℂ) + ((2 * y - sg * a : ℤ) : ℂ) * S = 0 := by
    push_cast
    linear_combination 4 * f1
  obtain ⟨-, k2⟩ := GramFrameMultiplicativityLemmas.indep_sqrt hd _ _ key
  obtain ⟨k, hk⟩ := hOK.2.1
  rcases hsg with h | h <;> subst h <;> omega

/- English proof (translation)
Introduce `a₀ b₀ c₀ dK ha hdK lam hlam hcm n _ _ h Λ hSD hSt θ hθ p _ ι g₁ ε hI hidx hidx2 hε htens t N hN hpN ht`. Establish `hidx1 : relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0`. Introduce `h0`. Conclude with `hidx (h0 ▸ dvd_zero p)`. Establish `hS` using `Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ g₁ hI hSD hSt hidx1 hidx2`.

Conclude with `tens_std p _ ι _ n h Λ _ _ g₁ hS hidx ε hε θ hθ htens t N hN hpN ht`.
-/
theorem fourth_power_theta : TensZ := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcm n _ _ h Λ hSD hSt θ hθ p _ ι g₁ ε hI hidx hidx2 hε htens t N hN hpN ht
  have hidx1 : relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0 := by
    intro h0
    exact hidx (h0 ▸ dvd_zero p)

  have hS := Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ g₁
    hI hSD hSt hidx1 hidx2
  exact tens_std p _ ι _ n h Λ _ _ g₁ hS hidx ε hε θ hθ htens t N hN hpN ht

open Formalism.L2.Th1.G JL Formalism.G in

/- English proof (translation)
Introduce `K _ _ _ n _ T γ hT ν _ M Cm hC hM`. Establish `k1 : JetsIn (unitBall K) (linSub γ (Formalism.L2.Th1.G.tens4 T))` using `(jets_in_norm_holds K _ _).1 hT`. Establish `k2 : JetsIn (unitBall K) (linSub Cm (linSub γ (Formalism.L2.Th1.G.tens4 T)))` using `jetsIn_linSub hC k1`. Establish `e : (fun (w : Fin 4 × n) (x : Fin 4 × ν) => ∑ w', γ w w' * Cm w' x) = four M`. Use function extensionality and compare the values at `w x`.

Conclude with `hM w.1 w.2 x.1 x.2`. Rewrite `k2` using `[linSub_linSub, e, linSub_tens4]`. Conclude with `jets_fourth_holds K (unitBall K) ν (linSub M T) fourth_root_mem k2`.
-/
theorem jets_linear : JetsLinZ := by
  intro K _ _ _ n _ T γ hT ν _ M Cm hC hM
  have k1 : JetsIn (unitBall K) (linSub γ (Formalism.L2.Th1.G.tens4 T)) := (jets_in_norm_holds K _ _).1 hT
  have k2 : JetsIn (unitBall K) (linSub Cm (linSub γ (Formalism.L2.Th1.G.tens4 T))) := jetsIn_linSub hC k1
  have e : (fun (w : Fin 4 × n) (x : Fin 4 × ν) => ∑ w', γ w w' * Cm w' x) = four M := by
    funext w x
    exact hM w.1 w.2 x.1 x.2
  rw [linSub_linSub, e, linSub_tens4] at k2
  exact jets_fourth_holds K (unitBall K) ν (linSub M T) fourth_root_mem k2

/- English proof (translation)
Introduce `a₀ b₀ c₀ dK ha hdK lam hlam hcmok n _ _ h Λ hsd hst θ hθ ι W hU hW ha1 hLN κx _ r t N hr hN hpN ht J _ v hv ν _ A hA`. Take `⟨-, -, hcm⟩` from `data ha hdK lam hlam hcmok`. Establish `hω : lam * (a₀ : ℂ) ∈ (cmL a₀ b₀ dK ha hdK lam hlam).lattice` using `(cmL a₀ b₀ dK ha hdK lam hlam).ω₁_mem_lattice`. Establish `hω1 : omegaK dK * (lam * (a₀ : ℂ) / 2) ∉ (cmL a₀ b₀ dK ha hdK lam hlam).lattice`. Use `half_notMem ha hdK lam hlam hcmok 1 (Or.inl rfl)` as an intermediate fact.

Simplify `this` using `[omegaK]`. Establish `hω2 : conj (omegaK dK) * (lam * (a₀ : ℂ) / 2) ∉ (cmL a₀ b₀ dK ha hdK lam hlam).lattice`. Use `half_notMem ha hdK lam hlam hcmok (-1) (Or.inr rfl)` as an intermediate fact. Rewrite using `[conj_omegaK]`. Simplify `this` using `[sub_eq_add_neg]`.

Take `⟨g₁, ε, hiso, hidx, hidx', hε, hten⟩` from `hLN`. Take `⟨D, q0, hD, hq0, hfac, hgram⟩` from `hG a₀ b₀ c₀ dK ha hdK lam hlam hcmok n h Λ g₁ hiso 2 ι hidx J v hv`. Take `⟨Cm, q1, hCm, -, hfacC, -⟩` from `hF ℂ_[2] (Fin 4 × n) n J ν (fun w w' => ι (g₁.symm (Pi.single w' 1) w)) D (fun i j => ι (v j i)) (fun j k => ι (hOK (cmL a₀ b₀ dK ha hdK lam hlam) h (v j) (v k))) _ q0 A hD hq0 hA hfac hgram`. Establish `key : ∀ k, JetsIntegral (linSub (frameM (ι : ℂ →+* ℂ_[2]) v A) (MvPowerSeries.map (ι : ℂ →+* ℂ_[2]) (taylorMv (opU (matH h) (t k) θ))))`. Introduce `k`.

Take `⟨κ, _, r', s', N', hr', hN', h2N', hs', he⟩` from `hT a₀ b₀ c₀ dK ha hdK lam hlam hcmok n h Λ hsd hst θ hθ 2 ι g₁ ε hiso hidx hidx' hε hten (t k) N hN hpN (ht k)`. Establish `hj` using `(Formalism.L2.Th1.Top.integral_operator_two_orthogonal dK _ hcmok.2.2.1 hcm ι W hU hW ha1 (lam * a₀) hω hω1 hω2 (Fin 4 × n) κ r' s' N' hr' hN' h2N' hs').1`. Rewrite `hj` using `[← he]`. Conclude with `hJ ℂ_[2] n _ _ hj ν (frameM (ι : ℂ →+* ℂ_[2]) v A) Cm hCm hfacC`. Establish `hall : JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[2]) h θ r t (frameM (ι : ℂ →+* ℂ_[2]) v A))` using `jets_comb r _ hr key`.

Conclude with `⟨hall, fun P hP => Formalism.DworkPowerSeriesWeights.intOp ℂ_[2] ν _ hall P hP⟩`.
-/
theorem jets_two_of (hT : TensZ) (hG : GramTransfer) (hF : FrameCompose) (hJ : JetsLinZ) : IntOpTwoLoc := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcmok n _ _ h Λ hsd hst θ hθ ι W hU hW ha1 hLN κx _ r t N hr hN hpN ht
    J _ v hv ν _ A hA
  obtain ⟨-, -, hcm⟩ := data ha hdK lam hlam hcmok
  have hω : lam * (a₀ : ℂ) ∈ (cmL a₀ b₀ dK ha hdK lam hlam).lattice :=
    (cmL a₀ b₀ dK ha hdK lam hlam).ω₁_mem_lattice
  have hω1 : omegaK dK * (lam * (a₀ : ℂ) / 2) ∉ (cmL a₀ b₀ dK ha hdK lam hlam).lattice := by
    have := half_notMem ha hdK lam hlam hcmok 1 (Or.inl rfl)
    simpa [omegaK] using this
  have hω2 : conj (omegaK dK) * (lam * (a₀ : ℂ) / 2) ∉ (cmL a₀ b₀ dK ha hdK lam hlam).lattice := by
    have := half_notMem ha hdK lam hlam hcmok (-1) (Or.inr rfl)
    rw [conj_omegaK]
    simpa [sub_eq_add_neg] using this
  obtain ⟨g₁, ε, hiso, hidx, hidx', hε, hten⟩ := hLN
  obtain ⟨D, q0, hD, hq0, hfac, hgram⟩ :=
    hG a₀ b₀ c₀ dK ha hdK lam hlam hcmok n h Λ g₁ hiso 2 ι hidx J v hv
  obtain ⟨Cm, q1, hCm, -, hfacC, -⟩ :=
    hF ℂ_[2] (Fin 4 × n) n J ν
      (fun w w' => ι (g₁.symm (Pi.single w' 1) w)) D (fun i j => ι (v j i))
      (fun j k => ι (hOK (cmL a₀ b₀ dK ha hdK lam hlam) h (v j) (v k))) _ q0 A hD hq0 hA hfac hgram
  have key : ∀ k, JetsIntegral (linSub (frameM (ι : ℂ →+* ℂ_[2]) v A)
        (MvPowerSeries.map (ι : ℂ →+* ℂ_[2]) (taylorMv (opU (matH h) (t k) θ)))) := by
    intro k
    obtain ⟨κ, _, r', s', N', hr', hN', h2N', hs', he⟩ := hT a₀ b₀ c₀ dK ha hdK lam hlam hcmok n h Λ hsd hst θ hθ
      2 ι g₁ ε hiso hidx hidx' hε hten (t k) N hN hpN (ht k)
    have hj := (Formalism.L2.Th1.Top.integral_operator_two_orthogonal dK _ hcmok.2.2.1 hcm ι W hU hW ha1 (lam * a₀) hω hω1 hω2
      (Fin 4 × n) κ r' s' N' hr' hN' h2N' hs').1
    rw [← he] at hj
    exact hJ ℂ_[2] n _ _ hj ν (frameM (ι : ℂ →+* ℂ_[2]) v A) Cm hCm hfacC
  have hall : JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[2]) h θ r t (frameM (ι : ℂ →+* ℂ_[2]) v A)) :=
    jets_comb r _ hr key
  exact ⟨hall, fun P hP => Formalism.DworkPowerSeriesWeights.intOp ℂ_[2] ν _ hall P hP⟩

/- English proof (translation)
The claim follows from `GramTransfer_of MulRing_proof IotaOK_proof`.
-/
theorem gram_transfer : GramTransfer := GramTransfer_of MulRing_proof IotaOK_proof

/- English proof (translation)
The claim follows from `TensStd_of ShapeToZ_proof TransIntC_proof`.
-/
theorem fourth_power_std : TensStd := TensStd_of ShapeToZ_proof TransIntC_proof

/- English proof (translation)
The claim follows from `jets_odd_of fourth_power_std gram_transfer FrameCompose_proof JetsLin_proof`.
-/
theorem jetsOdd : IntOpLoc := jets_odd_of fourth_power_std gram_transfer FrameCompose_proof JetsLin_proof

/- English proof (translation)
The claim follows from `jets_two_of fourth_power_theta gram_transfer FrameCompose_proof jets_linear`.
-/
theorem jetsTwo : IntOpTwoLoc := jets_two_of fourth_power_theta gram_transfer FrameCompose_proof jets_linear

/- English proof (translation)
The claim follows from `ShapeEigenLoc_of (EigenFrameE_of (EigenFrame_of (GramBasic_of gram_transfer IotaOK_proof) (EigenCompat_of (GramBasic_of gram_transfer IotaOK_proof))) (SepPairs_of hE InertiaRam_proof) IntNorm_proof) IotaOK_proof (shape_paired_of fourth_power_std gram_transfer IotaOK_proof FrameCo …`.
-/
theorem shape (hE : EmbSep) : ShapeEigenLoc :=
  ShapeEigenLoc_of
    (EigenFrameE_of
      (EigenFrame_of (GramBasic_of gram_transfer IotaOK_proof) (EigenCompat_of (GramBasic_of gram_transfer IotaOK_proof)))
      (SepPairs_of hE InertiaRam_proof) IntNorm_proof)
    IotaOK_proof (shape_paired_of fourth_power_std gram_transfer IotaOK_proof FrameCompose_proof ShapeLin_proof)

end Jets

end GlobalTheory.ThLoc.LocJets
