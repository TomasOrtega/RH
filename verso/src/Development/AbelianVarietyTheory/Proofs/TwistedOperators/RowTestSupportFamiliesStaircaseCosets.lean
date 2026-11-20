import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowVal

/- English proof (translation)
Introduce and unpack `⟨_ | a, _ | b⟩ h1 h2`. Simplify using `at h1`. Simplify using `at h1`. Simplify using `at h2`. Both sides reduce to the same expression.
-/
theorem givenLevel_inner {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) :
    ∀ p : ℕ × ℕ, 1 ≤ p.1 → 1 ≤ p.2 → givenLevel G t w p = KO (Kw w) _ := by
  rintro ⟨_ | a, _ | b⟩ h1 h2
  · simp at h1
  · simp at h1
  · simp at h2
  · rfl

/- English proof (translation)
Use `⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩` and prove the remaining obligations. Introduce `t Φ β hβ w hw0 i`. Establish `hL : R.toLevCh.Is A.μ0` using `s.core.lev`. Establish `hde` using `GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s`. Establish `hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal` using `hch.guard t`.

Establish `hT` using `isTensor_Tflip hL ch.W ch.S.B t Φ hde hc w.2`. Establish `hm : 0 < D.R.m` using `by have := D.R.two_le_m; omega`. Establish `hcond : HasConductor (psiAt ch.W w.1) 1` using `(((Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w.1 w.2).square 0 hm 0 hm).cond`. Establish `hce : depthAt ch.G w.1 = cosExp ch.G w.1`. Establish `e : 1 ≤ cosExp ch.G w.1` using `by classical`.

Unfold `cosExp`. Rewrite using `[if_pos hw0]`. Conclude with `ch.G.pl.depth_pos _ _`. Rewrite using `[depthAt, max_eq_left e]`. Rewrite `hT` using `[hce]`.

Use `haveI := (isUnitVol_unitVol w.1).1`. Establish `hJ : ∀ j, 0 < j → j < (locGrid ch.G t w.1).m → givenLevel ch.G t w.1 ((locGrid ch.G t w.1).m, j) = KO (Kw w.1) _` using `fun j hj hj' => givenLevel_inner ch.G t w.1 _ (by change 1 ≤ D.R.m; omega) hj`. Establish `key` using `OneCosetProof.oneCoset_of_isTensor (ν := unitVol w.1) one_le_sLen hcond hT hJ`. Establish `hk : keepAt ch.G w.1 = false` using `by classical`. Unfold `keepAt`.

Simplify using `[hw0]`. Establish `hβw` using `hβ w`. Rewrite `hβw` using `[hk]`. Conclude with `key (β w) hβw i`.
-/
theorem oneAt : Big fun ch => OneAt ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t Φ β hβ w hw0 i
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hT := isTensor_Tflip hL ch.W ch.S.B t Φ hde hc w.2
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hcond : HasConductor (psiAt ch.W w.1) 1 :=
    (((Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w.1 w.2).square 0 hm 0 hm).cond
  have hce : depthAt ch.G w.1 = cosExp ch.G w.1 := by
    have e : 1 ≤ cosExp ch.G w.1 := by
      classical
      unfold cosExp
      rw [if_pos hw0]
      exact ch.G.pl.depth_pos _ _
    rw [depthAt, max_eq_left e]
  rw [hce] at hT
  haveI := (isUnitVol_unitVol w.1).1
  have hJ : ∀ j, 0 < j → j < (locGrid ch.G t w.1).m →
      givenLevel ch.G t w.1 ((locGrid ch.G t w.1).m, j) = KO (Kw w.1) _ := fun j hj hj' =>
    givenLevel_inner ch.G t w.1 _ (by change 1 ≤ D.R.m; omega) hj
  have key := OneCosetProof.oneCoset_of_isTensor (ν := unitVol w.1) one_le_sLen hcond hT hJ
  have hk : keepAt ch.G w.1 = false := by
    classical
    unfold keepAt
    simp [hw0]
  have hβw := hβ w
  rw [hk] at hβw
  exact key (β w) hβw i

end GlobalTheory.RowVal
