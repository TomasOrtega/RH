import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwSecMulPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupLatticeDegreeTwistLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedWeightDegree
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

noncomputable section

namespace GlobalTheory.FlatRootTwist

/- English proof (translation)
Introduce `v hv`. Take `⟨k, hk⟩` from `h v hv`. Use `⟨n * k, ?_⟩` and prove the remaining obligations. Simplify using `[hk]`.
-/
theorem intOff_nsmul {K : Type} [Field K] [NumberField K] {B : Finset ℕ} {ρ : HeightOneSpectrum (𝓞 K) → ℝ}
    (h : IntOff B ρ) (n : ℕ) : IntOff B (n • ρ) := by
  intro v hv
  obtain ⟨k, hk⟩ := h v hv
  refine ⟨n * k, ?_⟩
  simp [hk]

/- English proof (translation)
Substitute `hG` using the available equality. Conclude with `⟨s, rfl, rfl⟩`.
-/
theorem twSec_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    {x : ℝ} {Z : Comp Xo c} {G G' : WTZ E} (hG : G = G') (s : TwSec U x Z G) :
    ∃ t : TwSec U x Z G', t.lo = s.lo ∧ t.degLo = s.degLo := by
  subst hG
  exact ⟨s, rfl, rfl⟩

/- English proof (translation)
Introduce `_ D H Dw l Xo c r U V dict hC hF hpq hg hflat hB w m`. Establish `hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)` using `fun σ hσ => (hC.2 σ hσ).1`. Establish `hξ : ∀ σ, GoodEmb c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D` using `fun σ hσ => (hC.2 σ hσ).2.2.2`. Take `⟨hK, hroot⟩` from `GlobalTheory.KeyRootTw.exists_twSec_keyRoot _ H Dw l Xo c r U (xiR D) hU hξ hF hpq hg hB`. Use `set b : ℝ := (∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) with hb`.

Establish `hW : wtOf Dw (parWt Dw w) 0 + m • wtOf Dw 0 1 = wtOf Dw (parWt Dw w) m`. Rewrite using `[GlobalTheory.CompHt.nsmul_wtOf, ← wtOf_add]`. Simplify using the standard rewrite rules. Establish `hsec : ∀ Z : Comp Xo c, ∃ t : TwSec U (xiR D) Z (wtOf Dw (parWt Dw w) m), IntOff (badPrimes H l) t.lo ∧ b ≤ t.degLo`. Introduce `Z`.

Take `⟨t₁, h₁I, -, h₁d⟩` from `(GlobalTheory.FlatTwisting.twSec_of_flat _ H Dw l Xo c r U (xiR D) (badPrimes H l) hK hU hpq hB).2 hflat Z w (GlobalTheory.FlatLine.hasPts U hpq hg hU Z)`. Take `⟨t₂, h₂I, h₂d⟩` from `hroot Z`. Establish `hmp` using `GlobalTheory.FlatTw.twSec_mul_pow _ H Dw l Xo c r U (xiR D) Z`. Take `⟨t₃, h₃lo, h₃d⟩` from `hmp.2 _ t₂ m`. Take `⟨t₄, -, -, h₄lo, h₄d⟩` from `hmp.1 _ _ t₁ t₃`.

Take `⟨t, htlo, htd⟩` from `twSec_congr hW t₄`. Use `⟨t, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[htlo, h₄lo, h₃lo]`. Conclude with `h₁I.add (intOff_nsmul h₂I m)`. Rewrite using `[htd, h₄d, h₃d]`.

Establish `hm : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`. Use `mul_le_mul_of_nonneg_left h₂d hm` as an intermediate fact. Rewrite using `[hb]`. Use the polynomial consequences of the given equalities and inequalities. Use `choose s hsI hsd using hsec`.

Establish `hBp : ∀ p ∈ badPrimes H l, p.Prime` using `fun p hp => badPrimes_prime p hp`. Establish `hadd : ∀ (u : GlobalTheory.AllWt.Weight Dw) (n : ℤ), wtOf Dw u n + wtOf Dw (parWt Dw w) m = wtOf Dw (u + parWt Dw w) (n + m)` using `fun u n => (wtOf_add u (parWt Dw w) n m).symm`. Use `⟨fun Z => ⟨s Z, hsI Z, hsd Z⟩, fun u n => ⟨fun Z hZ => ?_, fun hW' => ?_⟩⟩` and prove the remaining obligations. Take `⟨hgood, hrank⟩` from `GlobalTheory.FlatTw.Good.twist_goodOn _ H Dw l Xo c r U (xiR D) D V dict Z _ (s Z) (wtOf Dw u n) hU (even_wtOf u n) hZ`. Establish `hdeg` using `GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le _ H Dw l Xo c r U (xiR D) D V dict Z _ (s Z) (wtOf Dw u n) (badPrimes H l) hU (even_wtOf u n) hBp (hsI Z) hZ`.

Rewrite `hgood`, `hrank`, `hdeg` using `[hadd]`. Use `⟨hgood, hrank, ?_⟩` and prove the remaining obligations. Establish `hr : (0 : ℝ) ≤ (rankOn U Z (wtOf Dw u n) : ℝ)` using `Nat.cast_nonneg _`. Use `mul_le_mul_of_nonneg_left (sub_le_sub_right (hsd Z) (logSum (badPrimes H l))) hr` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨hgood, hrank, hdeg⟩` from `GlobalTheory.Proof.TwistedWeightDegree.degW_twist D H Dw l Xo c r U V dict hC _ (wtOf Dw u n) s (badPrimes H l) b (even_wtOf u n) hBp hsI hsd hW'`. Rewrite `hgood`, `hrank`, `hdeg` using `[hadd]`. Conclude with `⟨hgood, hrank, hdeg⟩`.
-/
theorem flat_root_twist : GlobalTheory.Published.AbelianDeRham → ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → FnAlgClosed Xo c → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → FlatExists U (xiR D) → UnramPts Xo c (badPrimes H l) → ∀ (w : Psi H → ℤ) (m : ℕ), (∀ Z : Comp Xo c, ∃ t : TwSec U (xiR D) Z (wtOf Dw (parWt Dw w) m), IntOff (badPrimes H l) t.lo ∧ (∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) ≤ t.degLo) ∧ ∀ (u : GlobalTheory.AllWt.Weight Dw) (n : ℤ), (∀ Z : Comp Xo c, GoodOn U (xiR D) V dict Z (wtOf Dw u n) → GoodOn U (xiR D) V dict Z (wtOf Dw (u + parWt Dw w) (n + m)) ∧ rankOn U Z (wtOf Dw (u + parWt Dw w) (n + m)) = rankOn U Z (wtOf Dw u n) ∧ degOn U (xiR D) V dict Z (wtOf Dw u n) + (rankOn U Z (wtOf Dw u n) : ℝ) * ((∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) - logSum (badPrimes H l)) ≤ degOn U (xiR D) V dict Z (wtOf Dw (u + parWt Dw w) (n + m))) ∧ (GoodW U (xiR D) V dict (wtOf Dw u n) → GoodW U (xiR D) V dict (wtOf Dw (u + parWt Dw w) (n + m)) ∧ rankW U (wtOf Dw (u + parWt Dw w) (n + m)) = rankW U (wtOf Dw u n) ∧ degW U (xiR D) V dict (wtOf Dw u n) + (rankW U (wtOf Dw u n) : ℝ) * ((∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) - logSum (badPrimes H l)) ≤ degW U (xiR D) V dict (wtOf Dw (u + parWt Dw w) (n + m))) := by
  intro _ D H Dw l Xo c r U V dict hC hF hpq hg hflat hB w m
  have hU : ∀ σ, GoodEmb c σ → IsUnf (U σ) := fun σ hσ => (hC.2 σ hσ).1
  have hξ : ∀ σ, GoodEmb c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D :=
    fun σ hσ => (hC.2 σ hσ).2.2.2
  obtain ⟨hK, hroot⟩ :=
    GlobalTheory.KeyRootTw.exists_twSec_keyRoot _ H Dw l Xo c r U (xiR D) hU hξ hF hpq hg hB

  set b : ℝ := (∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) -
    (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) *
      (Real.log (2 * Real.pi) / 2 + lrd D.host.E) with hb

  have hW : wtOf Dw (parWt Dw w) 0 + m • wtOf Dw 0 1 = wtOf Dw (parWt Dw w) m := by
    rw [GlobalTheory.CompHt.nsmul_wtOf, ← wtOf_add]
    simp
  have hsec : ∀ Z : Comp Xo c, ∃ t : TwSec U (xiR D) Z (wtOf Dw (parWt Dw w) m),
      IntOff (badPrimes H l) t.lo ∧ b ≤ t.degLo := by
    intro Z
    obtain ⟨t₁, h₁I, -, h₁d⟩ :=
      (GlobalTheory.FlatTwisting.twSec_of_flat _ H Dw l Xo c r U (xiR D) (badPrimes H l) hK hU hpq hB).2 hflat Z w
        (GlobalTheory.FlatLine.hasPts U hpq hg hU Z)
    obtain ⟨t₂, h₂I, h₂d⟩ := hroot Z
    have hmp := GlobalTheory.FlatTw.twSec_mul_pow _ H Dw l Xo c r U (xiR D) Z
    obtain ⟨t₃, h₃lo, h₃d⟩ := hmp.2 _ t₂ m
    obtain ⟨t₄, -, -, h₄lo, h₄d⟩ := hmp.1 _ _ t₁ t₃
    obtain ⟨t, htlo, htd⟩ := twSec_congr hW t₄
    refine ⟨t, ?_, ?_⟩
    · rw [htlo, h₄lo, h₃lo]
      exact h₁I.add (intOff_nsmul h₂I m)
    · rw [htd, h₄d, h₃d]
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have := mul_le_mul_of_nonneg_left h₂d hm
      rw [hb]
      nlinarith
  choose s hsI hsd using hsec
  have hBp : ∀ p ∈ badPrimes H l, p.Prime := fun p hp => badPrimes_prime p hp
  have hadd : ∀ (u : GlobalTheory.AllWt.Weight Dw) (n : ℤ),
      wtOf Dw u n + wtOf Dw (parWt Dw w) m = wtOf Dw (u + parWt Dw w) (n + m) :=
    fun u n => (wtOf_add u (parWt Dw w) n m).symm
  refine ⟨fun Z => ⟨s Z, hsI Z, hsd Z⟩, fun u n => ⟨fun Z hZ => ?_, fun hW' => ?_⟩⟩
  · obtain ⟨hgood, hrank⟩ := GlobalTheory.FlatTw.Good.twist_goodOn _ H Dw l Xo c r U (xiR D) D V dict Z _ (s Z)
      (wtOf Dw u n) hU (even_wtOf u n) hZ
    have hdeg := GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le _ H Dw l Xo c r U (xiR D) D V dict Z _ (s Z)
      (wtOf Dw u n) (badPrimes H l) hU (even_wtOf u n) hBp (hsI Z) hZ
    rw [hadd] at hgood hrank hdeg
    refine ⟨hgood, hrank, ?_⟩
    have hr : (0 : ℝ) ≤ (rankOn U Z (wtOf Dw u n) : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left (sub_le_sub_right (hsd Z) (logSum (badPrimes H l))) hr
    linarith
  · obtain ⟨hgood, hrank, hdeg⟩ := GlobalTheory.Proof.TwistedWeightDegree.degW_twist D H Dw l Xo c r U V dict hC _ (wtOf Dw u n) s
      (badPrimes H l) b (even_wtOf u n) hBp hsI hsd hW'
    rw [hadd] at hgood hrank hdeg
    exact ⟨hgood, hrank, hdeg⟩

end GlobalTheory.FlatRootTwist
