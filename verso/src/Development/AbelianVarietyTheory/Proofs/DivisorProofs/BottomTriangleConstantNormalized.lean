import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomTriplePeriodConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomTriplePeriodConstDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantTripleCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleRootOfUnityTwistStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hQ : ζ ∈ Qbar`. Establish `: IsIntegral ℚ ζ` using `IsIntegral.of_pow hn (h ▸ isIntegral_one)`. Conclude with `mem_algebraicClosure_iff.2 this.isAlgebraic`. Use `⟨fun e => by simp [e, hn.ne'] at h, hQ, fun p _ lam => ?_⟩` and prove the remaining obligations. Establish `h2 : (⟨ζ, hQ⟩ : Qbar) ^ n = 1` using `Subtype.ext (by simpa using h)`.

Establish `h3 : lamC lam ζ = lam ⟨ζ, hQ⟩` using `by simp [lamC, hQ]`. Establish `h4 : ‖lam ⟨ζ, hQ⟩‖ ^ n = 1` using `by rw [← norm_pow, ← map_pow, h2, map_one, norm_one]`. Rewrite using `[h3]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h4`.
-/
theorem GlobalTheory.BotFormula.root_unit {ζ : ℂ} {n : ℕ} (hn : 0 < n) (h : ζ ^ n = 1) :
    ζ ≠ 0 ∧ ζ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam ζ‖ = 1 := by
  have hQ : ζ ∈ Qbar := by
    have : IsIntegral ℚ ζ := IsIntegral.of_pow hn (h ▸ isIntegral_one)
    exact mem_algebraicClosure_iff.2 this.isAlgebraic
  refine ⟨fun e => by simp [e, hn.ne'] at h, hQ, fun p _ lam => ?_⟩
  have h2 : (⟨ζ, hQ⟩ : Qbar) ^ n = 1 := Subtype.ext (by simpa using h)
  have h3 : lamC lam ζ = lam ⟨ζ, hQ⟩ := by simp [lamC, hQ]
  have h4 : ‖lam ⟨ζ, hQ⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h2, map_one, norm_one]
  rw [h3]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h4

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `hPr hK hM hI hB`. Take `⟨cA, hA⟩` from `GlobalTheory.T.exists_bottom_triple_period_const hPr hK hM hI hB`. Take `⟨cB, hB'⟩` from `GlobalTheory.T.exists_bottom_triple_period_const_dual hPr hK hM hI hB`. Take `⟨cC, hC⟩` from `GlobalTheory.T.exists_constant_triple_coefficient hPr.minguezThetaGL hPr hK hM hI hB`. Take `⟨cD, hD⟩` from `GlobalTheory.T.bottom_triangle_root_of_unity_twist hPr`.

Use `⟨max (max (max cA cB) cC) cD, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Simplify using `only [max_le_iff] at hCF`. Take `⟨CA, xA, hA⟩` from `hA ε CF hCF.1.1.1`. Take `⟨CB, xB, hB'⟩` from `hB' ε CF hCF.1.1.2`. Take `⟨CC, xC, hC⟩` from `hC ε CF hCF.1.2`.

Take `⟨CD, xD, hD⟩` from `hD ε CF hCF.2`. Use `⟨max (max (max CA CB) CC) CD, max (max (max xA xB) xC) xD, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩` and prove the remaining obligations. Simplify using `only [max_le_iff] at hC0 hx`. Establish `hA` using `hA C hC0.1.1.1 D large₂ he hx.1.1.1 hR T Lc μ₀ hL G`. Establish `hB'` using `hB' C hC0.1.1.2 D large₂ he hx.1.1.2 hR T Lc μ₀ hL G`.

Establish `hC` using `hC C hC0.1.2 D large₂ he hx.1.2 hR T Lc μ₀ hL G`. Establish `hD` using `hD C hC0.2 D large₂ he hx.2 hR T Lc μ₀ hL G`. Introduce `W S hψ _ i j A A' WW X₀ c0 δ t0 hX₀ hc₀`. Take `⟨X, ζ, hX, hβ, hζ, hc⟩` from `hD W hψ i j A A' WW X₀ c0 hX₀ hc₀`. Take `⟨Ω, hΩ, HA⟩` from `hA W hψ i j A A' WW X δ t0 hX hβ`.

Take `⟨Ω', hΩ', HB⟩` from `hB' W hψ i j A A' WW X δ t0 hX hβ`. Take `⟨κ₀, hκ₀, HC⟩` from `hC W hψ i j A A' WW X _ hX hc`. Use `⟨Ω * κ₀ * Ω', mul_ne_zero (mul_ne_zero hΩ hκ₀) hΩ', fun s Q P P' hP => ?_⟩` and prove the remaining obligations. Take `⟨uA, huA, huAQ, huAu, HA⟩` from `HA s Q P P' hP`. Take `⟨uB, huB, huBQ, huBu, HB⟩` from `HB s Q P P' hP`.

Take `⟨n, hn, hζn⟩` from `hζ s`. Take `⟨hz0, hzQ, hzu⟩` from `GlobalTheory.BotFormula.root_unit hn hζn`. Establish `ea : P.a = A.rank` using `hP.rank.1.trans hX.rank.symm`. Establish `ea' : P'.a = A'.rank` using `hP.rank.2.1.trans hX.rank'.symm`. Establish `ed : P.d = WW.rank` using `by rw [hP.rank.2.2.1, ← hX.is.rank, hX.rank, hX.rank']`.

Establish `ed' : P'.d = WW.rank` using `hP.rank.2.2.2.trans ed`. Take `⟨M, M', hMM, HC⟩` from `HC s Q δ t0 P P' hP ea ea' ed ed'`. Use `⟨uA * uB * ζ s, M, M', mul_ne_zero (mul_ne_zero huA huB) hz0, Qbar.mul_mem (Qbar.mul_mem huAQ huBQ) hzQ, fun p _ hp lam => ?_, fun hd h => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.BotFormula.lamC_mul lam (Qbar.mul_mem huAQ huBQ) hzQ, GlobalTheory.BotFormula.lamC_mul lam huAQ huBQ, norm_mul, norm_mul, huAu p hp lam, huBu p hp lam, hzu p lam, one_mul, one_mul]`. Take `⟨g, hg⟩` from `GlobalTheory.T.exists_finiteAdelicPoint_unitaryGroup_gramOne WW hX.stdW.1 h ed.symm`.

Establish `hg'` using `hg.cast hd`. Establish `key : ∀ T, starRingEnd ℂ (P.coord h T) = Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * ∑ T', (M T T' : ℂ) * P'.coord (hd ▸ h) T'`. Introduce `T`. Rewrite using `[HA ea ed h g hg T, HC g T]`. Simplify using `only [Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun T' _ => ?_` and prove the remaining obligations. Rewrite using `[HB ea' ed' (hd ▸ h) g hg' T']`. Expand and normalize the polynomial expressions, which then agree. Use `⟨key, fun T' => ?_⟩` and prove the remaining obligations. Repeatedly rewrite using `[key, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Establish `e1 : ∀ T'' T, (M' T' T : ℂ) * (Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * ((M T T'' : ℂ) * P'.coord (hd ▸ h) T'')) = ((M' T' T * M T T'' : ℤ) : ℂ) * (Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * P'.coord (hd ▸ h) T'')`. Introduce `T'' T`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[e1, ← Finset.sum_mul, ← Int.cast_sum, hMM]`. Simplify using `[mul_comm]`.
-/
theorem GlobalTheory.BotFormula.bottom_formula : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ) (δ t0 : ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ (u : ℂ) (M : Tup D P.a P.d P.n → Tup D P'.a P'.d P'.n → ℤ) (M' : Tup D P'.a P'.d P'.n → Tup D P.a P.d P.n → ℤ),
          u ≠ 0 ∧ u ∈ Qbar ∧
          (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (hd : P'.d = P.d) (h : GA D P.d),
            (∀ T, starRingEnd ℂ (P.coord h T) = κ * u * c0 s * ∑ T', (M T T' : ℂ) * P'.coord (hd ▸ h) T') ∧
            ∀ T', P'.coord (hd ▸ h) T' * (κ * u * c0 s) = ∑ T, (M' T' T : ℂ) * starRingEnd ℂ (P.coord h T) := by
  intro hPr hK hM hI hB
  obtain ⟨cA, hA⟩ := GlobalTheory.T.exists_bottom_triple_period_const hPr hK hM hI hB
  obtain ⟨cB, hB'⟩ := GlobalTheory.T.exists_bottom_triple_period_const_dual hPr hK hM hI hB
  obtain ⟨cC, hC⟩ := GlobalTheory.T.exists_constant_triple_coefficient hPr.minguezThetaGL hPr hK hM hI hB
  obtain ⟨cD, hD⟩ := GlobalTheory.T.bottom_triangle_root_of_unity_twist hPr
  refine ⟨max (max (max cA cB) cC) cD, fun ε CF hCF => ?_⟩
  simp only [max_le_iff] at hCF
  obtain ⟨CA, xA, hA⟩ := hA ε CF hCF.1.1.1
  obtain ⟨CB, xB, hB'⟩ := hB' ε CF hCF.1.1.2
  obtain ⟨CC, xC, hC⟩ := hC ε CF hCF.1.2
  obtain ⟨CD, xD, hD⟩ := hD ε CF hCF.2
  refine ⟨max (max (max CA CB) CC) CD, max (max (max xA xB) xC) xD, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  simp only [max_le_iff] at hC0 hx
  have hA := hA C hC0.1.1.1 D large₂ he hx.1.1.1 hR T Lc μ₀ hL G
  have hB' := hB' C hC0.1.1.2 D large₂ he hx.1.1.2 hR T Lc μ₀ hL G
  have hC := hC C hC0.1.2 D large₂ he hx.1.2 hR T Lc μ₀ hL G
  have hD := hD C hC0.2 D large₂ he hx.2 hR T Lc μ₀ hL G
  intro W S hψ _ i j A A' WW X₀ c0 δ t0 hX₀ hc₀
  obtain ⟨X, ζ, hX, hβ, hζ, hc⟩ := hD W hψ i j A A' WW X₀ c0 hX₀ hc₀
  obtain ⟨Ω, hΩ, HA⟩ := hA W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω', hΩ', HB⟩ := hB' W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨κ₀, hκ₀, HC⟩ := hC W hψ i j A A' WW X _ hX hc
  refine ⟨Ω * κ₀ * Ω', mul_ne_zero (mul_ne_zero hΩ hκ₀) hΩ', fun s Q P P' hP => ?_⟩
  obtain ⟨uA, huA, huAQ, huAu, HA⟩ := HA s Q P P' hP
  obtain ⟨uB, huB, huBQ, huBu, HB⟩ := HB s Q P P' hP
  obtain ⟨n, hn, hζn⟩ := hζ s
  obtain ⟨hz0, hzQ, hzu⟩ := GlobalTheory.BotFormula.root_unit hn hζn
  have ea : P.a = A.rank := hP.rank.1.trans hX.rank.symm
  have ea' : P'.a = A'.rank := hP.rank.2.1.trans hX.rank'.symm
  have ed : P.d = WW.rank := by rw [hP.rank.2.2.1, ← hX.is.rank, hX.rank, hX.rank']
  have ed' : P'.d = WW.rank := hP.rank.2.2.2.trans ed
  obtain ⟨M, M', hMM, HC⟩ := HC s Q δ t0 P P' hP ea ea' ed ed'
  refine ⟨uA * uB * ζ s, M, M', mul_ne_zero (mul_ne_zero huA huB) hz0, Qbar.mul_mem (Qbar.mul_mem huAQ huBQ) hzQ, fun p _ hp lam => ?_, fun hd h => ?_⟩
  · rw [GlobalTheory.BotFormula.lamC_mul lam (Qbar.mul_mem huAQ huBQ) hzQ, GlobalTheory.BotFormula.lamC_mul lam huAQ huBQ, norm_mul, norm_mul,
      huAu p hp lam, huBu p hp lam, hzu p lam, one_mul, one_mul]
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_finiteAdelicPoint_unitaryGroup_gramOne WW hX.stdW.1 h ed.symm
  have hg' := hg.cast hd
  have key : ∀ T, starRingEnd ℂ (P.coord h T) =
      Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * ∑ T', (M T T' : ℂ) * P'.coord (hd ▸ h) T' := by
    intro T
    rw [HA ea ed h g hg T, HC g T]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T' _ => ?_
    rw [HB ea' ed' (hd ▸ h) g hg' T']
    ring
  refine ⟨key, fun T' => ?_⟩
  simp_rw [key, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e1 : ∀ T'' T, (M' T' T : ℂ) * (Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * ((M T T'' : ℂ) * P'.coord (hd ▸ h) T'')) =
      ((M' T' T * M T T'' : ℤ) : ℂ) * (Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * P'.coord (hd ▸ h) T'') := by
    intro T'' T; push_cast; ring
  simp_rw [e1, ← Finset.sum_mul, ← Int.cast_sum, hMM]
  simp [mul_comm]
