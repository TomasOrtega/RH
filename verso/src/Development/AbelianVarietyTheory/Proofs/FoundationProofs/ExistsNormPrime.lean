import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.EndInt
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PhNorm
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.ShiftAnalyticW
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormLeOneOfQuad
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.CurveFormalFirstLevelHolds
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.CMUnit

open Formalism.MainNotions.GL3Theta

/- English proof (translation)
Take `⟨hcurve, -, hδ12, hLam, hOk⟩` from `hA`. Establish `hcc : cc ≠ ⊥` using `hcurve.1`. Establish `hδ : δ ≠ 0` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcurve δ hδ12`. Take `⟨⟨L, hL⟩, -⟩` from `Formalism.L2.Th1.F2.lamOfLat D cc δ hcc hδ`. Establish `hLg : g.abelian₂ = L.lattice.toAddSubgroup` using `hLam.trans hL.symm`.

Take `⟨hg2, hg3⟩` from `Formalism.L2.KerInert.Sigma.invAlg' D cc δ hcurve hδ12 L hL`. Use `set a2 : Qbar := ⟨L.g₂, hg2⟩ with ha2`. Use `set a3 : Qbar := ⟨L.g₃, hg3⟩ with ha3`. Take `⟨e2, e3⟩` from `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)`. Establish `hcmby` using `Formalism.L2.KerInert.Sigma.ChartWirtingerDerivatives.hasCMBy_curve D cc δ hcurve hδ12 L hL`.

Take `⟨ι, hι⟩` from `Formalism.L2.KerInert.lamExt p g.lam`. Establish `hιg2 : ι L.g₂ = g.lam a2` using `hι a2`. Establish `hιg3 : ι L.g₃ = g.lam a3` using `hι a3`. Establish `hwm : wModel g.lam g.abelian₂ = Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃)`. Establish `e4 : lamC g.lam (-(g2 g.abelian₂) / 4) = -(g.lam a2) / 4`.

Establish `: -(g2 g.abelian₂) / 4 = ((-a2 / 4 : Qbar) : ℂ)` using `by rw [e2]; push_cast; rfl`. Rewrite using `[this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]`. Establish `e6 : lamC g.lam (-(g3 g.abelian₂) / 4) = -(g.lam a3) / 4`. Establish `: -(g3 g.abelian₂) / 4 = ((-a3 / 4 : Qbar) : ℂ)` using `by rw [e3]; push_cast; rfl`. Rewrite using `[this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]`.

Rewrite using `[hιg2, hιg3]`. Apply the tactic sequence `ext <;> simp [wModel, Formalism.L2.Th1.A.shortW, e4, e6]`. Use `set W0 : WeierstrassCurve ℂ_[p] := Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) with hW0`. Establish `hgW : g.W = g.C • W0` using `by rw [G1.W, hwm]`. Take `⟨i1, i2, i3, i4, i6, hΔ⟩` from `hOk.1`.

Establish `hWint : Formalism.L2.Th1.E.IntCurve g.W` using `⟨i1, i2, i3, i4, i6, hΔ⟩`. Establish `hW0'` using `Formalism.L2.KerInert.Sigma.wModel_g g.lam g.abelian₂ a2 a3 e2 e3`. Rewrite `hW0'` using `[hwm]`. Take `⟨c2, c3⟩` from `Formalism.L2.KerInert.PN.g_change' W0 g.C`. Rewrite `c2` using `[← hgW, hW0'.1]`.

Rewrite `c3` using `[← hgW, hW0'.2]`. Use `set uu : ℂ_[p] := ((g.C.u : ℂ_[p]ˣ) : ℂ_[p]) with huu`. Establish `hc : ι.symm uu ≠ 0`. Introduce `h`. Conclude with `Units.ne_zero g.C.u (by rw [← huu, ← ι.apply_symm_apply uu, h, map_zero])`.

Establish `hιc : ι (ι.symm uu) = uu` using `ι.apply_symm_apply uu`. Establish `hH` using `Formalism.L2.Th1.F.homogeneity L (ι.symm uu) hc`. Establish `hU' : Formalism.L2.Th1.E.Unif p (Formalism.L2.Th1.F.scalePair L (ι.symm uu) hc) ι g.W`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[c2, hH.2.2.2.2.2.2.2.2.2.1, map_mul, map_inv₀, map_pow, hιc, ← hιg2, Units.val_inv_eq_inv_val, inv_pow]`.

Rewrite using `[c3, hH.2.2.2.2.2.2.2.2.2.2, map_mul, map_inv₀, map_pow, hιc, ← hιg3, Units.val_inv_eq_inv_val, inv_pow]`. Establish `hcm' : Formalism.L2.Th1.CM.HasCMBy D.host.d (Formalism.L2.Th1.F.scalePair L (ι.symm uu) hc)` using `Formalism.L2.Th1.F.hasCMByScale _ L _ hc hcmby`. Conclude with `⟨ι, _, hι, hcm', hU', hWint⟩`.
-/
theorem unif_setup (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p)
    (hA : At D cc δ g) :
    ∃ (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair), Formalism.L2.KerInert.IotaExt g.lam ι ∧
      Formalism.L2.Th1.CM.HasCMBy D.host.d L ∧ Formalism.L2.Th1.E.Unif p L ι g.W ∧ Formalism.L2.Th1.E.IntCurve g.W := by
  obtain ⟨hcurve, -, hδ12, hLam, hOk⟩ := hA
  have hcc : cc ≠ ⊥ := hcurve.1
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcurve δ hδ12
  obtain ⟨⟨L, hL⟩, -⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc hδ
  have hLg : g.abelian₂ = L.lattice.toAddSubgroup := hLam.trans hL.symm
  obtain ⟨hg2, hg3⟩ := Formalism.L2.KerInert.Sigma.invAlg' D cc δ hcurve hδ12 L hL
  set a2 : Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Qbar := ⟨L.g₃, hg3⟩ with ha3
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L
    (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)
  have hcmby := Formalism.L2.KerInert.Sigma.ChartWirtingerDerivatives.hasCMBy_curve D cc δ hcurve hδ12 L hL
  obtain ⟨ι, hι⟩ := Formalism.L2.KerInert.lamExt p g.lam
  have hιg2 : ι L.g₂ = g.lam a2 := hι a2
  have hιg3 : ι L.g₃ = g.lam a3 := hι a3
  have hwm : wModel g.lam g.abelian₂ = Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) := by
    have e4 : lamC g.lam (-(g2 g.abelian₂) / 4) = -(g.lam a2) / 4 := by
      have : -(g2 g.abelian₂) / 4 = ((-a2 / 4 : Qbar) : ℂ) := by rw [e2]; push_cast; rfl
      rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]
    have e6 : lamC g.lam (-(g3 g.abelian₂) / 4) = -(g.lam a3) / 4 := by
      have : -(g3 g.abelian₂) / 4 = ((-a3 / 4 : Qbar) : ℂ) := by rw [e3]; push_cast; rfl
      rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]
    rw [hιg2, hιg3]
    ext <;> simp [wModel, Formalism.L2.Th1.A.shortW, e4, e6]
  set W0 : WeierstrassCurve ℂ_[p] := Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) with hW0
  have hgW : g.W = g.C • W0 := by rw [G1.W, hwm]
  obtain ⟨i1, i2, i3, i4, i6, hΔ⟩ := hOk.1
  have hWint : Formalism.L2.Th1.E.IntCurve g.W := ⟨i1, i2, i3, i4, i6, hΔ⟩
  have hW0' := Formalism.L2.KerInert.Sigma.wModel_g g.lam g.abelian₂ a2 a3 e2 e3
  rw [hwm] at hW0'
  obtain ⟨c2, c3⟩ := Formalism.L2.KerInert.PN.g_change' W0 g.C
  rw [← hgW, hW0'.1] at c2
  rw [← hgW, hW0'.2] at c3
  set uu : ℂ_[p] := ((g.C.u : ℂ_[p]ˣ) : ℂ_[p]) with huu
  have hc : ι.symm uu ≠ 0 := by
    intro h
    exact Units.ne_zero g.C.u (by rw [← huu, ← ι.apply_symm_apply uu, h, map_zero])
  have hιc : ι (ι.symm uu) = uu := ι.apply_symm_apply uu
  have hH := Formalism.L2.Th1.F.homogeneity L (ι.symm uu) hc
  have hU' : Formalism.L2.Th1.E.Unif p (Formalism.L2.Th1.F.scalePair L (ι.symm uu) hc) ι g.W := by
    refine ⟨?_, ?_⟩
    · rw [c2, hH.2.2.2.2.2.2.2.2.2.1, map_mul, map_inv₀, map_pow, hιc, ← hιg2, Units.val_inv_eq_inv_val, inv_pow]
    · rw [c3, hH.2.2.2.2.2.2.2.2.2.2, map_mul, map_inv₀, map_pow, hιc, ← hιg3, Units.val_inv_eq_inv_val, inv_pow]
  have hcm' : Formalism.L2.Th1.CM.HasCMBy D.host.d (Formalism.L2.Th1.F.scalePair L (ι.symm uu) hc) :=
    Formalism.L2.Th1.F.hasCMByScale _ L _ hc hcmby
  exact ⟨ι, _, hι, hcm', hU', hWint⟩

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h0` using `h 0`. Establish `h1` using `h 1`. Establish `e : Formalism.L2.Th1.D.normInt dK 1 1 - Formalism.L2.Th1.D.normInt dK 0 1 = 2`.

Unfold `Formalism.L2.Th1.D.normInt`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (p : ℤ) ∣ 2` using `by rw [← e]; exact dvd_sub h1 h0`. Establish `h2' : p ∣ 2` using `by exact_mod_cast h2`. Conclude with `hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2')`.
-/
theorem exists_norm_prime (dK : ℕ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ m : ℤ, ¬ (p : ℤ) ∣ Formalism.L2.Th1.D.normInt dK m 1 := by
  by_contra h
  push_neg at h
  have h0 := h 0
  have h1 := h 1
  have e : Formalism.L2.Th1.D.normInt dK 1 1 - Formalism.L2.Th1.D.normInt dK 0 1 = 2 := by
    unfold Formalism.L2.Th1.D.normInt; ring
  have h2 : (p : ℤ) ∣ 2 := by rw [← e]; exact dvd_sub h1 h0
  have h2' : p ∣ 2 := by exact_mod_cast h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2')

/- English proof (translation)
Establish `hN0 : Formalism.L2.Th1.D.normInt dK m n ≠ 0` using `fun h => hN (by rw [h]; exact dvd_zero _)`. Use `set b : ℂ := (m : ℂ) + (n : ℂ) * Formalism.L2.Th1.CM.omegaK dK with hb`. Use `set bb : ℂ := (m : ℂ) + (n : ℂ) * (1 - Formalism.L2.Th1.CM.omegaK dK) with hbb`. Establish `hprodC : b * bb = ((Formalism.L2.Th1.D.normInt dK m n : ℤ) : ℂ)` using `Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.prod_bar hmod m n`. Establish `hb0 : b ≠ 0`.

Introduce `h`. Apply `hN0` to reduce the goal to its premises. Establish `h'` using `hprodC`. Rewrite `h'` using `[h, zero_mul]`. Conclude with `h'.symm` after adjusting the coercions.

Establish `hst : Formalism.L2.Th1.F.MulStable L b` using `(Formalism.L2.Th1.F.hasCMByStable dK L hCM m n).1`. Establish `hstb : Formalism.L2.Th1.F.MulStable L bb`. Establish `h` using `(Formalism.L2.Th1.F.hasCMByStable dK L hCM (m + n) (-n)).1`. Establish `e : (((m + n : ℤ) : ℂ) + ((-n : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK) = bb`. Rewrite using `[hbb]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Take `⟨S, hS⟩` from `Formalism.L2.Th1.F.kerRepsExist L b hb0 hst`. Use `set t : ℂ := L.ω₁ / 2 with ht`.

Establish `ht0 : t ∉ L.lattice` using `L.ω₁_div_two_notMem_lattice`. Establish `ht2 : 2 * t ∈ L.lattice`. Rewrite using `[ht, mul_div_cancel₀ _ two_ne_zero]`. Conclude with `L.ω₁_mem_lattice`. Use `set Q : ℂ := t / b with hQ`.

Establish `hbQ : b * Q = t` using `by rw [hQ, mul_div_cancel₀ _ hb0]`. Establish `hiso` using `Formalism.L2.Th1.F.isogenyP L b S hb0 hst hS Q (by rw [hbQ]; exact ht0)`. Rewrite `hiso` using `[hbQ]`. Use `set M : ℕ := 2 * (Formalism.L2.Th1.D.normInt dK m n).natAbs with hM`. Establish `hpM : ¬ p ∣ M`.

Introduce `h`. Break down `(Nat.Prime.dvd_mul Fact.out).1 h with h2 | h2` into its components or cases. Conclude with `hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2)`. Conclude with `hN (Int.natCast_dvd.2 h2)`. Establish `hMR : ∀ R : ℂ, (2 * (b * bb)) * R ∈ L.lattice → (M : ℂ) * R ∈ L.lattice`.

Introduce `R hR`. Rewrite `hR` using `[hprodC]`. Break down `Int.natAbs_eq (Formalism.L2.Th1.D.normInt dK m n) with e | e` into its components or cases. Establish `hc : ((Formalism.L2.Th1.D.normInt dK m n : ℤ) : ℂ) = ((Formalism.L2.Th1.D.normInt dK m n).natAbs : ℂ)`. Rewrite using `[← Int.cast_natCast, ← e]`.

Rewrite `hR` using `[hc]`. Establish `e2 : (M : ℂ) = 2 * ((Formalism.L2.Th1.D.normInt dK m n).natAbs : ℂ)` using `by rw [hM]; push_cast; ring`. Rewrite using `[e2]`. Conclude with `hR`. Establish `hc : ((Formalism.L2.Th1.D.normInt dK m n : ℤ) : ℂ) = -((Formalism.L2.Th1.D.normInt dK m n).natAbs : ℂ)`.

Rewrite using `[← Int.cast_natCast, ← Int.cast_neg, ← e]`. Rewrite `hR` using `[hc]`. Establish `e2 : (M : ℂ) * R = -(2 * -((Formalism.L2.Th1.D.normInt dK m n).natAbs : ℂ) * R)` using `by rw [hM]; push_cast; ring`. Rewrite using `[e2]`. Conclude with `neg_mem hR`.

Establish `intR : ∀ R : ℂ, R ∉ L.lattice → (2 * (b * bb)) * R ∈ L.lattice → ι (L.weierstrassP R) - W.b₂ / 12 ∈ Formalism.G.unitBall ℂ_[p]`. Introduce `R hR h`. Establish `h1` using `(Formalism.L2.Th1.E.TransW.ptW_int Formalism.L2.Th1.E.ptWAdd Formalism.L2.Th1.E.ptWZero hU hW R M hpM (hMR R h) hR).1`. Rewrite `h1` using `[Formalism.L2.Th1.E.AnaSysW.px_ptW hU R hR]`. Conclude with `h1`.

Establish `mt : (2 * (b * bb)) * t ∈ L.lattice`. Establish `e : (2 * (b * bb)) * t = b * (bb * (2 * t))` using `by ring`. Rewrite using `[e]`. Conclude with `hst _ (hstb _ ht2)`. Establish `mQ : (2 * (b * bb)) * Q ∈ L.lattice`.

Establish `e : (2 * (b * bb)) * Q = bb * (2 * (b * Q))` using `by ring`. Rewrite using `[e, hbQ]`. Conclude with `hstb _ ht2`. Establish `mP : ∀ P ∈ S, (2 * (b * bb)) * P ∈ L.lattice`. Introduce `P hP`.

Establish `h` using `(hS.1 P hP).1`. Establish `e : (2 * (b * bb)) * P = bb * (b * P) + bb * (b * P)` using `by ring`. Rewrite using `[e]`. Conclude with `add_mem (hstb _ h) (hstb _ h)`. Establish `nQ : Q ∉ L.lattice`.

Introduce `h`. Apply `ht0` to reduce the goal to its premises. Rewrite using `[← hbQ]`. Conclude with `hst _ h`. Establish `nQP : ∀ P ∈ S, Q + P ∉ L.lattice`.

Introduce `P hP h`. Apply `ht0` to reduce the goal to its premises. Establish `e : t = b * (Q + P) - b * P` using `by rw [← hbQ]; ring`. Rewrite using `[e]`. Conclude with `sub_mem (hst _ h) (hS.1 P hP).1`.

Establish `iT` using `intR t ht0 mt`. Establish `iQ` using `intR Q nQ mQ`. Establish `iP : ∀ P ∈ S, ι (L.weierstrassP P) - W.b₂ / 12 ∈ Formalism.G.unitBall ℂ_[p]` using `fun P hP => intR P (hS.1 P hP).2 (mP P hP)`. Establish `iQP : ∀ P ∈ S, ι (L.weierstrassP (Q + P)) - W.b₂ / 12 ∈ Formalism.G.unitBall ℂ_[p]`. Introduce `P hP`.

Use `intR (Q + P) (nQP P hP) ?_` and prove the remaining obligations. Rewrite using `[mul_add]`. Conclude with `add_mem mQ (mP P hP)`. Establish `hbI : ι b ∈ Formalism.G.unitBall ℂ_[p]`. Establish `hs : ι b + ι bb = ((2 * m + n : ℤ) : ℂ_[p])`.

Rewrite using `[← map_add, hb, hbb]`. Establish `e : ((m : ℂ) + (n : ℂ) * Formalism.L2.Th1.CM.omegaK dK) + ((m : ℂ) + (n : ℂ) * (1 - Formalism.L2.Th1.CM.omegaK dK)) = ((2 * m + n : ℤ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e, map_intCast]`. Establish `hp : ι b * ι bb = ((Formalism.L2.Th1.D.normInt dK m n : ℤ) : ℂ_[p])`. Rewrite using `[← map_mul, hprodC, map_intCast]`.

Conclude with `Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.norm_le_one_of_quad hs hp (IsUltrametricDist.norm_intCast_le_one ℂ_[p] _)`. Establish `hi` using `congrArg ι hiso`. Simplify using `only [map_mul, map_pow, map_add, map_sum, map_sub] at hi`. Establish `key : (ι b ^ 2 - 1) * (W.b₂ / 12) = (ι (L.weierstrassP Q) - W.b₂ / 12) + ∑ P ∈ S, ((ι (L.weierstrassP (Q + P)) - W.b₂ / 12) - (ι (L.weierstrassP P) - W.b₂ / 12)) - ι b ^ 2 * (ι (L.weierstrassP t) - W.b₂ / 12)`. Establish `e : ∑ P ∈ S, ((ι (L.weierstrassP (Q + P)) - W.b₂ / 12) - (ι (L.weierstrassP P) - W.b₂ / 12)) = ∑ P ∈ S, (ι (L.weierstrassP (Q + P)) - ι (L.weierstrassP P))` using `Finset.sum_congr rfl (fun _ _ => by ring)`.

Rewrite using `[e]`. Take the linear combination `hi`. Establish `hmem : (ι b ^ 2 - 1) * (W.b₂ / 12) ∈ Formalism.G.unitBall ℂ_[p]`. Rewrite using `[key]`. Use `sub_mem (add_mem iQ (Subring.sum_mem _ fun P hP => sub_mem (iQP P hP) (iP P hP))) (mul_mem (pow_mem hbI 2) iT)` and prove the remaining obligations.

Conclude with `hmem`.
-/
theorem hb_odd (dK : ℕ) (L : PeriodPair) (hmod : dK % 4 = 3) (hCM : Formalism.L2.Th1.CM.HasCMBy dK L)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (ι : ℂ ≃+* ℂ_[p]) (W : WeierstrassCurve ℂ_[p])
    (hU : Formalism.L2.Th1.E.Unif p L ι W) (hW : Formalism.L2.Th1.E.IntCurve W) (m n : ℤ)
    (hN : ¬ (p : ℤ) ∣ Formalism.L2.Th1.D.normInt dK m n) :
    ‖(ι ((m : ℂ) + (n : ℂ) * Formalism.L2.Th1.CM.omegaK dK) ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 := by
  have hN0 : Formalism.L2.Th1.D.normInt dK m n ≠ 0 := fun h => hN (by rw [h]; exact dvd_zero _)
  set b : ℂ := (m : ℂ) + (n : ℂ) * Formalism.L2.Th1.CM.omegaK dK with hb
  set bb : ℂ := (m : ℂ) + (n : ℂ) * (1 - Formalism.L2.Th1.CM.omegaK dK) with hbb
  have hprodC : b * bb = ((Formalism.L2.Th1.D.normInt dK m n : ℤ) : ℂ) :=
    Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.prod_bar hmod m n
  have hb0 : b ≠ 0 := by
    intro h
    apply hN0
    have h' := hprodC
    rw [h, zero_mul] at h'
    exact_mod_cast h'.symm
  have hst : Formalism.L2.Th1.F.MulStable L b := (Formalism.L2.Th1.F.hasCMByStable dK L hCM m n).1
  have hstb : Formalism.L2.Th1.F.MulStable L bb := by
    have h := (Formalism.L2.Th1.F.hasCMByStable dK L hCM (m + n) (-n)).1
    have e : (((m + n : ℤ) : ℂ) + ((-n : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK) = bb := by
      rw [hbb]; push_cast; ring
    rwa [e] at h
  obtain ⟨S, hS⟩ := Formalism.L2.Th1.F.kerRepsExist L b hb0 hst
  set t : ℂ := L.ω₁ / 2 with ht
  have ht0 : t ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have ht2 : 2 * t ∈ L.lattice := by
    rw [ht, mul_div_cancel₀ _ two_ne_zero]; exact L.ω₁_mem_lattice
  set Q : ℂ := t / b with hQ
  have hbQ : b * Q = t := by rw [hQ, mul_div_cancel₀ _ hb0]
  have hiso := Formalism.L2.Th1.F.isogenyP L b S hb0 hst hS Q (by rw [hbQ]; exact ht0)
  rw [hbQ] at hiso

  set M : ℕ := 2 * (Formalism.L2.Th1.D.normInt dK m n).natAbs with hM
  have hpM : ¬ p ∣ M := by
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).1 h with h2 | h2
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2)
    · exact hN (Int.natCast_dvd.2 h2)
  have hMR : ∀ R : ℂ, (2 * (b * bb)) * R ∈ L.lattice → (M : ℂ) * R ∈ L.lattice := by
    intro R hR
    rw [hprodC] at hR
    rcases Int.natAbs_eq (Formalism.L2.Th1.D.normInt dK m n) with e | e
    · have hc : ((Formalism.L2.Th1.D.normInt dK m n : ℤ) : ℂ) = ((Formalism.L2.Th1.D.normInt dK m n).natAbs : ℂ) := by
        rw [← Int.cast_natCast, ← e]
      rw [hc] at hR
      have e2 : (M : ℂ) = 2 * ((Formalism.L2.Th1.D.normInt dK m n).natAbs : ℂ) := by rw [hM]; push_cast; ring
      rw [e2]; exact hR
    · have hc : ((Formalism.L2.Th1.D.normInt dK m n : ℤ) : ℂ) = -((Formalism.L2.Th1.D.normInt dK m n).natAbs : ℂ) := by
        rw [← Int.cast_natCast, ← Int.cast_neg, ← e]
      rw [hc] at hR
      have e2 : (M : ℂ) * R = -(2 * -((Formalism.L2.Th1.D.normInt dK m n).natAbs : ℂ) * R) := by rw [hM]; push_cast; ring
      rw [e2]; exact neg_mem hR
  have intR : ∀ R : ℂ, R ∉ L.lattice → (2 * (b * bb)) * R ∈ L.lattice →
      ι (L.weierstrassP R) - W.b₂ / 12 ∈ Formalism.G.unitBall ℂ_[p] := by
    intro R hR h
    have h1 := (Formalism.L2.Th1.E.TransW.ptW_int Formalism.L2.Th1.E.ptWAdd Formalism.L2.Th1.E.ptWZero hU hW R M hpM
      (hMR R h) hR).1
    rw [Formalism.L2.Th1.E.AnaSysW.px_ptW hU R hR] at h1
    exact h1
  have mt : (2 * (b * bb)) * t ∈ L.lattice := by
    have e : (2 * (b * bb)) * t = b * (bb * (2 * t)) := by ring
    rw [e]; exact hst _ (hstb _ ht2)
  have mQ : (2 * (b * bb)) * Q ∈ L.lattice := by
    have e : (2 * (b * bb)) * Q = bb * (2 * (b * Q)) := by ring
    rw [e, hbQ]; exact hstb _ ht2
  have mP : ∀ P ∈ S, (2 * (b * bb)) * P ∈ L.lattice := by
    intro P hP
    have h := (hS.1 P hP).1
    have e : (2 * (b * bb)) * P = bb * (b * P) + bb * (b * P) := by ring
    rw [e]; exact add_mem (hstb _ h) (hstb _ h)
  have nQ : Q ∉ L.lattice := by
    intro h; apply ht0; rw [← hbQ]; exact hst _ h
  have nQP : ∀ P ∈ S, Q + P ∉ L.lattice := by
    intro P hP h
    apply ht0
    have e : t = b * (Q + P) - b * P := by rw [← hbQ]; ring
    rw [e]; exact sub_mem (hst _ h) (hS.1 P hP).1
  have iT := intR t ht0 mt
  have iQ := intR Q nQ mQ
  have iP : ∀ P ∈ S, ι (L.weierstrassP P) - W.b₂ / 12 ∈ Formalism.G.unitBall ℂ_[p] :=
    fun P hP => intR P (hS.1 P hP).2 (mP P hP)
  have iQP : ∀ P ∈ S, ι (L.weierstrassP (Q + P)) - W.b₂ / 12 ∈ Formalism.G.unitBall ℂ_[p] := by
    intro P hP
    refine intR (Q + P) (nQP P hP) ?_
    rw [mul_add]; exact add_mem mQ (mP P hP)

  have hbI : ι b ∈ Formalism.G.unitBall ℂ_[p] := by
    have hs : ι b + ι bb = ((2 * m + n : ℤ) : ℂ_[p]) := by
      rw [← map_add, hb, hbb]
      have e : ((m : ℂ) + (n : ℂ) * Formalism.L2.Th1.CM.omegaK dK) +
          ((m : ℂ) + (n : ℂ) * (1 - Formalism.L2.Th1.CM.omegaK dK)) = ((2 * m + n : ℤ) : ℂ) := by
        push_cast; ring
      rw [e, map_intCast]
    have hp : ι b * ι bb = ((Formalism.L2.Th1.D.normInt dK m n : ℤ) : ℂ_[p]) := by
      rw [← map_mul, hprodC, map_intCast]
    exact Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.norm_le_one_of_quad hs hp
      (IsUltrametricDist.norm_intCast_le_one ℂ_[p] _)

  have hi := congrArg ι hiso
  simp only [map_mul, map_pow, map_add, map_sum, map_sub] at hi
  have key : (ι b ^ 2 - 1) * (W.b₂ / 12) =
      (ι (L.weierstrassP Q) - W.b₂ / 12) +
        ∑ P ∈ S, ((ι (L.weierstrassP (Q + P)) - W.b₂ / 12) - (ι (L.weierstrassP P) - W.b₂ / 12)) -
        ι b ^ 2 * (ι (L.weierstrassP t) - W.b₂ / 12) := by
    have e : ∑ P ∈ S, ((ι (L.weierstrassP (Q + P)) - W.b₂ / 12) - (ι (L.weierstrassP P) - W.b₂ / 12)) =
        ∑ P ∈ S, (ι (L.weierstrassP (Q + P)) - ι (L.weierstrassP P)) :=
      Finset.sum_congr rfl (fun _ _ => by ring)
    rw [e]
    linear_combination hi
  have hmem : (ι b ^ 2 - 1) * (W.b₂ / 12) ∈ Formalism.G.unitBall ℂ_[p] := by
    rw [key]
    refine sub_mem (add_mem iQ (Subring.sum_mem _ fun P hP => sub_mem (iQP P hP) (iP P hP)))
      (mul_mem (pow_mem hbI 2) iT)
  exact hmem

/- English proof (translation)
Establish `hN0 : Formalism.L2.Th1.D.normInt dK m n ≠ 0`. Introduce `h`. Apply `hN` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `dvd_zero _`.

Take `⟨S, neg, hcard, hker, hnegP, hE, hprod, -⟩` from `Formalism.L2.Th1.D.CurveNormEndomorphisms.cdata L hmod hCM m n hN0`. Establish `hpN : ¬ p ∣ (S.card + 1)`. Introduce `h`. Apply `hN` to reduce the goal to its premises. Rewrite using `[← hcard]`.

Conclude with `h` after adjusting the coercions. Use `⟨S, neg, fun P => Formalism.L2.Th1.E.AnaSysW.xc p L ι W (P : ℂ), fun P => Formalism.L2.Th1.E.AnaSysW.yc p L ι W (P : ℂ), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `Formalism.L2.Th1.D.CurveNormEndomorphisms.endoCurve_of_endoZ (RingHom.id ℂ_[p]) W (wF := fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[p]) (Formalism.L2.Th1.F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))` to reduce the goal to its premises. Introduce `P`. Conclude with `(Formalism.L2.Th1.E.AnaSysW.nonsing hU _ (hker P).2).1`.

Introduce `P`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Formalism.L2.Th1.E.AnaSysW.xc, (hnegP P).1]`. Simplify using `only [Formalism.L2.Th1.E.AnaSysW.yc, Formalism.L2.Th1.E.AnaSysW.xc, WeierstrassCurve.Affine.negY, (hnegP P).1, (hnegP P).2, map_neg]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h` using `Formalism.L2.Th1.D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[p]) hE`. Simplify using `only [PowerSeries.map_id, RingHom.id_apply, Formalism.L2.Th1.E.AnaSysW.xc, sub_add_cancel]`. Rewrite using `[Formalism.L2.Th1.E.AnaSysW.wpBridge hU]`. Conclude with `h`. Introduce `P`.

Establish `h` using `(Formalism.L2.Th1.E.TransW.ptW_int Formalism.L2.Th1.E.ptWAdd Formalism.L2.Th1.E.ptWZero hU hW (P : ℂ) (S.card + 1) hpN (hker P).1 (hker P).2).1`. Rewrite `h` using `[Formalism.L2.Th1.E.AnaSysW.px_ptW hU _ (hker P).2]`. Then use the resulting hypothesis. Introduce `P`. Establish `h` using `(Formalism.L2.Th1.E.TransW.ptW_int Formalism.L2.Th1.E.ptWAdd Formalism.L2.Th1.E.ptWZero hU hW (P : ℂ) (S.card + 1) hpN (hker P).1 (hker P).2).2`. Rewrite `h` using `[Formalism.L2.Th1.E.AnaSysW.ptW_notMem hU _ (hker P).2]`.

Conclude with `h`. Rewrite using `[← map_mul, hprod, Fintype.card_coe]`. Simplify using the standard rewrite rules.
-/
theorem endoDatum_model (dK : ℕ) (L : PeriodPair) (hmod : dK % 4 = 3) (hCM : Formalism.L2.Th1.CM.HasCMBy dK L)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (W : WeierstrassCurve ℂ_[p])
    (hU : Formalism.L2.Th1.E.Unif p L ι W) (hW : Formalism.L2.Th1.E.IntCurve W) (m n : ℤ)
    (hN : ¬ (p : ℤ) ∣ Formalism.L2.Th1.D.normInt dK m n) :
    ∃ (S : Finset ℂ) (neg : S → S) (xP yP : S → ℂ_[p]),
      Formalism.L2.Th1.C.IsEndoCurve W neg xP yP (ι ((m : ℂ) + (n : ℂ) * Formalism.L2.Th1.CM.omegaK dK)) ∧
      (∀ P, ‖xP P‖ ≤ 1) ∧ (∀ P, ‖yP P‖ ≤ 1) ∧
      ι ((m : ℂ) + (n : ℂ) * Formalism.L2.Th1.CM.omegaK dK) * ι ((m : ℂ) + (n : ℂ) * (1 - Formalism.L2.Th1.CM.omegaK dK)) =
        (Fintype.card S : ℂ_[p]) + 1 := by
  have hN0 : Formalism.L2.Th1.D.normInt dK m n ≠ 0 := by
    intro h
    apply hN
    rw [h]
    exact dvd_zero _
  obtain ⟨S, neg, hcard, hker, hnegP, hE, hprod, -⟩ :=
    Formalism.L2.Th1.D.CurveNormEndomorphisms.cdata L hmod hCM m n hN0
  have hpN : ¬ p ∣ (S.card + 1) := by
    intro h
    apply hN
    rw [← hcard]
    exact_mod_cast h
  refine ⟨S, neg, fun P => Formalism.L2.Th1.E.AnaSysW.xc p L ι W (P : ℂ),
    fun P => Formalism.L2.Th1.E.AnaSysW.yc p L ι W (P : ℂ), ?_, ?_, ?_, ?_⟩
  · apply Formalism.L2.Th1.D.CurveNormEndomorphisms.endoCurve_of_endoZ (RingHom.id ℂ_[p]) W
      (wF := fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[p])
        (Formalism.L2.Th1.F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))
    · intro P
      exact (Formalism.L2.Th1.E.AnaSysW.nonsing hU _ (hker P).2).1
    · intro P
      refine ⟨?_, ?_⟩
      · simp only [Formalism.L2.Th1.E.AnaSysW.xc, (hnegP P).1]
      · simp only [Formalism.L2.Th1.E.AnaSysW.yc, Formalism.L2.Th1.E.AnaSysW.xc, WeierstrassCurve.Affine.negY,
          (hnegP P).1, (hnegP P).2, map_neg]
        ring
    · have h := Formalism.L2.Th1.D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[p]) hE
      simp only [PowerSeries.map_id, RingHom.id_apply, Formalism.L2.Th1.E.AnaSysW.xc, sub_add_cancel]
      rw [Formalism.L2.Th1.E.AnaSysW.wpBridge hU]
      exact h
  · intro P
    have h := (Formalism.L2.Th1.E.TransW.ptW_int Formalism.L2.Th1.E.ptWAdd Formalism.L2.Th1.E.ptWZero hU hW (P : ℂ)
      (S.card + 1) hpN (hker P).1 (hker P).2).1
    rwa [Formalism.L2.Th1.E.AnaSysW.px_ptW hU _ (hker P).2] at h
  · intro P
    have h := (Formalism.L2.Th1.E.TransW.ptW_int Formalism.L2.Th1.E.ptWAdd Formalism.L2.Th1.E.ptWZero hU hW (P : ℂ)
      (S.card + 1) hpN (hker P).1 (hker P).2).2
    rw [Formalism.L2.Th1.E.AnaSysW.ptW_notMem hU _ (hker P).2] at h
    exact h
  · rw [← map_mul, hprod, Fintype.card_coe]
    simp

/- English proof (translation)
Introduce `D p _ cc δ g hA hp2 a _`. Establish `hOk : g.Ok` using `hA.2.2.2.2`. Take `⟨ι, L, hι, hcm, hU, hW⟩` from `unif_setup D p cc δ g hA`. Establish `hd4 : D.host.d % 4 = 3` using `by have := D.host.hyp.2.2.2.1; omega`. Take `⟨m, hm⟩` from `exists_norm_prime D.host.d p hp2`.

Take `⟨S, neg, xP, yP, hE, hx, hy, hprod⟩` from `endoDatum_model D.host.d L hd4 hcm p ι g.W hU hW m 1 hm`. Establish `hb` using `hb_odd D.host.d L hd4 hcm p hp2 ι g.W hU hW m 1 hm`. Use `set β := ι ((m : ℂ) + ((1 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d) with hβ`. Use `set β' := ι ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - Formalism.L2.Th1.CM.omegaK D.host.d)) with hβ'`. Establish `h2 : ‖(2 : ℂ_[p])‖ = 1` using `Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.norm_two p hp2`.

Establish `hsum : β + β' = ((2 * m + 1 : ℤ) : ℂ_[p])`. Rewrite using `[hβ, hβ', ← map_add]`. Establish `e : ((m : ℂ) + ((1 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d) + ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - Formalism.L2.Th1.CM.omegaK D.host.d)) = ((2 * m + 1 : ℤ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e, map_intCast]`. Establish `hN1 : ‖(Fintype.card S : ℂ_[p]) + 1‖ = 1`.

Establish `e` using `Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.prod_bar hd4 m 1`. Establish `e' : β * β' = ((Formalism.L2.Th1.D.normInt D.host.d m 1 : ℤ) : ℂ_[p])`. Rewrite using `[hβ, hβ', ← map_mul, e, map_intCast]`. Rewrite using `[← hprod, e']`. Conclude with `Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.norm_int p hm`.

Establish `hβ1 : ‖β‖ = 1` using `Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.norm_eq_one_of_quad hsum hprod hN1`. Establish `hβinv : β⁻¹ ∈ Formalism.L2.KerInert.IwahoriBlocks.RB p` using `by show ‖β⁻¹‖ ≤ 1`. Rewrite using `[norm_inv, hβ1, inv_one]`. Establish `hR` using `Formalism.L2.Th1.C.curveEndoR ℂ_[p] (Formalism.L2.KerInert.IwahoriBlocks.RB p) g.W (Formalism.L2.KerInert.IwahoriBlocks.coeffIn_g g hOk) S neg xP yP β β' hE (fun P => hx P) (fun P => hy P) hprod hβ1.le hβinv hb`. Take `⟨hlp, hwp, hAx, hFG, -⟩` from `Formalism.L2.Th1.C.curveFrame ℂ_[p] (Formalism.L2.KerInert.IwahoriBlocks.RB p) g.W (Formalism.L2.KerInert.IwahoriBlocks.coeffIn_g g hOk)`.

Establish `h2R : (2 : ℂ_[p])⁻¹ ∈ Formalism.L2.KerInert.IwahoriBlocks.RB p` using `by show ‖(2 : ℂ_[p])⁻¹‖ ≤ 1`. Rewrite using `[norm_inv, h2, inv_one]`. Establish `hEβ` using `Formalism.L2.Th1.C.endIntFromDatum ℂ_[p] (Formalism.L2.KerInert.IwahoriBlocks.RB p) _ _ _ _ _ S neg xP _ _ β β' hlp hwp hAx h2R hR`. Establish `hEω : Formalism.L2.Th1.C.EndInt (Formalism.L2.KerInert.IwahoriBlocks.RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) (ι (Formalism.L2.Th1.CM.omegaK D.host.d))`. Establish `hm'` using `Formalism.L2.Th1.G.WeierstrassCurveSeries.endInt_int (Formalism.L2.KerInert.IwahoriBlocks.RB p) _ _ hlp hFG (-m)`.

Establish `h` using `Formalism.L2.Th1.C.Pts.endInt_add hlp hFG hEβ hm'`. Establish `e : β + ((-m : ℤ) : ℂ_[p]) = ι (Formalism.L2.Th1.CM.omegaK D.host.d)`. Rewrite using `[hβ, map_add, map_mul, map_intCast, map_intCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h` using `[e]`. Then use the resulting hypothesis. Conclude with `Formalism.L2.KerInert.IwahoriBlocks.integralMv_of_endInt g hOk _ (Formalism.L2.KerInert.IwahoriBlocks.endInt_OK D p g hOk ι hι hEω a)`.
-/
theorem unit_endo : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → p ≠ 2 → ∀ a : 𝓞 D.host.K, Nat.Coprime (Algebra.norm ℤ a).natAbs p →
    IntegralMv (g.mulBy (GL3Theta.tauK D g.lam (a : D.host.K)) (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
  intro D p _ cc δ g hA hp2 a _
  have hOk : g.Ok := hA.2.2.2.2
  obtain ⟨ι, L, hι, hcm, hU, hW⟩ := unif_setup D p cc δ g hA
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  obtain ⟨m, hm⟩ := exists_norm_prime D.host.d p hp2
  obtain ⟨S, neg, xP, yP, hE, hx, hy, hprod⟩ :=
    endoDatum_model D.host.d L hd4 hcm p ι g.W hU hW m 1 hm
  have hb := hb_odd D.host.d L hd4 hcm p hp2 ι g.W hU hW m 1 hm
  set β := ι ((m : ℂ) + ((1 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d) with hβ
  set β' := ι ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - Formalism.L2.Th1.CM.omegaK D.host.d)) with hβ'
  have h2 : ‖(2 : ℂ_[p])‖ = 1 := Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.norm_two p hp2
  have hsum : β + β' = ((2 * m + 1 : ℤ) : ℂ_[p]) := by
    rw [hβ, hβ', ← map_add]
    have e : ((m : ℂ) + ((1 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d) +
        ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - Formalism.L2.Th1.CM.omegaK D.host.d)) = ((2 * m + 1 : ℤ) : ℂ) := by
      push_cast; ring
    rw [e, map_intCast]
  have hN1 : ‖(Fintype.card S : ℂ_[p]) + 1‖ = 1 := by
    have e := Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.prod_bar hd4 m 1
    have e' : β * β' = ((Formalism.L2.Th1.D.normInt D.host.d m 1 : ℤ) : ℂ_[p]) := by
      rw [hβ, hβ', ← map_mul, e, map_intCast]
    rw [← hprod, e']
    exact Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.norm_int p hm
  have hβ1 : ‖β‖ = 1 := Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.norm_eq_one_of_quad hsum hprod hN1
  have hβinv : β⁻¹ ∈ Formalism.L2.KerInert.IwahoriBlocks.RB p := by
    show ‖β⁻¹‖ ≤ 1
    rw [norm_inv, hβ1, inv_one]
  have hR := Formalism.L2.Th1.C.curveEndoR ℂ_[p] (Formalism.L2.KerInert.IwahoriBlocks.RB p) g.W
    (Formalism.L2.KerInert.IwahoriBlocks.coeffIn_g g hOk) S neg xP yP β β' hE (fun P => hx P) (fun P => hy P) hprod
    hβ1.le hβinv hb
  obtain ⟨hlp, hwp, hAx, hFG, -⟩ := Formalism.L2.Th1.C.curveFrame ℂ_[p] (Formalism.L2.KerInert.IwahoriBlocks.RB p) g.W
    (Formalism.L2.KerInert.IwahoriBlocks.coeffIn_g g hOk)
  have h2R : (2 : ℂ_[p])⁻¹ ∈ Formalism.L2.KerInert.IwahoriBlocks.RB p := by
    show ‖(2 : ℂ_[p])⁻¹‖ ≤ 1
    rw [norm_inv, h2, inv_one]
  have hEβ := Formalism.L2.Th1.C.endIntFromDatum ℂ_[p] (Formalism.L2.KerInert.IwahoriBlocks.RB p) _ _ _ _ _ S neg xP _ _ β β'
    hlp hwp hAx h2R hR
  have hEω : Formalism.L2.Th1.C.EndInt (Formalism.L2.KerInert.IwahoriBlocks.RB p) (Formalism.L2.Th1.A.logSer g.W)
      (Formalism.L2.Th1.A.expSer g.W) (ι (Formalism.L2.Th1.CM.omegaK D.host.d)) := by
    have hm' := Formalism.L2.Th1.G.WeierstrassCurveSeries.endInt_int (Formalism.L2.KerInert.IwahoriBlocks.RB p) _ _ hlp hFG (-m)
    have h := Formalism.L2.Th1.C.Pts.endInt_add hlp hFG hEβ hm'
    have e : β + ((-m : ℤ) : ℂ_[p]) = ι (Formalism.L2.Th1.CM.omegaK D.host.d) := by
      rw [hβ, map_add, map_mul, map_intCast, map_intCast]; push_cast; ring
    rwa [e] at h
  exact Formalism.L2.KerInert.IwahoriBlocks.integralMv_of_endInt g hOk _
    (Formalism.L2.KerInert.IwahoriBlocks.endInt_OK D p g hOk ι hι hEω a)

end GlobalTheory.CMUnit
