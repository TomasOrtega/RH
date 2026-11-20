import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.Count.PerpSize

open GlobalTheory.Count.PerpStep

/- English proof (translation)
Introduce `I x R hi hR hhi hL N hPN hNA`. Take `⟨-, hA, -⟩` from `GlobalTheory.PointLattice.lamX_selfDual I x`. Take `⟨htc, -, -, -, hw⟩` from `GlobalTheory.Count.FrameMajorant.frames_give_majorants I x`. Establish `hX : ∀ v, IsUnit (frm I x v).det` using `fun v => (hw v).1`. Take `⟨-, -, -, hm⟩` from `GlobalTheory.Count.PerpStep.main I x`.

Take `⟨N', n1, n2, n3, n4⟩` from `nd_sat (bas I) (frm I x) hX hA hNA`. Take `⟨sP, rP, ppR, -, -⟩` from `hm R R hR hR le_rfl`. Take `⟨sS, rS, ppN, -, -⟩` from `hm N' N' n2 n2 le_rfl`. Establish `hPN' : perpIn I x R ≤ N'` using `hPN.le.trans n1`. Take `⟨-, -, -, hle, hq⟩` from `hm _ N' sP n2 hPN'`.

Rewrite `hle`, `hq` using `[ppR]`. Establish `hfg : ∀ {M}, M ≤ lamX I x → M.FG` using `fun h => Submodule.FG.of_le hA h`. Establish `hR0 : R ≠ ⊥`. Introduce `e`. Establish `h1 : perpIn I x N' = R`.

Rewrite `hle`, the goal using `[e]`. Conclude with `le_bot_iff.1 hle`. Rewrite `ppN` using `[h1]`. Conclude with `(lt_of_lt_of_le hPN n1).ne ppN`. Rewrite `hq` using `[htQ_eq _ _ hX _ _ (hfg hR.1) (sat_mono _ _ sS hle hR.1), htQ_eq _ _ hX _ _ (hfg n2.1) (sat_mono _ _ sP hPN' n2.1), ← Real.exp_neg]`.

Establish `hq'` using `Real.exp_injective hq`. Take `⟨l0, lb⟩` from `largest_bound (bas I) (frm I x) hX (hfg hR.1) hR0 hle`. Establish `hd` using `rk_lt (bas I) (frm I x) hX hA sP hPN hNA`. Establish `r1` using `(plLat _ _ _ (bas I) (frm I x) hX _ (hfg hR.1)).2.1`. Establish `r2` using `(plLat _ _ _ (bas I) (frm I x) hX _ (hfg sP.1)).2.1`.

Establish `r3` using `(plLat _ _ _ (bas I) (frm I x) hX _ (hfg sS.1)).2.1`. Establish `r4` using `(plLat _ _ _ (bas I) (frm I x) hX _ (hfg n2.1)).2.1`. Establish `hrk : rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) + rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) R = rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x N') + rk (Formalism.HermitianLatticesTheory.re …`. Rewrite using `[← n3, r1, r2, r3, r4, ← mul_add, ← mul_add, rP, rS]`. Establish `hrk' : (rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) R : ℝ) - rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x N') = (rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N : ℝ) - rk (Formalism.HermitianLatticesTheory.re …`.

Establish `h` using `congrArg (Nat.cast : ℕ → ℝ) hrk`. Move the coercions through the operations in `at h`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `lb` using `[hrk']`. Rewrite using `[log_sizeQ (bas I) (frm I x) hX hA sP hPN hNA, ← Real.log_le_iff_le_exp (inv_pos.2 hhi), le_div_iff₀ (sub_pos.2 hd), Real.log_inv]`.

Establish `h4` using `Real.log_le_log l0 hL`. Establish `h5` using `mul_le_mul_of_nonneg_right h4 (sub_pos.2 hd).le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem inv_le_sizeQ_perp : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → ∀ N, perpIn I x R < N → N ≤ lamX I x → hi⁻¹ ≤ sizeQ (bas I) (frm I x) N (perpIn I x R) := by
  intro I x R hi hR hhi hL N hPN hNA
  obtain ⟨-, hA, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨htc, -, -, -, hw⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  have hX : ∀ v, IsUnit (frm I x v).det := fun v => (hw v).1
  obtain ⟨-, -, -, hm⟩ := GlobalTheory.Count.PerpStep.main I x
  obtain ⟨N', n1, n2, n3, n4⟩ := nd_sat (bas I) (frm I x) hX hA hNA
  obtain ⟨sP, rP, ppR, -, -⟩ := hm R R hR hR le_rfl
  obtain ⟨sS, rS, ppN, -, -⟩ := hm N' N' n2 n2 le_rfl
  have hPN' : perpIn I x R ≤ N' := hPN.le.trans n1
  obtain ⟨-, -, -, hle, hq⟩ := hm _ N' sP n2 hPN'
  rw [ppR] at hle hq
  have hfg : ∀ {M}, M ≤ lamX I x → M.FG := fun h => Submodule.FG.of_le hA h
  have hR0 : R ≠ ⊥ := by
    intro e
    have h1 : perpIn I x N' = R := by
      rw [e] at hle ⊢
      exact le_bot_iff.1 hle
    rw [h1] at ppN
    exact (lt_of_lt_of_le hPN n1).ne ppN
  rw [htQ_eq _ _ hX _ _ (hfg hR.1) (sat_mono _ _ sS hle hR.1),
    htQ_eq _ _ hX _ _ (hfg n2.1) (sat_mono _ _ sP hPN' n2.1), ← Real.exp_neg] at hq
  have hq' := Real.exp_injective hq
  obtain ⟨l0, lb⟩ := largest_bound (bas I) (frm I x) hX (hfg hR.1) hR0 hle
  have hd := rk_lt (bas I) (frm I x) hX hA sP hPN hNA
  have r1 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg hR.1)).2.1
  have r2 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg sP.1)).2.1
  have r3 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg sS.1)).2.1
  have r4 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg n2.1)).2.1
  have hrk : rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) +
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) R =
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x N') +
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N := by
    rw [← n3, r1, r2, r3, r4, ← mul_add, ← mul_add, rP, rS]
  have hrk' : (rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) R : ℝ) -
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x N') =
      (rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N : ℝ) -
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hrk
    push_cast at h
    linarith
  rw [hrk'] at lb
  rw [log_sizeQ (bas I) (frm I x) hX hA sP hPN hNA, ← Real.log_le_iff_le_exp (inv_pos.2 hhi),
    le_div_iff₀ (sub_pos.2 hd), Real.log_inv]
  have h4 := Real.log_le_log l0 hL
  have h5 := mul_le_mul_of_nonneg_right h4 (sub_pos.2 hd).le
  linarith

end GlobalTheory.Count.PerpSize
