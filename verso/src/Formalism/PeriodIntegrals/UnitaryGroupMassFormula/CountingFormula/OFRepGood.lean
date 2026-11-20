import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnipotentIntegralPreservesLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameDeterminant.DdSNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseMulEquiv

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `h0 : ddS D ≠ 0` using `PI.TripleFrameDeterminant.W.ddS_ne_zero D`. Establish `hle : ddS D ^ k ≤ 1`. Rewrite using `[ddS, ← FractionalIdeal.coeIdeal_pow]`. Conclude with `FractionalIdeal.coeIdeal_le_one`. Establish `h` using `FractionalIdeal.inv_anti_mono (pow_ne_zero k h0) one_ne_zero hle`.

Rewrite `h` using `[inv_one]`. Rewrite using `[zpow_neg, zpow_natCast]`. Conclude with `h (FractionalIdeal.one_mem_one _)`.
-/
theorem one_mem_ddS_zpow (D : Formalism.BasicNotions.D7) (k : ℕ) :
    (1 : D.host.E) ∈ ((ddS D) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have h0 : ddS D ≠ 0 := PI.TripleFrameDeterminant.W.ddS_ne_zero D
  have hle : ddS D ^ k ≤ 1 := by
    rw [ddS, ← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one
  have h := FractionalIdeal.inv_anti_mono (pow_ne_zero k h0) one_ne_zero hle
  rw [inv_one] at h
  rw [zpow_neg, zpow_natCast]
  exact h (FractionalIdeal.one_mem_one _)

/- English proof (translation)
Establish `hs : ∀ x y, (VS D).hT y x = starRingEnd D.host.E ((VS D).hT x y)` using `fun x y => ((VS D).herm.eq x y).symm`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => simp [FlagG.fvec, G.z_norm]`.

Consider the case `cast j`. Rewrite using `[hs]`. Simplify using `[FlagG.fvec, G.z_orth j]`. Consider the case `cast i`. Proceed by induction on `b using Fin.lastCases with`.

Consider the case `last => simp [FlagG.fvec, G.z_orth i]`. Consider the case `cast j => simp [FlagG.fvec, G.e_iso i j]`.
-/
theorem flag_gram (D : Formalism.BasicNotions.D7) {T' : D.host.E} (G : FlagG (VS D) D.R.rS T') (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (G.fvec a) (G.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T' else 0 := by
  have hs : ∀ x y, (VS D).hT y x = starRingEnd D.host.E ((VS D).hT x y) :=
    fun x y => ((VS D).herm.eq x y).symm
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, G.z_norm]
    | cast j =>
      rw [hs]
      simp [FlagG.fvec, G.z_orth j]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, G.z_orth i]
    | cast j => simp [FlagG.fvec, G.e_iso i j]

/- English proof (translation)
Introduce `D T T' F0 Λ Z F' hF'`. Take `⟨hT, -, -, hFr, hZ⟩` from `hF'`. Establish `hfr : fr D (F'.fl.e, F'.fl.z) = F'.fl.fvec` using `rfl`. Use `⟨fun b => ?_, fun a b => ?_, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[hfr]`.

Establish `h` using `PI.CntNotIntW.frame_mem Λ F' hFr.2 hT.1.1 b 1 (one_mem_ddS_zpow D _)`. Rewrite `h` using `[one_smul]`. Then use the resulting hypothesis. Rewrite using `[hfr, ← hZ]`. Both sides reduce to the same expression. Rewrite using `[hfr]`.

Conclude with `flag_gram D F'.fl a b`.
-/
theorem good_places_integral : GoodEZ := by
  intro D T T' F0 Λ Z F' hF'
  obtain ⟨hT, -, -, hFr, hZ⟩ := hF'
  have hfr : fr D (F'.fl.e, F'.fl.z) = F'.fl.fvec := rfl
  refine ⟨fun b => ?_, fun a b => ?_, fun a b => ?_⟩
  · rw [hfr]
    have h := PI.CntNotIntW.frame_mem Λ F' hFr.2 hT.1.1 b 1 (one_mem_ddS_zpow D _)
    rwa [one_smul] at h
  · rw [hfr, ← hZ]
    rfl
  · rw [hfr]
    exact flag_gram D F'.fl a b

end PI.UnitaryGroupMassFormula.CntFormula
