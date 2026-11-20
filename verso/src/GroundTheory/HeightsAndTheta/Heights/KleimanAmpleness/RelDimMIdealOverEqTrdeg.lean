import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TrdegEqOfLeOfIsAlgebraic
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open GroundTheory.Heights₂.Heights.NumbersDVR (segreVec)

/- English proof (translation)
Establish `hy` using `trdeg_quotient_mIdealOver (F := F) y c hc`. Establish `_ : (mIdealOver F y).IsPrime` using `RingHom.ker_isPrime _`. Establish `hfin` using `trdeg_lt_aleph0_of_finiteType (R := F) (S := MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y)`. Rewrite `hfin` using `[hy]`. Take `⟨t, ht⟩` from `Cardinal.lt_aleph0.1 (lt_of_le_of_lt le_self_add hfin)`.

Establish `dimy : ringKrullDim (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) = ((t + Fintype.card K : ℕ) : ℕ∞)`. Rewrite using `[GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hy, ht]`. Simplify using the standard rewrite rules. Use `⟨t, ht, ?_⟩` and prove the remaining obligations. Unfold `relDim`.

Rewrite using `[dimy]`. Establish `e₁ : WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d) ((((t + Fintype.card K : ℕ) : ℕ∞)) : WithBot ℕ∞) = (((((t + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))` using `rfl`. Rewrite using `[e₁, Nat.cast_add, add_sub_cancel_right]`. Both sides reduce to the same expression.
-/
theorem relDim_mIdealOver_eq_trdeg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ t : ℕ, Algebra.trdeg F (chartRingOver F y c) = t ∧
      relDim (mIdealOver F y) = ((t : ℕ) : WithBot (WithTop ℤ)) := by
  have hy := trdeg_quotient_mIdealOver (F := F) y c hc
  have _ : (mIdealOver F y).IsPrime := RingHom.ker_isPrime _
  have hfin := trdeg_lt_aleph0_of_finiteType (R := F) (S := MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y)
  rw [hy] at hfin
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.1 (lt_of_le_of_lt le_self_add hfin)
  have dimy : ringKrullDim (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) =
      ((t + Fintype.card K : ℕ) : ℕ∞) := by
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hy, ht]
    simp
  refine ⟨t, ht, ?_⟩
  unfold relDim
  rw [dimy]
  have e₁ : WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)
      ((((t + Fintype.card K : ℕ) : ℕ∞)) : WithBot ℕ∞) =
      (((((t + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
  rw [e₁, Nat.cast_add, add_sub_cancel_right]
  rfl

/- English proof (translation)
Introduce `F _ K _ _ ι _ Ω _ _ y hy`. Use `choose c hc using hy`. Take `⟨t, ht, hrel⟩` from `relDim_mIdealOver_eq_trdeg (F := F) y c hc`. Take `⟨t', ht', hrel'⟩` from `relDim_mIdealOver_eq_trdeg (F := F) (segreJoin y) (segreChart c c) (segreChart_adm y (segreVec_ne_zero y hc) hc)`. Establish `heq : chartRingOver F (segreJoin y) (segreChart c c) = chartRingOver F y c` using `le_antisymm (segre_diag_le (S := F) y c) (chartRingOver_le_segre (S := F) y c c)`.

Rewrite `ht'` using `[heq, ht]`. Establish `htt : t = t'` using `by exact_mod_cast ht'`. Rewrite using `[hrel, hrel', htt]`.
-/
theorem SegreDim.proof : SegreDim.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y hy
  choose c hc using hy
  obtain ⟨t, ht, hrel⟩ := relDim_mIdealOver_eq_trdeg (F := F) y c hc
  obtain ⟨t', ht', hrel'⟩ := relDim_mIdealOver_eq_trdeg (F := F) (segreJoin y) (segreChart c c)
    (segreChart_adm y (segreVec_ne_zero y hc) hc)
  have heq : chartRingOver F (segreJoin y) (segreChart c c) = chartRingOver F y c :=
    le_antisymm (segre_diag_le (S := F) y c) (chartRingOver_le_segre (S := F) y c c)
  rw [heq, ht] at ht'
  have htt : t = t' := by exact_mod_cast ht'
  rw [hrel, hrel', htt]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
