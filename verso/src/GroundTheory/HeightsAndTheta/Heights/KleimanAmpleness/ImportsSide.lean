import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherExtra
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PReindexDim
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TrdegEqOfLeOfIsAlgebraic
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

/- English proof (translation)
Introduce `F _ K _ _ ι _ Ω _ _ y k₀ N e hmod d`. Take `⟨hnz, hsame⟩` from `hmod`. Use `choose c hc using hnz`. Take `⟨c', hc', htr⟩` from `exists_trdeg_chartRing_eq y _ hsame c hc`. Establish `hy` using `trdeg_quotient_mIdealOver (F := F) y c hc`.

Establish `hx` using `trdeg_quotient_mIdealOver (F := F) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c' hc'`. Rewrite `hx` using `[← htr, Fintype.card_unit]`. Establish `_ : (mIdealOver F y).IsPrime` using `RingHom.ker_isPrime _`. Establish `_ : (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀))).IsPrime` using `RingHom.ker_isPrime _`. Establish `hfin` using `trdeg_lt_aleph0_of_finiteType (R := F) (S := MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y)`.

Rewrite `hfin` using `[hy]`. Take `⟨t, ht⟩` from `Cardinal.lt_aleph0.1 (lt_of_le_of_lt le_self_add hfin)`. Establish `dimy : ringKrullDim (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) = ((t + Fintype.card K : ℕ) : ℕ∞)`. Rewrite using `[GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hy, ht]`. Simplify using the standard rewrite rules.

Establish `dimx : ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S` using `F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) = ((t + 1 : ℕ) : WithBot ℕ∞) := by`. Rewrite using `[← ReindexDim.proof F (ι k₀) Ω (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) N e, GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hx, ht]`. Simplify using the standard rewrite rules. Establish `hrel : relDim (mIdealOver F y) = ((t : ℕ) : WithBot (WithTop ℤ))`. Unfold `relDim`.

Rewrite using `[dimy]`. Establish `e₁ : WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d) ((((t + Fintype.card K : ℕ) : ℕ∞)) : WithBot ℕ∞) = (((((t + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))` using `rfl`. Rewrite using `[e₁, Nat.cast_add, add_sub_cancel_right]`. Both sides reduce to the same expression. Rewrite using `[hrel]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `h.dim`. Rewrite `h'` using `[dimx]`. Establish `htd : t + 1 = d + 1` using `by exact_mod_cast h'`.

Rewrite using `[show t = d by omega]`. Introduce `h`. Establish `htd : t = d` using `by exact_mod_cast h`. Use `⟨inferInstance, fun p hp n => Kleiman.homogeneousComponent_mem_primeOf _ hp n, le_rfl, ⟨e (c k₀), ?_⟩, by rw [dimx, htd]⟩` and prove the remaining obligations. Rewrite using `[Kleiman.mem_primeOf_of_isHomogeneous _ (isHomogeneous_X F _), aeval_X]`.

Simplify `hc k₀` using `[IndefiniteRowSideFullHecke.Kleiman2.blockVec]`.
-/
theorem ModelDimEq.full : ModelDimEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod d
  obtain ⟨hnz, hsame⟩ := hmod
  choose c hc using hnz
  obtain ⟨c', hc', htr⟩ := exists_trdeg_chartRing_eq y _ hsame c hc
  have hy := trdeg_quotient_mIdealOver (F := F) y c hc
  have hx := trdeg_quotient_mIdealOver (F := F) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c' hc'
  rw [← htr, Fintype.card_unit] at hx

  have _ : (mIdealOver F y).IsPrime := RingHom.ker_isPrime _
  have _ : (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀))).IsPrime :=
    RingHom.ker_isPrime _
  have hfin := trdeg_lt_aleph0_of_finiteType (R := F) (S := MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y)
  rw [hy] at hfin
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.1 (lt_of_le_of_lt le_self_add hfin)
  have dimy : ringKrullDim (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) = ((t + Fintype.card K : ℕ) : ℕ∞) := by
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hy, ht]
    simp
  have dimx : ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) =
      ((t + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← ReindexDim.proof F (ι k₀) Ω (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) N e,
      GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hx, ht]
    simp
  have hrel : relDim (mIdealOver F y) = ((t : ℕ) : WithBot (WithTop ℤ)) := by
    unfold relDim
    rw [dimy]
    have e₁ : WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)
        ((((t + Fintype.card K : ℕ) : ℕ∞)) : WithBot ℕ∞) =
        (((((t + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
    rw [e₁, Nat.cast_add, add_sub_cancel_right]
    rfl
  rw [hrel]
  constructor
  · intro h
    have h' := h.dim
    rw [dimx] at h'
    have htd : t + 1 = d + 1 := by exact_mod_cast h'
    rw [show t = d by omega]
  · intro h
    have htd : t = d := by exact_mod_cast h
    refine ⟨inferInstance, fun p hp n => Kleiman.homogeneousComponent_mem_primeOf _ hp n, le_rfl,
      ⟨e (c k₀), ?_⟩, by rw [dimx, htd]⟩
    rw [Kleiman.mem_primeOf_of_isHomogeneous _ (isHomogeneous_X F _), aeval_X]
    simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hc k₀

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
