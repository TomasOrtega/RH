import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.BlockSum

/- English proof (translation)
Proceed by induction on `m using Fin.induction with`. Consider the case `zero => simp [hW.1, detOn_bot, Fin.not_lt_zero]`. Consider the case `succ m ih`. Rewrite using `[ht.detOn_succ hW m, ih, ← Real.exp_add]`. Use `congr 1`.

Establish `e1 : (Finset.univ.filter fun l : Fin b => l.castSucc < m.succ) = Iic m`. Use extensionality with `l`. Simplify using `[Fin.castSucc_lt_succ_iff]`. Establish `e2 : (Finset.univ.filter fun l : Fin b => l.castSucc < m.castSucc) = Iio m`. Use extensionality with `l`.

Simplify using the standard rewrite rules. Rewrite using `[e1, e2, ← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]`. Simplify using `[add_comm]`.
-/
theorem detOn_prefix {n b : ℕ} {ε : Fin n → Bool} {W' : Flag n b}
    (hW : IsIsoFlag ε (fun _ => 1) W') {x : Fin b → ℝ} {t : UJ ε} (ht : IsSplit ε W' x t) (m : Fin (b + 1)) :
    detOn (uMat t) (W' m) = Real.exp (∑ l with l.castSucc < m, x l) := by
  induction m using Fin.induction with
  | zero => simp [hW.1, detOn_bot, Fin.not_lt_zero]
  | succ m ih =>
    rw [ht.detOn_succ hW m, ih, ← Real.exp_add]
    congr 1
    have e1 : (Finset.univ.filter fun l : Fin b => l.castSucc < m.succ) = Iic m := by
      ext l; simp [Fin.castSucc_lt_succ_iff]
    have e2 : (Finset.univ.filter fun l : Fin b => l.castSucc < m.castSucc) = Iio m := by
      ext l; simp
    rw [e1, e2, ← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    simp [add_comm]

/- English proof (translation)
Introduce `n a b ε W W' β p hW hp hβ x t ht hl i`. Establish `hS : ∀ k : Fin (a + 1), ∑ l with l.castSucc < p k, x l = 0` using `fun k => by`. Establish `h1` using `hl.2 k`. Rewrite `h1` using `[← hp k, detOn_prefix hW ht]`. Conclude with `Real.exp_eq_one_iff _ |>.1 h1`.

Use `set A := p i.castSucc`. Use `set B := p i.succ`. Establish `hblk : (Finset.univ.filter fun l : Fin b => β l = i) = ((Finset.univ.filter fun l : Fin b => l.castSucc < B).filter fun l => ¬ l.castSucc < A)`. Use extensionality with `l`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, hβ, not_lt]`.

The claim follows by propositional logic. Establish `hsplit` using `Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun l : Fin b => l.castSucc < B) (fun l => l.castSucc < A) x`. Rewrite `hsplit` using `[hS i.succ, ← hblk]`. Establish `h0 : ∑ l ∈ (Finset.univ.filter fun l : Fin b => l.castSucc < B).filter (fun l => l.castSucc < A), x l = 0`. Rewrite using `[Finset.filter_filter]`.

Break down `le_total A B with h | h` into its components or cases. Establish `: (Finset.univ.filter fun l : Fin b => l.castSucc < B ∧ l.castSucc < A) = Finset.univ.filter fun l : Fin b => l.castSucc < A`. Use extensionality with `l`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `⟨fun h' => h'.2, fun h' => ⟨lt_of_lt_of_le h' h, h'⟩⟩`.

Rewrite using `[this]`. Conclude with `hS i.castSucc`. Establish `: (Finset.univ.filter fun l : Fin b => l.castSucc < B ∧ l.castSucc < A) = Finset.univ.filter fun l : Fin b => l.castSucc < B`. Use extensionality with `l`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.

Conclude with `⟨fun h' => h'.1, fun h' => ⟨h', lt_of_lt_of_le h' h⟩⟩`. Rewrite using `[this]`. Conclude with `hS i.succ`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem blockSum_eq_zero : ∀ {n a b : ℕ} {ε : Fin n → Bool} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a}
    {p : Fin (a + 1) → Fin (b + 1)}, IsIsoFlag ε (fun _ => 1) W' → (∀ i, W' (p i) = W i) →
    (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) →
    ∀ {x : Fin b → ℝ} {t : UJ ε}, IsSplit ε W' x t → t ∈ leviOne ε W → ∀ i, ∑ l with β l = i, x l = 0 := by
  intro n a b ε W W' β p hW hp hβ x t ht hl i
  have hS : ∀ k : Fin (a + 1), ∑ l with l.castSucc < p k, x l = 0 := fun k => by
    have h1 := hl.2 k
    rw [← hp k, detOn_prefix hW ht] at h1
    exact Real.exp_eq_one_iff _ |>.1 h1
  set A := p i.castSucc
  set B := p i.succ
  have hblk : (Finset.univ.filter fun l : Fin b => β l = i) =
      ((Finset.univ.filter fun l : Fin b => l.castSucc < B).filter fun l => ¬ l.castSucc < A) := by
    ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hβ, not_lt]; tauto
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter fun l : Fin b => l.castSucc < B) (fun l => l.castSucc < A) x
  rw [hS i.succ, ← hblk] at hsplit
  have h0 : ∑ l ∈ (Finset.univ.filter fun l : Fin b => l.castSucc < B).filter (fun l => l.castSucc < A), x l = 0 := by
    rw [Finset.filter_filter]
    rcases le_total A B with h | h
    · have : (Finset.univ.filter fun l : Fin b => l.castSucc < B ∧ l.castSucc < A) =
          Finset.univ.filter fun l : Fin b => l.castSucc < A := by
        ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h' => h'.2, fun h' => ⟨lt_of_lt_of_le h' h, h'⟩⟩
      rw [this]; exact hS i.castSucc
    · have : (Finset.univ.filter fun l : Fin b => l.castSucc < B ∧ l.castSucc < A) =
          Finset.univ.filter fun l : Fin b => l.castSucc < B := by
        ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h' => h'.1, fun h' => ⟨h', lt_of_lt_of_le h' h⟩⟩
      rw [this]; exact hS i.succ
  linarith

end GlobalTheory.RealInd.BlockSum
