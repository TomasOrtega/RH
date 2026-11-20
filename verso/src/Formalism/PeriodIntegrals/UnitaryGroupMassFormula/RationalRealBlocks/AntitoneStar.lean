import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.EvenStep

open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem reM_rfl {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) : reM (m := m) rfl A = A := by
  ext i j
  rfl

/- English proof (translation)
Rewrite using `[detShift, dif_pos (Nat.succ_pos m)]`. Both sides reduce to the same expression.
-/
theorem detShift_eq {m : ℕ} (w : Fin (m + 1) → ℤ) : detShift w = w (Fin.last m) := by
  rw [detShift, dif_pos (Nat.succ_pos m)]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[natW, nuOf, detShift_eq]`.
-/
theorem natW_eq {m : ℕ} (w : Fin (m + 1) → ℤ) : natW w = nuOf w := by
  funext i
  rw [natW, nuOf, detShift_eq]

/- English proof (translation)
Introduce `_ _ hij` and use `neg_le_neg (h (Fin.rev_le_rev.mpr hij))`.
-/
theorem antitone_star {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone fun i : Fin (m + 1) => -lam i.rev :=
  fun _ _ hij => neg_le_neg (h (Fin.rev_le_rev.mpr hij))

/- English proof (translation)
Introduce `nV n' m lam0 Tau _ n LL _ h pos G M embLL lam hanti htie hM`. Substitute `h` using the available equality. Introduce `v s f hf`. Use `set τ := pos ⟨v, s⟩ with hτ`. Establish `hl : lam0 v s = lam τ` using `funext fun i => by rw [htie v s i]; rfl`.

Take `⟨M0, hM0⟩` from `hM τ`. Establish `hf' : f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf (lam τ))`. Rewrite using `[← natW_eq]`. Conclude with `hf`. Distinguish the cases in `hs : Even s.val`.

Establish `hla : lamAt (lam0 v) s = lam τ` using `by rw [lamAt, if_pos hs, hl]`. Take `⟨F, hF, hFe⟩` from `hE m LL embLL (lam τ) (hanti τ) M0 f hf'`. Use `⟨F, ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[blkMod, hla, if_pos (hanti τ)]`. Conclude with `hF`.

Establish `h1` using `hFe (y.1 τ) (y.2 τ)`. Rewrite using `[zAt, if_pos hs, reM_rfl, eAt, hla, detShift_eq, hM0]`. Conclude with `h1`. Establish `hla : lamAt (lam0 v) s = fun i => -lam τ i.rev` using `by rw [lamAt, if_neg hs, hl]`. Take `⟨F, hF, hFe⟩` from `hO m LL embLL (lam τ) (hanti τ) M0 f hf'`.

Use `⟨F, ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[blkMod, hla, if_pos (antitone_star (hanti τ))]`. Conclude with `hF`. Establish `h1` using `hFe (y.1 τ) (y.2 τ)`. Rewrite using `[zAt, if_neg hs, reM_rfl, eAt, hla, detShift_eq, hM0]`.

Conclude with `h1`.
-/
theorem stmt_of (hE : EvenStep) (hO : OddStep) : Stmt := by
  intro nV n' m lam0 Tau _ n LL _ h pos G M embLL lam hanti htie hM
  subst h
  intro v s f hf
  set τ := pos ⟨v, s⟩ with hτ
  have hl : lam0 v s = lam τ := funext fun i => by rw [htie v s i]; rfl
  obtain ⟨M0, hM0⟩ := hM τ
  have hf' : f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf (lam τ)) := by
    rw [← natW_eq]; exact hf
  by_cases hs : Even s.val
  · have hla : lamAt (lam0 v) s = lam τ := by rw [lamAt, if_pos hs, hl]
    obtain ⟨F, hF, hFe⟩ := hE m LL embLL (lam τ) (hanti τ) M0 f hf'
    refine ⟨F, ?_, fun y => ?_⟩
    · rw [blkMod, hla, if_pos (hanti τ)]; exact hF
    · have h1 := hFe (y.1 τ) (y.2 τ)
      rw [zAt, if_pos hs, reM_rfl, eAt, hla, detShift_eq, hM0]
      exact h1
  · have hla : lamAt (lam0 v) s = fun i => -lam τ i.rev := by rw [lamAt, if_neg hs, hl]
    obtain ⟨F, hF, hFe⟩ := hO m LL embLL (lam τ) (hanti τ) M0 f hf'
    refine ⟨F, ?_, fun y => ?_⟩
    · rw [blkMod, hla, if_pos (antitone_star (hanti τ))]; exact hF
    · have h1 := hFe (y.1 τ) (y.2 τ)
      rw [zAt, if_neg hs, reM_rfl, eAt, hla, detShift_eq, hM0]
      exact h1

end PI.BlockRatReal
