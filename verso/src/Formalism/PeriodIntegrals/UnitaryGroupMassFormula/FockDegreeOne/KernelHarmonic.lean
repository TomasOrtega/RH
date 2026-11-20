import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.RedOps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.ExistsMonomialWeight

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW.RedOps

open PI.FockOneDegW

variable {p q r s : ℕ}

/- English proof (translation)
Rewrite using `[lowOp_apply, lowOp_apply, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : linePos ((a, d) : Ln p q r s) = true`. Simplify using `only [h, ↓reduceIte]`. Establish `hc : pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) (pderiv l' P)) = pderiv l' (pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P))`.

Rewrite using `[PI.FockOneDegW.Core.pd_comm ((a, d) : Ln p q r s) l' P, PI.FockOneDegW.Core.pd_comm ((a, c) : Ln p q r s) l' (pderiv ((a, d) : Ln p q r s) P)]`. Rewrite using `[dd_X_mul, hc]`. Normalize the expressions using the abelian group laws. Simplify using `[h]`.
-/
theorem lowOp_Xd (c d : Ix r s) (l l' : Ln p q r s) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (X l * pderiv l' P) =
      X l * pderiv l' (lowOp (p := p) (q := q) c d P) +
      ∑ a : Ix p q, (if linePos ((a, d) : Ln p q r s) = true then
        ((if ((a, d) : Ln p q r s) = l then pderiv ((a, c) : Ln p q r s) (pderiv l' P) else 0) +
         (if ((a, c) : Ln p q r s) = l then pderiv ((a, d) : Ln p q r s) (pderiv l' P) else 0))
        else 0) := by
  rw [lowOp_apply, lowOp_apply, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : linePos ((a, d) : Ln p q r s) = true
  · simp only [h, ↓reduceIte]
    have hc : pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) (pderiv l' P)) =
        pderiv l' (pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P)) := by
      rw [PI.FockOneDegW.Core.pd_comm ((a, d) : Ln p q r s) l' P,
        PI.FockOneDegW.Core.pd_comm ((a, c) : Ln p q r s) l' (pderiv ((a, d) : Ln p q r s) P)]
    rw [dd_X_mul, hc]
    abel
  · simp [h]

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single a]`. Simplify using `[Prod.mk.injEq]`. Introduce `b _ hb`. Simplify using `[Prod.mk.injEq, hb]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ a) h`.
-/
theorem sum_rows (c d e : Ix r s) (a : Ix p q) (F G : Ix p q → Pol p q r s) :
    ∑ a' : Ix p q, (if linePos ((a', d) : Ln p q r s) = true then
      ((if ((a', d) : Ln p q r s) = (a, e) then F a' else 0) +
       (if ((a', c) : Ln p q r s) = (a, e) then G a' else 0)) else 0) =
    if linePos ((a, d) : Ln p q r s) = true then
      ((if d = e then F a else 0) + (if c = e then G a else 0)) else 0 := by
  rw [Finset.sum_eq_single a]
  · simp [Prod.mk.injEq]
  · intro b _ hb
    simp [Prod.mk.injEq, hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

/- English proof (translation)
The claim follows from `hcd ((FockRL.linePos_right a c d).1 (h1.trans h2.symm))`.
-/
theorem not_both (c d : Ix r s) (hcd : ¬ sameBlock c d) (a : Ix p q)
    (h1 : linePos ((a, c) : Ln p q r s) = true) (h2 : linePos ((a, d) : Ln p q r s) = true) :
    False :=
  hcd ((FockRL.linePos_right a c d).1 (h1.trans h2.symm))

/- English proof (translation)
Establish `hcd' : c ≠ d`. Apply the tactic sequence `rintro rfl; exact hcd (by rcases c with c | c <;> simp [sameBlock])`. Rewrite using `[posOp_apply, posOp_apply, map_sum]`. Establish `hterm : ∀ e : Ix r s, lowOp (p` using `p) (q := q) c d (if linePos ((a, e) : Ln p q r s) = true then X ((a, e) : Ln p q r s) * pderiv ((b, e) : Ln p q r s) P else 0) = (if linePos ((a, e) : Ln p q r s) = true then X ((a, e) : Ln p q r s) * pderiv ((b, e) : Ln p q r s) (lowOp (p := p) (q := q) c d P) else 0) + (if line …`. Introduce `e`.

Distinguish the cases in `h : linePos ((a, e) : Ln p q r s) = true`. Simplify using `only [h, ↓reduceIte]`. Rewrite using `[lowOp_Xd, sum_rows c d e a (fun a' => pderiv ((a', c) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P)) (fun a' => pderiv ((a', d) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P))]`. Simplify using `[h]`. Repeatedly rewrite using `[hterm]`.

Rewrite using `[Finset.sum_add_distrib]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single d]`. Distinguish the cases in `h : linePos ((a, d) : Ln p q r s) = true`. Simplify using `[h, hcd']`.

Simplify using `[h]`. Introduce `e _ hed`. Distinguish the cases in `h1 : linePos ((a, e) : Ln p q r s) = true`. Distinguish the cases in `h2 : linePos ((a, d) : Ln p q r s) = true`. Establish `hce : c ≠ e`.

Introduce and unpack `rfl`. Conclude with `not_both c d hcd a h1 h2`. Simplify using `[h1, h2, Ne.symm hed, hce]`. Simplify using `[h1, h2]`. Simplify using `[h1]`.

Simplify using the standard rewrite rules.
-/
theorem lowOp_posOp (c d : Ix r s) (hcd : ¬ sameBlock c d) (a b : Ix p q) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (posOp a b P) =
      posOp a b (lowOp (p := p) (q := q) c d P) +
      (if linePos ((a, d) : Ln p q r s) = true then
        pderiv ((a, c) : Ln p q r s) (pderiv ((b, d) : Ln p q r s) P) else 0) := by
  have hcd' : c ≠ d := by
    rintro rfl; exact hcd (by rcases c with c | c <;> simp [sameBlock])
  rw [posOp_apply, posOp_apply, map_sum]
  have hterm : ∀ e : Ix r s,
      lowOp (p := p) (q := q) c d (if linePos ((a, e) : Ln p q r s) = true then
        X ((a, e) : Ln p q r s) * pderiv ((b, e) : Ln p q r s) P else 0) =
      (if linePos ((a, e) : Ln p q r s) = true then
        X ((a, e) : Ln p q r s) * pderiv ((b, e) : Ln p q r s) (lowOp (p := p) (q := q) c d P) else 0) +
      (if linePos ((a, e) : Ln p q r s) = true then
        (if linePos ((a, d) : Ln p q r s) = true then
          ((if d = e then pderiv ((a, c) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P) else 0) +
           (if c = e then pderiv ((a, d) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P) else 0))
          else 0) else 0) := by
    intro e
    by_cases h : linePos ((a, e) : Ln p q r s) = true
    · simp only [h, ↓reduceIte]
      rw [lowOp_Xd, sum_rows c d e a (fun a' => pderiv ((a', c) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P))
        (fun a' => pderiv ((a', d) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P))]
    · simp [h]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single d]
  · by_cases h : linePos ((a, d) : Ln p q r s) = true
    · simp [h, hcd']
    · simp [h]
  · intro e _ hed
    by_cases h1 : linePos ((a, e) : Ln p q r s) = true
    · by_cases h2 : linePos ((a, d) : Ln p q r s) = true
      · have hce : c ≠ e := by
          rintro rfl; exact not_both c d hcd a h1 h2
        simp [h1, h2, Ne.symm hed, hce]
      · simp [h1, h2]
    · simp [h1]
  · simp

/- English proof (translation)
Establish `hcd' : c ≠ d`. Apply the tactic sequence `rintro rfl; exact hcd (by rcases c with c | c <;> simp [sameBlock])`. Establish `hba : linePos ((b, d) : Ln p q r s) = linePos ((a, d) : Ln p q r s)` using `(FockRL.linePos_left b a d).2 (FockRL.sameBlock_symm hab)`. Rewrite using `[negOp_apply, negOp_apply, map_sum]`. Establish `hterm : ∀ e : Ix r s, lowOp (p` using `p) (q := q) c d (if linePos ((b, e) : Ln p q r s) = true then 0 else X ((b, e) : Ln p q r s) * pderiv ((a, e) : Ln p q r s) P) = (if linePos ((b, e) : Ln p q r s) = true then 0 else X ((b, e) : Ln p q r s) * pderiv ((a, e) : Ln p q r s) (lowOp (p := p) (q := q) c d P)) + (if line …`.

Introduce `e`. Distinguish the cases in `h : linePos ((b, e) : Ln p q r s) = true`. Simplify using `[h]`. Simplify using `only [h, Bool.false_eq_true, ↓reduceIte]`. Rewrite using `[lowOp_Xd, sum_rows c d e b (fun a' => pderiv ((a', c) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P)) (fun a' => pderiv ((a', d) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P))]`.

Repeatedly rewrite using `[hterm]`. Rewrite using `[Finset.sum_add_distrib]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single c]`. Distinguish the cases in `h : linePos ((b, d) : Ln p q r s) = true`.

Establish `hbc : linePos ((b, c) : Ln p q r s) = false`. Consider the cases of `h' : linePos ((b, c) : Ln p q r s)`. Both sides reduce to the same expression. Conclude with `(not_both c d hcd b h' h).elim`. Rewrite using `[← hba]`.

Simplify using `[h, hbc, Ne.symm hcd', PI.FockOneDegW.Core.pd_comm ((b, d) : Ln p q r s) ((a, c) : Ln p q r s) P]`. Rewrite using `[← hba]`. Simplify using `[h]`. Introduce `e _ hec`. Distinguish the cases in `h1 : linePos ((b, e) : Ln p q r s) = true`.

Simplify using `[h1]`. Distinguish the cases in `h2 : linePos ((b, d) : Ln p q r s) = true`. Establish `hde : d ≠ e`. Introduce and unpack `rfl`. Conclude with `h1 h2`.

Simplify using `[h1, h2, hde, Ne.symm hec]`. Simplify using `[h1, h2]`. Simplify using the standard rewrite rules.
-/
theorem lowOp_negOp (c d : Ix r s) (hcd : ¬ sameBlock c d) (a b : Ix p q) (hab : sameBlock a b)
    (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (negOp b a P) =
      negOp b a (lowOp (p := p) (q := q) c d P) +
      (if linePos ((a, d) : Ln p q r s) = true then
        pderiv ((a, c) : Ln p q r s) (pderiv ((b, d) : Ln p q r s) P) else 0) := by
  have hcd' : c ≠ d := by
    rintro rfl; exact hcd (by rcases c with c | c <;> simp [sameBlock])
  have hba : linePos ((b, d) : Ln p q r s) = linePos ((a, d) : Ln p q r s) :=
    (FockRL.linePos_left b a d).2 (FockRL.sameBlock_symm hab)
  rw [negOp_apply, negOp_apply, map_sum]
  have hterm : ∀ e : Ix r s,
      lowOp (p := p) (q := q) c d (if linePos ((b, e) : Ln p q r s) = true then 0 else
        X ((b, e) : Ln p q r s) * pderiv ((a, e) : Ln p q r s) P) =
      (if linePos ((b, e) : Ln p q r s) = true then 0 else
        X ((b, e) : Ln p q r s) * pderiv ((a, e) : Ln p q r s) (lowOp (p := p) (q := q) c d P)) +
      (if linePos ((b, e) : Ln p q r s) = true then 0 else
        (if linePos ((b, d) : Ln p q r s) = true then
          ((if d = e then pderiv ((b, c) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P) else 0) +
           (if c = e then pderiv ((b, d) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P) else 0))
          else 0)) := by
    intro e
    by_cases h : linePos ((b, e) : Ln p q r s) = true
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      rw [lowOp_Xd, sum_rows c d e b (fun a' => pderiv ((a', c) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P))
        (fun a' => pderiv ((a', d) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P))]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single c]
  · by_cases h : linePos ((b, d) : Ln p q r s) = true
    · have hbc : linePos ((b, c) : Ln p q r s) = false := by
        cases h' : linePos ((b, c) : Ln p q r s)
        · rfl
        · exact (not_both c d hcd b h' h).elim
      rw [← hba]
      simp [h, hbc, Ne.symm hcd', PI.FockOneDegW.Core.pd_comm ((b, d) : Ln p q r s) ((a, c) : Ln p q r s) P]
    · rw [← hba]
      simp [h]
  · intro e _ hec
    by_cases h1 : linePos ((b, e) : Ln p q r s) = true
    · simp [h1]
    · by_cases h2 : linePos ((b, d) : Ln p q r s) = true
      · have hde : d ≠ e := by
          rintro rfl; exact h1 h2
        simp [h1, h2, hde, Ne.symm hec]
      · simp [h1, h2]
  · simp

end PI.FockOneDegW.RedOps

namespace PI.FockOneDegW

open PI.FockOneDegW.RedOps

/- English proof (translation)
Introduce `p q r s a b hab P hP`. Rewrite `hP`, the goal using `[harmIff]`. Introduce `c d hcd`. Rewrite using `[fock_operators_kernel p q r s a b hab]`. Simplify using `only [LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub, lowOp_posOp c d hcd, lowOp_negOp c d hcd a b hab, hP c d hcd, map_zero, zero_add, sub_self]`.

Apply the tactic sequence `split_ifs <;> simp [hP c d hcd]`.
-/
theorem kernel_harmonic : KHarm := by
  intro p q r s a b hab P hP
  rw [harmIff] at hP ⊢
  intro c d hcd
  rw [fock_operators_kernel p q r s a b hab]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub, lowOp_posOp c d hcd,
    lowOp_negOp c d hcd a b hab, hP c d hcd, map_zero, zero_add, sub_self]
  split_ifs <;> simp [hP c d hcd]

end PI.FockOneDegW
