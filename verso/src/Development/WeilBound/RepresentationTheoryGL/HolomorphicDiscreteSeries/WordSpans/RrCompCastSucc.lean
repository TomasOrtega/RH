import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpan
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowExp
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmColExp

noncomputable section

open Matrix Finset

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.FourierDecayAlt.P.CapelliAbstractCharacter

section Ring

variable {A : Type} [Ring A] [Algebra ℂ A]

/- English proof (translation)
Unfold `qminor`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 3`. Use function extensionality and compare the values at `k`. Simplify using `only [Tm, Function.comp_apply, hι.eq_iff]`.
-/
theorem qminor_comp {n m t : ℕ} (E : Fin n → Fin n → A) (ι : Fin m → Fin n) (hι : Function.Injective ι)
    (a b : Fin t → Fin m) (u : ℂ) :
    qminor (fun x y => E (ι x) (ι y)) a b u = qminor E (ι ∘ a) (ι ∘ b) u := by
  unfold qminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp only [Tm, Function.comp_apply, hι.eq_iff]

/- English proof (translation)
Rewrite using `[PI.QnCovDetW.qminor_perm_perm E hE τ τ u]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]`.
-/
theorem qdet_perm {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (τ : Equiv.Perm (Fin n)) (u : ℂ) :
    qminor E τ τ u = qdet E u := by
  rw [PI.QnCovDetW.qminor_perm_perm E hE τ τ u]
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]

end Ring

variable {N : ℕ}

def rr (ι : Fin (N + 1) → Fin (N + 2)) (z : Fin (N + 2)) : Fin (N + 2) → Fin (N + 2) :=
  Fin.lastCases (motive := fun _ => Fin (N + 2)) z ι

/- English proof (translation)
Simplify using `[rr]`.
-/
theorem rr_castSucc (ι : Fin (N + 1) → Fin (N + 2)) (z : Fin (N + 2)) (i : Fin (N + 1)) : rr ι z i.castSucc = ι i := by
  simp [rr]

/- English proof (translation)
Simplify using `[rr]`.
-/
theorem rr_last (ι : Fin (N + 1) → Fin (N + 2)) (z : Fin (N + 2)) : rr ι z (Fin.last (N + 1)) = z := by
  simp [rr]

/- English proof (translation)
Introduce `x y h`. Proceed by induction on `x using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `y using Fin.lastCases with`. Consider the case `last => rfl`.

Consider the case `cast j => rw [rr_last, rr_castSucc] at h`. Conclude with `absurd h.symm (hz j)`. Consider the case `cast i`. Proceed by induction on `y using Fin.lastCases with`. Consider the case `last => rw [rr_last, rr_castSucc] at h`.

Conclude with `absurd h (hz i)`. Consider the case `cast j => rw [rr_castSucc, rr_castSucc] at h`. Rewrite using `[hι h]`.
-/
theorem rr_injective {ι : Fin (N + 1) → Fin (N + 2)} {z : Fin (N + 2)} (hι : Function.Injective ι) (hz : ∀ a, ι a ≠ z) :
    Function.Injective (rr ι z) := by
  intro x y h
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => rfl
    | cast j => rw [rr_last, rr_castSucc] at h; exact absurd h.symm (hz j)
  | cast i =>
    induction y using Fin.lastCases with
    | last => rw [rr_last, rr_castSucc] at h; exact absurd h (hz i)
    | cast j => rw [rr_castSucc, rr_castSucc] at h; rw [hι h]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `rr_castSucc ι z i`.
-/
theorem rr_comp_castSucc (ι : Fin (N + 1) → Fin (N + 2)) (z : Fin (N + 2)) : rr ι z ∘ Fin.castSucc = ι := by
  funext i; exact rr_castSucc ι z i

/- English proof (translation)
Use function extensionality and compare the values at `j`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`. Simplify using `only [Function.comp_apply, Fin.lastCases_last]`. Rewrite using `[Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last c)), Fin.succ_last, rr_last]`.

Consider the case `cast j`. Simplify using `only [Function.comp_apply, Fin.lastCases_castSucc]`. Rewrite using `[Fin.castSucc_succAbove_castSucc, rr_castSucc]`.
-/
theorem rr_succAbove (ι : Fin (N + 1) → Fin (N + 2)) (z : Fin (N + 2)) (c : Fin (N + 1)) :
    rr ι z ∘ (Fin.castSucc c).succAbove = Fin.lastCases (motive := fun _ => Fin (N + 2)) z (ι ∘ c.succAbove) := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    simp only [Function.comp_apply, Fin.lastCases_last]
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last c)),
      Fin.succ_last, rr_last]
  | cast j =>
    simp only [Function.comp_apply, Fin.lastCases_castSucc]
    rw [Fin.castSucc_succAbove_castSucc, rr_castSucc]

/- English proof (translation)
Introduce `V _ _ N E ι z hE hι hz u v`. Establish `hrr : Function.Injective (rr ι z)` using `rr_injective hι hz`. Establish `h1 : qdet E u = qminor E (rr ι z) (rr ι z) u`. Use `qdet_perm E hE (Equiv.ofBijective (rr ι z) (Finite.injective_iff_bijective.mp hrr)) u` as an intermediate fact. Simplify using `using this.symm`.

Establish `hrow` using `PI.QmRowExpWork.expLastRow_of quantum_minor_row_form (Module.End ℂ V) (N + 2) (N + 1) E hE (rr ι z) (rr ι z) u`. Establish `hcol : ∀ c : Fin (N + 1), qminor E ι (rr ι z ∘ (Fin.castSucc c).succAbove) (u - 1) = ∑ l : Fin (N + 1), (((-1 : ℤ) ^ (N + (l : ℕ)) : ℤ) : Module.End ℂ V) * (qminor (fun a b : Fin (N + 1) => E (ι a) (ι b)) l.succAbove c.succAbove (u - 1) * E (ι l) z)`. Introduce `c`. Rewrite using `[rr_succAbove, PI.QmColExpWork.expLast]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[qminor_comp E ι hι]`. Establish `e1 : (Fin.lastCases (motive` using `fun _ => Fin (N + 2)) z (ι ∘ c.succAbove) ∘ Fin.castSucc) = ι ∘ c.succAbove := by`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Establish `e2 : Tm E (u - 1 - (N : ℂ)) (ι l) (Fin.lastCases (motive` using `fun _ => Fin (N + 2)) z (ι ∘ c.succAbove) (Fin.last N)) = E (ι l) z := by`.

Simplify using `[Tm, hz l]`. Rewrite using `[e1, e2]`. Establish `hT : ∀ x : Fin (N + 1), Tm E u z (ι x) = E z (ι x)`. Introduce `x`. Simplify using `[Tm, Ne.symm (hz x)]`.

Establish `hq : qminor E ι ι (u - 1) = qdet (fun a b : Fin (N + 1) => E (ι a) (ι b)) (u - 1)`. Rewrite using `[qdet, qminor_comp E ι hι]`. Both sides reduce to the same expression. Establish `hlast : ((-1 : ℤ) ^ (N + 1 + ((Fin.last (N + 1) : Fin (N + 2)) : ℕ))) = 1`. Rewrite using `[Fin.val_last]`.

Conclude with `Even.neg_one_pow ⟨N + 1, rfl⟩`. Establish `hs : ∀ c l : ℕ, ((-1 : ℤ) ^ (N + 1 + c)) * (-1) ^ (N + l) = -((-1 : ℤ) ^ (l + c))`. Introduce `c l`. Rewrite using `[← pow_add]`. Establish `h : N + 1 + c + (N + l) = (l + c) + 1 + 2 * N` using `by ring`.

Rewrite using `[h, pow_add, pow_add, pow_mul]`. Evaluate the numerical expressions. Rewrite using `[h1, hrow, Fin.sum_univ_castSucc]`. Simplify using `only [Fin.succAbove_last, rr_comp_castSucc, rr_last, rr_castSucc, hcol, hT, hq, hlast, Int.cast_one, one_mul, Fin.coe_castSucc]`. Unfold `Th`.

Simplify using `only [← zsmul_eq_mul, Finset.smul_sum, Finset.sum_mul, smul_mul_assoc]`. Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]`. Rewrite using `[add_comm, sub_eq_add_neg (a := (qdet (fun a b : Fin (N + 1) => E (ι a) (ι b)) (u - 1)) ((Tm E u z z) v))]`. Use `congr 1`. Rewrite using `[← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, hs, neg_smul, neg_inj, ← Int.cast_smul_eq_zsmul ℂ]`. Use `push_cast`.

Apply the tactic sequence `try rfl`.
-/
theorem algId : AlgId := by
  intro V _ _ N E ι z hE hι hz u v
  have hrr : Function.Injective (rr ι z) := rr_injective hι hz
  have h1 : qdet E u = qminor E (rr ι z) (rr ι z) u := by
    have := qdet_perm E hE (Equiv.ofBijective (rr ι z) (Finite.injective_iff_bijective.mp hrr)) u
    simpa using this.symm
  have hrow := PI.QmRowExpWork.expLastRow_of quantum_minor_row_form (Module.End ℂ V) (N + 2) (N + 1) E hE
    (rr ι z) (rr ι z) u
  have hcol : ∀ c : Fin (N + 1), qminor E ι (rr ι z ∘ (Fin.castSucc c).succAbove) (u - 1) =
      ∑ l : Fin (N + 1), (((-1 : ℤ) ^ (N + (l : ℕ)) : ℤ) : Module.End ℂ V) *
        (qminor (fun a b : Fin (N + 1) => E (ι a) (ι b)) l.succAbove c.succAbove (u - 1) * E (ι l) z) := by
    intro c
    rw [rr_succAbove, PI.QmColExpWork.expLast]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [qminor_comp E ι hι]
    have e1 : (Fin.lastCases (motive := fun _ => Fin (N + 2)) z (ι ∘ c.succAbove) ∘ Fin.castSucc) =
        ι ∘ c.succAbove := by
      funext j
      simp
    have e2 : Tm E (u - 1 - (N : ℂ)) (ι l)
        (Fin.lastCases (motive := fun _ => Fin (N + 2)) z (ι ∘ c.succAbove) (Fin.last N)) = E (ι l) z := by
      simp [Tm, hz l]
    rw [e1, e2]
  have hT : ∀ x : Fin (N + 1), Tm E u z (ι x) = E z (ι x) := by
    intro x
    simp [Tm, Ne.symm (hz x)]
  have hq : qminor E ι ι (u - 1) = qdet (fun a b : Fin (N + 1) => E (ι a) (ι b)) (u - 1) := by
    rw [qdet, qminor_comp E ι hι]
    rfl
  have hlast : ((-1 : ℤ) ^ (N + 1 + ((Fin.last (N + 1) : Fin (N + 2)) : ℕ))) = 1 := by
    rw [Fin.val_last]
    exact Even.neg_one_pow ⟨N + 1, rfl⟩
  have hs : ∀ c l : ℕ, ((-1 : ℤ) ^ (N + 1 + c)) * (-1) ^ (N + l) = -((-1 : ℤ) ^ (l + c)) := by
    intro c l
    rw [← pow_add]
    have h : N + 1 + c + (N + l) = (l + c) + 1 + 2 * N := by ring
    rw [h, pow_add, pow_add, pow_mul]
    norm_num
  rw [h1, hrow, Fin.sum_univ_castSucc]
  simp only [Fin.succAbove_last, rr_comp_castSucc, rr_last, rr_castSucc, hcol, hT, hq, hlast,
    Int.cast_one, one_mul, Fin.coe_castSucc]
  unfold Th
  simp only [← zsmul_eq_mul, Finset.smul_sum, Finset.sum_mul, smul_mul_assoc]
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    Finset.sum_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [add_comm, sub_eq_add_neg (a := (qdet (fun a b : Fin (N + 1) => E (ι a) (ι b)) (u - 1))
    ((Tm E u z z) v))]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul, hs, neg_smul, neg_inj, ← Int.cast_smul_eq_zsmul ℂ]
  push_cast
  try rfl

end PositivityTheory.RgHe.SM
