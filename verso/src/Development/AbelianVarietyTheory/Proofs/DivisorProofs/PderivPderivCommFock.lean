import Mathlib
import Formalism.LocalRingCardinality.DataTheta

open Formalism.BasicNotions.TH MvPolynomial

namespace GlobalTheory

/- English proof (translation)
Establish `hc : ∀ (a b k : σ), pderiv a (pderiv b (X k : MvPolynomial σ ℂ)) = 0`. Introduce `a b k`. Rewrite using `[pderiv_X, Pi.single_apply]`. Use `split_ifs`. Conclude with `pderiv_one`.

Conclude with `map_zero _`. Use `MvPolynomial.induction_on (motive := fun P => pderiv i (pderiv j P) = pderiv j (pderiv i P)) P ?_ ?_ ?_` and prove the remaining obligations. Introduce `a`. Simplify using the standard rewrite rules. Introduce `p q hp hq`.

Rewrite using `[map_add, map_add, map_add, map_add, hp, hq]`. Introduce `p k hp`. Simplify using `only [pderiv_mul, map_add, hc, mul_zero, add_zero]`. Rewrite using `[hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pderiv_pderiv_comm_fock {σ : Type} (i j : σ) (P : MvPolynomial σ ℂ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  have hc : ∀ (a b k : σ), pderiv a (pderiv b (X k : MvPolynomial σ ℂ)) = 0 := by
    intro a b k
    rw [pderiv_X, Pi.single_apply]
    split_ifs
    · exact pderiv_one
    · exact map_zero _
  refine MvPolynomial.induction_on (motive := fun P => pderiv i (pderiv j P) = pderiv j (pderiv i P)) P ?_ ?_ ?_
  · intro a
    simp
  · intro p q hp hq
    rw [map_add, map_add, map_add, map_add, hp, hq]
  · intro p k hp
    simp only [pderiv_mul, map_add, hc, mul_zero, add_zero]
    rw [hp]
    ring

/- English proof (translation)
Establish `hcomm : ∀ (i j : Ln p q r s) (P : Pol p q r s), pderiv i (pderiv j P) = pderiv j (pderiv i P)` using `fun i j P => pderiv_pderiv_comm_fock i j P`. Establish `hX : ∀ (i j : Ln p q r s), pderiv i (X j : Pol p q r s) = if j = i then 1 else 0`. Introduce `i j`. Rewrite using `[pderiv_X, Pi.single_apply]`. Establish `hne : ∀ l m : Ln p q r s, linePos l ≠ linePos m → l ≠ m`.

Introduce and unpack `l m h rfl`. Conclude with `h rfl`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hlm : l = m`. Substitute `hlm` using the available equality.

Rewrite using `[if_pos rfl]`. Apply the tactic sequence `cases hl : linePos l <;> simp only [lowB, raiB, hl, Bool.false_eq_true, ↓reduceIte] <;>`. Apply the tactic sequence `refine LinearMap.ext fun f => ?_ <;>`. Simplify using `[Module.End.mul_apply, hX]`. Rewrite using `[if_neg hlm]`.

Apply the tactic sequence `cases hl : linePos l <;> cases hm : linePos m <;>`. Apply the tactic sequence `simp only [lowB, raiB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>`. Apply the tactic sequence `refine LinearMap.ext fun f => ?_ <;>`. Apply the tactic sequence `simp [Module.End.mul_apply, hX, hcomm, Ne.symm hlm, hlm] <;> ring`. Apply the tactic sequence `cases hl : linePos l <;> cases hm : linePos m <;>`.

Apply the tactic sequence `simp only [lowB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>`. Apply the tactic sequence `refine LinearMap.ext fun f => ?_ <;>`. Apply the tactic sequence `simp [Module.End.mul_apply, hX, hcomm] <;> (try ring_nf) <;> (try (intro h; subst h; exact absurd (hl.symm.trans hm) (by decide)))`. Apply the tactic sequence `cases hl : linePos l <;> cases hm : linePos m <;>`. Apply the tactic sequence `simp only [raiB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>`.

Apply the tactic sequence `refine LinearMap.ext fun f => ?_ <;>`. Apply the tactic sequence `simp [Module.End.mul_apply, hX, hcomm] <;> (try ring_nf) <;> (try (intro h; subst h; exact absurd (hl.symm.trans hm) (by decide)))`.
-/
theorem fock_letters_ccr (p q r s : ℕ) (l m : Ln p q r s) :
    (lowB l * raiB m - raiB m * lowB l = if l = m then (1 : Module.End ℂ (Pol p q r s)) else 0) ∧
      lowB l * lowB m = lowB m * lowB l ∧ raiB l * raiB m = raiB m * raiB l := by
  classical
  have hcomm : ∀ (i j : Ln p q r s) (P : Pol p q r s), pderiv i (pderiv j P) = pderiv j (pderiv i P) :=
    fun i j P => pderiv_pderiv_comm_fock i j P
  have hX : ∀ (i j : Ln p q r s), pderiv i (X j : Pol p q r s) = if j = i then 1 else 0 := by
    intro i j
    rw [pderiv_X, Pi.single_apply]
  have hne : ∀ l m : Ln p q r s, linePos l ≠ linePos m → l ≠ m := by
    rintro l m h rfl
    exact h rfl
  refine ⟨?_, ?_, ?_⟩
  · by_cases hlm : l = m
    · subst hlm
      rw [if_pos rfl]
      cases hl : linePos l <;> simp only [lowB, raiB, hl, Bool.false_eq_true, ↓reduceIte] <;>
        refine LinearMap.ext fun f => ?_ <;>
        simp [Module.End.mul_apply, hX]
    · rw [if_neg hlm]
      cases hl : linePos l <;> cases hm : linePos m <;>
        simp only [lowB, raiB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
        refine LinearMap.ext fun f => ?_ <;>
        simp [Module.End.mul_apply, hX, hcomm, Ne.symm hlm, hlm] <;> ring
  · cases hl : linePos l <;> cases hm : linePos m <;>
      simp only [lowB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
      refine LinearMap.ext fun f => ?_ <;>
      simp [Module.End.mul_apply, hX, hcomm] <;> (try ring_nf) <;> (try (intro h; subst h; exact absurd (hl.symm.trans hm) (by decide)))
  · cases hl : linePos l <;> cases hm : linePos m <;>
      simp only [raiB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
      refine LinearMap.ext fun f => ?_ <;>
      simp [Module.End.mul_apply, hX, hcomm] <;> (try ring_nf) <;> (try (intro h; subst h; exact absurd (hl.symm.trans hm) (by decide)))

end GlobalTheory
