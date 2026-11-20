import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S Matrix

section

variable {K : Type} [Field K] {n : ℕ}

def cmonoE (p q : Fin n) (y : K) : Matrix (Fin n) (Fin n) K := fun a b => if a = p ∧ b = q then y else 0

/- English proof (translation)
Introduce `a b hab`. Unfold `cmonoE`. Rewrite using `[if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `absurd h (not_lt.2 hab)`.
-/
theorem cmono_strict (p q : Fin n) (y : K) (h : p < q) : StrictUp (cmonoE p q y) := by
  intro a b hab
  unfold cmonoE
  rw [if_neg]
  rintro ⟨rfl, rfl⟩
  exact absurd h (not_lt.2 hab)

/- English proof (translation)
Unfold `supSum`. Rewrite using `[Finset.sum_eq_single p]`. Establish `hp : p.val + 1 < n` using `h ▸ q.isLt`. Rewrite using `[dif_pos hp]`. Unfold `cmonoE`.

Rewrite using `[if_pos ⟨rfl, Fin.ext h.symm⟩]`. Introduce `a _ hne split_ifs with h1`. Unfold `cmonoE`. Rewrite using `[if_neg (fun hh => hne hh.1)]`. Both sides reduce to the same expression.

Introduce `hh`. Conclude with `absurd (Finset.mem_univ p) hh`.
-/
theorem cmono_supSum_succ (p q : Fin n) (y : K) (h : q.val = p.val + 1) : supSum (cmonoE p q y) = y := by
  unfold supSum
  rw [Finset.sum_eq_single p]
  · have hp : p.val + 1 < n := h ▸ q.isLt
    rw [dif_pos hp]
    unfold cmonoE
    rw [if_pos ⟨rfl, Fin.ext h.symm⟩]
  · intro a _ hne
    split_ifs with h1
    · unfold cmonoE
      rw [if_neg (fun hh => hne hh.1)]
    · rfl
  · intro hh
    exact absurd (Finset.mem_univ p) hh

/- English proof (translation)
Unfold `supSum`. Use `Finset.sum_eq_zero (fun a _ => ?_)` and prove the remaining obligations. Use `split_ifs with h1`. Unfold `cmonoE`. Rewrite using `[if_neg]`.

Introduce and unpack `⟨rfl, h2⟩`. Conclude with `h (by rw [← h2])`. Both sides reduce to the same expression.
-/
theorem cmono_supSum_ne (p q : Fin n) (y : K) (h : q.val ≠ p.val + 1) : supSum (cmonoE p q y) = 0 := by
  unfold supSum
  refine Finset.sum_eq_zero (fun a _ => ?_)
  split_ifs with h1
  · unfold cmonoE
    rw [if_neg]
    rintro ⟨rfl, h2⟩
    exact h (by rw [← h2])
  · rfl

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (σ j)]`. Simplify using `only [Matrix.conjTranspose_apply, cmonoE, mono, if_true]`. Distinguish the cases in `h1 : i = q ∧ j = b`. Take `⟨rfl, rfl⟩` from `h1`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h1, if_neg, star_zero, zero_mul]`. Introduce and unpack `⟨h2, h3⟩`. Conclude with `h1 ⟨h3, hσ h2⟩`. Introduce `k _ hk`. Simplify using `only [mono]`.

Rewrite using `[if_neg hk, mul_zero]`. Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`.
-/
theorem cmono_left [StarRing K] (σ : Fin n → Fin n) (t : Fin n → K) (hσ : Function.Injective σ) (b : Fin n) (q : Fin n)
    (y : K) (i j : Fin n) :
    ((cmonoE (σ b) q y)ᴴ * mono σ t) i j = if i = q ∧ j = b then star y * t b else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ j)]
  · simp only [Matrix.conjTranspose_apply, cmonoE, mono, if_true]
    by_cases h1 : i = q ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h1
      simp
    · rw [if_neg h1, if_neg, star_zero, zero_mul]
      rintro ⟨h2, h3⟩
      exact h1 ⟨h3, hσ h2⟩
  · intro k _ hk
    simp only [mono]
    rw [if_neg hk, mul_zero]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single c]`. Simplify using `only [cmonoE, mono, true_and]`. Distinguish the cases in `h1 : i = σ c`. Distinguish the cases in `h2 : j = b`. Simplify using `[h1, h2]`.

Simplify using `[h1, h2]`. Simplify using `[h1]`. Introduce `k _ hk`. Simplify using `only [cmonoE]`. Rewrite using `[if_neg (fun hh => hk hh.1), mul_zero]`.

Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`.
-/
theorem cmono_right (σ : Fin n → Fin n) (t : Fin n → K) (c b : Fin n) (x : K) (i j : Fin n) :
    (mono σ t * cmonoE c b x) i j = if i = σ c ∧ j = b then t c * x else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single c]
  · simp only [cmonoE, mono, true_and]
    by_cases h1 : i = σ c
    · by_cases h2 : j = b
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]
  · intro k _ hk
    simp only [cmonoE]
    rw [if_neg (fun hh => hk hh.1), mul_zero]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

end

/- English proof (translation)
Introduce `K _ _ n σ t hσ ht hrel c b hcb hv`. Establish `htb : t b ≠ 0` using `ht b`. Establish `htc : t c ≠ 0` using `ht c`. Establish `hlt : σ b < σ c` using `Fin.lt_def.2 (by omega)`. Use `set y : K := star (-(t c / t b)) with hy`.

Establish `hsy : star y * t b + t c * 1 = 0`. Rewrite using `[hy, star_star]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hR : (cmonoE (σ b) (σ c) y)ᴴ * mono σ t + mono σ t * cmonoE c b 1 = 0`.

Use extensionality with `i j`. Rewrite using `[Matrix.add_apply, cmono_left σ t hσ.1, cmono_right, Matrix.zero_apply]`. Distinguish the cases in `h : i = σ c ∧ j = b`. Rewrite using `[if_pos h, if_pos h, hsy]`. Rewrite using `[if_neg h, if_neg h, add_zero]`.

Establish `h` using `hrel _ _ (cmono_strict (σ b) (σ c) y hlt) (cmono_strict c b 1 hcb) hR`. Rewrite `h` using `[cmono_supSum_succ (σ b) (σ c) y hv]`. Establish `hy0 : y ≠ 0`. Rewrite using `[hy]`. Introduce `h0`.

Establish `h1 : -(t c / t b) = 0` using `by simpa using h0`. Conclude with `(div_ne_zero htc htb) (neg_eq_zero.1 h1)`. Distinguish the cases in `hb : b.val = c.val + 1`. Use `⟨hb, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[cmono_supSum_succ c b 1 hb, star_one]`.

Rewrite `hsy` using `[h, star_one, one_mul, mul_one]`. Conclude with `eq_neg_of_add_eq_zero_left hsy`. Rewrite `h` using `[cmono_supSum_ne c b 1 hb, star_zero]`. Conclude with `absurd h hy0`.
-/
theorem cell_mono : RelevantMonomialConsecutive := by
  intro K _ _ n σ t hσ ht hrel c b hcb hv
  have htb : t b ≠ 0 := ht b
  have htc : t c ≠ 0 := ht c
  have hlt : σ b < σ c := Fin.lt_def.2 (by omega)

  set y : K := star (-(t c / t b)) with hy
  have hsy : star y * t b + t c * 1 = 0 := by
    rw [hy, star_star]
    field_simp
    ring
  have hR : (cmonoE (σ b) (σ c) y)ᴴ * mono σ t + mono σ t * cmonoE c b 1 = 0 := by
    ext i j
    rw [Matrix.add_apply, cmono_left σ t hσ.1, cmono_right, Matrix.zero_apply]
    by_cases h : i = σ c ∧ j = b
    · rw [if_pos h, if_pos h, hsy]
    · rw [if_neg h, if_neg h, add_zero]
  have h := hrel _ _ (cmono_strict (σ b) (σ c) y hlt) (cmono_strict c b 1 hcb) hR
  rw [cmono_supSum_succ (σ b) (σ c) y hv] at h
  have hy0 : y ≠ 0 := by
    rw [hy]
    intro h0
    have h1 : -(t c / t b) = 0 := by simpa using h0
    exact (div_ne_zero htc htb) (neg_eq_zero.1 h1)
  by_cases hb : b.val = c.val + 1
  · refine ⟨hb, ?_⟩
    rw [cmono_supSum_succ c b 1 hb, star_one] at h
    rw [h, star_one, one_mul, mul_one] at hsy
    exact eq_neg_of_add_eq_zero_left hsy
  · rw [cmono_supSum_ne c b 1 hb, star_zero] at h
    exact absurd h hy0

end Formalism.MainNotions.BridgeLemma

end
