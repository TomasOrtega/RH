import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock

/- English proof (translation)
Establish `hd : Disjoint (univ.filter fun a => lev a < k) (univ.filter fun a => lev a = k)`. Use `Finset.disjoint_left.2 fun a ha hb => ?_` and prove the remaining obligations. Simplify using `only [mem_filter, mem_univ, true_and] at ha hb`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← Finset.card_union_of_disjoint hd]`.

Use `congr 1`. Use extensionality with `a`. Simplify using `only [mem_filter, mem_univ, true_and, mem_union]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_lev_lt_succ {n : ℕ} (lev : Fin n → ℕ) (k : ℕ) :
    (univ.filter fun a => lev a < k + 1).card =
      (univ.filter fun a => lev a < k).card + (univ.filter fun a => lev a = k).card := by
  have hd : Disjoint (univ.filter fun a => lev a < k) (univ.filter fun a => lev a = k) := by
    refine Finset.disjoint_left.2 fun a ha hb => ?_
    simp only [mem_filter, mem_univ, true_and] at ha hb
    omega
  rw [← Finset.card_union_of_disjoint hd]
  congr 1
  ext a
  simp only [mem_filter, mem_univ, true_and, mem_union]
  omega

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro hk`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `hk`. Rewrite using `[Fin.sum_univ_castSucc, card_lev_lt_succ, ← ih (by omega)]`. Both sides reduce to the same expression.
-/
theorem sum_sz_castLE {n M : ℕ} (lev : Fin n → ℕ) : ∀ (k : ℕ) (hk : k ≤ M),
    ∑ b : Fin k, sz lev M (Fin.castLE hk b) = (univ.filter fun a => lev a < k).card := by
  intro k
  induction k with
  | zero => intro hk; simp
  | succ k ih =>
    intro hk
    rw [Fin.sum_univ_castSucc, card_lev_lt_succ, ← ih (by omega)]
    rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hn`. Establish `hs : (univ.filter fun b => lev b < k) ⊆ Finset.Iio a`. Introduce `b hb`.

Simplify using `only [mem_filter, mem_univ, true_and] at hb`. Conclude with `Finset.mem_Iio.2 (hm.reflect_lt (by omega))`. Use `Finset.card_le_card hs` as an intermediate fact. Rewrite `this` using `[Fin.card_Iio]`. Use linear arithmetic over natural numbers and integers.

Introduce `h`. Establish `hs : Finset.Iic a ⊆ (univ.filter fun b => lev b < k)`. Introduce `b hb`. Simplify using `only [mem_filter, mem_univ, true_and]`. Conclude with `lt_of_le_of_lt (hm (Finset.mem_Iic.1 hb)) h`.

Use `Finset.card_le_card hs` as an intermediate fact. Rewrite `this` using `[Fin.card_Iic]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lt_card_iff {n : ℕ} {lev : Fin n → ℕ} (hm : Monotone lev) (k : ℕ) (a : Fin n) :
    (a : ℕ) < (univ.filter fun b => lev b < k).card ↔ lev a < k := by
  constructor
  · intro h
    by_contra hn
    have hs : (univ.filter fun b => lev b < k) ⊆ Finset.Iio a := by
      intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      exact Finset.mem_Iio.2 (hm.reflect_lt (by omega))
    have := Finset.card_le_card hs
    rw [Fin.card_Iio] at this
    omega
  · intro h
    have hs : Finset.Iic a ⊆ (univ.filter fun b => lev b < k) := by
      intro b hb
      simp only [mem_filter, mem_univ, true_and]
      exact lt_of_le_of_lt (hm (Finset.mem_Iic.1 hb)) h
    have := Finset.card_le_card hs
    rw [Fin.card_Iic] at this
    omega

/- English proof (translation)
Establish `hv` using `stdBlocks_val (sz lev M) h i p`. Rewrite `hv` using `[sum_sz_castLE lev (i : ℕ) i.2.le]`. Establish `hp : (p : ℕ) < (univ.filter fun a => lev a = (i : ℕ)).card` using `p.2`. Establish `h1` using `lt_card_iff hm (i : ℕ) (stdBlocks (sz lev M) h ⟨i, p⟩)`. Establish `h2` using `lt_card_iff hm ((i : ℕ) + 1) (stdBlocks (sz lev M) h ⟨i, p⟩)`.

Rewrite `h2` using `[card_lev_lt_succ]`. Establish `h3` using `h2.1 (by omega)`. Establish `h4 : ¬ lev (stdBlocks (sz lev M) h ⟨i, p⟩) < (i : ℕ)` using `fun hl => by`. Use `h1.2 hl` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers.
-/
theorem lev_stdBlocks {n M : ℕ} (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n) (hm : Monotone lev)
    (i : Fin M) (p : Fin (sz lev M i)) : lev (stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ) := by
  have hv := stdBlocks_val (sz lev M) h i p
  rw [sum_sz_castLE lev (i : ℕ) i.2.le] at hv
  have hp : (p : ℕ) < (univ.filter fun a => lev a = (i : ℕ)).card := p.2
  have h1 := lt_card_iff hm (i : ℕ) (stdBlocks (sz lev M) h ⟨i, p⟩)
  have h2 := lt_card_iff hm ((i : ℕ) + 1) (stdBlocks (sz lev M) h ⟨i, p⟩)
  rw [card_lev_lt_succ] at h2
  have h3 := h2.1 (by omega)
  have h4 : ¬ lev (stdBlocks (sz lev M) h ⟨i, p⟩) < (i : ℕ) := fun hl => by
    have := h1.2 hl
    omega
  omega

/- English proof (translation)
Introduce `n M lev h hm _`. Use `⟨lev_stdBlocks lev h hm, fun f i => ?_⟩` and prove the remaining obligations. Use `Finset.sum_bij (fun p _ => stdBlocks (sz lev M) h ⟨i, p⟩) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p _`. Simplify using `only [mem_filter, mem_univ, true_and]`.

Conclude with `lev_stdBlocks lev h hm i p`. Introduce `p _ q _ hpq`. Use `(stdBlocks (sz lev M) h).injective hpq` as an intermediate fact. Simplify using `using this`. Introduce `a ha`.

Simplify using `only [mem_filter, mem_univ, true_and] at ha`. Take `⟨⟨j, q⟩, rfl⟩` from `(stdBlocks (sz lev M) h).surjective a`. Establish `hj : j = i` using `Fin.ext ((lev_stdBlocks lev h hm j q).symm.trans ha)`. Substitute `hj` using the available equality. Conclude with `⟨q, mem_univ _, rfl⟩`.

Introduce `p _`. Both sides reduce to the same expression.
-/
theorem stdBlocks_clusters : ∀ (n M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n), Monotone lev → (∀ a, lev a < M) →
    (∀ (i : Fin M) (p : Fin (sz lev M i)), lev (stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ)) ∧
    ∀ (f : Fin n → ℂ) (i : Fin M), ∑ p : Fin (sz lev M i), f (stdBlocks (sz lev M) h ⟨i, p⟩) =
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), f a := by
  intro n M lev h hm _
  refine ⟨lev_stdBlocks lev h hm, fun f i => ?_⟩
  refine Finset.sum_bij (fun p _ => stdBlocks (sz lev M) h ⟨i, p⟩) ?_ ?_ ?_ ?_
  · intro p _
    simp only [mem_filter, mem_univ, true_and]
    exact lev_stdBlocks lev h hm i p
  · intro p _ q _ hpq
    have := (stdBlocks (sz lev M) h).injective hpq
    simpa using this
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    obtain ⟨⟨j, q⟩, rfl⟩ := (stdBlocks (sz lev M) h).surjective a
    have hj : j = i := Fin.ext ((lev_stdBlocks lev h hm j q).symm.trans ha)
    subst hj
    exact ⟨q, mem_univ _, rfl⟩
  · intro p _
    rfl

end GlobalTheory.CompanionTheory.RgCOBlock
