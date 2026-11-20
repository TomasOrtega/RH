import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

open Finset MvPolynomial UpperTheory.Gal.Schur

/- English proof (translation)
Introduce `h R _ n g i`. Establish `key` using `h R n (fun a b => g a - g b) i`. Establish `h1 : ∀ k ∈ univ.erase i, (if k < i then g k - g i else g i - g k) = (if k < i then (-1 : R) else 1) * (g i - g k)`. Introduce `k _`. Apply the tactic sequence `split_ifs <;> ring`.

Establish `h2 : ∏ k ∈ univ.erase i, (if k < i then (-1 : R) else 1) = (-1) ^ (i : ℕ)`. Establish `hf : (univ.erase i).filter (· < i) = Finset.Iio i`. Use extensionality with `k`. Simplify using `only [mem_filter, mem_erase, mem_univ, and_true, mem_Iio]`. Conclude with `⟨fun hk => hk.2, fun hk => ⟨ne_of_lt hk, hk⟩⟩`.

Rewrite using `[Finset.prod_ite, prod_const, prod_const_one, mul_one, hf, Fin.card_Iio]`. Unfold `vdm vdmAway`. Rewrite using `[key, Finset.prod_congr rfl h1, Finset.prod_mul_distrib, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Gal.Schur.vdmSplit_of :
    PairSplit → VdmSplit := by
  intro h R _ n g i
  have key := h R n (fun a b => g a - g b) i
  have h1 : ∀ k ∈ univ.erase i, (if k < i then g k - g i else g i - g k) =
      (if k < i then (-1 : R) else 1) * (g i - g k) := by
    intro k _
    split_ifs <;> ring
  have h2 : ∏ k ∈ univ.erase i, (if k < i then (-1 : R) else 1) = (-1) ^ (i : ℕ) := by
    have hf : (univ.erase i).filter (· < i) = Finset.Iio i := by
      ext k
      simp only [mem_filter, mem_erase, mem_univ, and_true, mem_Iio]
      exact ⟨fun hk => hk.2, fun hk => ⟨ne_of_lt hk, hk⟩⟩
    rw [Finset.prod_ite, prod_const, prod_const_one, mul_one, hf, Fin.card_Iio]
  unfold vdm vdmAway
  rw [key, Finset.prod_congr rfl h1, Finset.prod_mul_distrib, h2]
  ring
