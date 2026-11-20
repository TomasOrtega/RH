import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.TwoUpOKOf

namespace UpperTheory.Gal.TP.Sub

open Formalism.BasicNotions

/- English proof (translation)
Rewrite using `[Fin.univ_val_map, List.ofFn_add, ← Multiset.coe_add, Fin.univ_val_map, Fin.univ_val_map]`. Both sides reduce to the same expression.
-/
private theorem multiset_map_fin_add_eq_add {n t : ℕ} (f : Fin (n + t) → ℤ) :
    Multiset.map f Finset.univ.val =
      Multiset.map (fun k : Fin n => f (Fin.castAdd t k)) Finset.univ.val +
        Multiset.map (fun i : Fin t => f (Fin.natAdd n i)) Finset.univ.val := by
  rw [Fin.univ_val_map, List.ofFn_add, ← Multiset.coe_add, Fin.univ_val_map, Fin.univ_val_map]
  rfl

/- English proof (translation)
Use `conv_lhs => rw [← Multiset.map_univ_val_equiv (Fin.revPerm : Equiv.Perm (Fin n)), Multiset.map_map]`. Both sides reduce to the same expression.
-/
private theorem multiset_map_fin_rev_eq {n : ℕ} (f : Fin n → ℤ) :
    Multiset.map f Finset.univ.val = Multiset.map (fun k : Fin n => f k.rev) Finset.univ.val := by
  conv_lhs => rw [← Multiset.map_univ_val_equiv (Fin.revPerm : Equiv.Perm (Fin n)), Multiset.map_map]
  rfl

/- English proof (translation)
Introduce `n t lam lam' mX mW hL`. Use `⟨fun m p hm hp => ?_, fun m p hm hp => ?_⟩` and prove the remaining obligations. Unfold `wtJumps`. Rewrite using `[multiset_map_fin_add_eq_add]`. Use `congr 1`.

Rewrite using `[Multiset.map_map]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Establish `h1` using `hL (Fin.castAdd t k)`. Simplify using `only [Fin.coe_castAdd, k.2, dif_pos, Fin.eta] at h1`.

Simplify using `only [Function.comp_apply, Fin.coe_castAdd]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[multiset_map_fin_rev_eq (fun i : Fin t => -p i)]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Establish `h1` using `hL (Fin.natAdd n i)`. Establish `h2` using `hp i.rev`. Simplify using `only [Fin.coe_natAdd, Fin.val_rev] at h1 h2 ⊢`. Rewrite `h1` using `[dif_neg (by omega)]`. Establish `hi` using `i.2`.

Move the coercions through the operations in `at h1`. Use linear arithmetic over natural numbers and integers. Unfold `wtJumps`. Rewrite using `[multiset_map_fin_rev_eq, multiset_map_fin_rev_eq (fun k : Fin n => ((k : ℕ) : ℤ) - lam.dual.w k)]`. Simplify using `only [DomWeight.dual, Fin.rev_rev, Fin.val_rev]`.

Rewrite using `[multiset_map_fin_add_eq_add]`. Use `congr 1`. Rewrite using `[Multiset.map_map]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Establish `h1` using `hL (Fin.castAdd t k)`. Simplify using `only [Fin.coe_castAdd, k.2, dif_pos, Fin.eta] at h1`. Simplify using `only [Function.comp_apply, Fin.coe_castAdd]`. Establish `hk` using `k.2`. Use linear arithmetic over natural numbers and integers.

Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `h1` using `hL (Fin.natAdd n i)`. Establish `h2` using `hp i`. Simplify using `only [Fin.coe_natAdd] at h1 h2 ⊢`.

Rewrite `h1` using `[dif_neg (by omega)]`. Establish `hi` using `i.2`. Establish `hc : ((n + t - (n + (i : ℕ) + 1) : ℕ) : ℤ) = (t : ℤ) - 1 - (i : ℕ)`. Rewrite using `[Nat.cast_sub (by omega)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Move the coercions through the operations in `at h1`. Rewrite using `[hc]`. Use linear arithmetic over natural numbers and integers.
-/
theorem wtId_holds : WtId := by
  intro n t lam lam' mX mW hL
  refine ⟨fun m p hm hp => ?_, fun m p hm hp => ?_⟩
  · unfold wtJumps
    rw [multiset_map_fin_add_eq_add]
    congr 1
    · rw [Multiset.map_map]
      congr 1
      funext k
      have h1 := hL (Fin.castAdd t k)
      simp only [Fin.coe_castAdd, k.2, dif_pos, Fin.eta] at h1
      simp only [Function.comp_apply, Fin.coe_castAdd]
      omega
    · rw [multiset_map_fin_rev_eq (fun i : Fin t => -p i)]
      congr 1
      funext i
      have h1 := hL (Fin.natAdd n i)
      have h2 := hp i.rev
      simp only [Fin.coe_natAdd, Fin.val_rev] at h1 h2 ⊢
      rw [dif_neg (by omega)] at h1
      have hi := i.2
      push_cast at h1
      omega
  · unfold wtJumps
    rw [multiset_map_fin_rev_eq, multiset_map_fin_rev_eq (fun k : Fin n => ((k : ℕ) : ℤ) - lam.dual.w k)]
    simp only [DomWeight.dual, Fin.rev_rev, Fin.val_rev]
    rw [multiset_map_fin_add_eq_add]
    congr 1
    · rw [Multiset.map_map]
      congr 1
      funext k
      have h1 := hL (Fin.castAdd t k)
      simp only [Fin.coe_castAdd, k.2, dif_pos, Fin.eta] at h1
      simp only [Function.comp_apply, Fin.coe_castAdd]
      have hk := k.2
      omega
    · congr 1
      funext i
      have h1 := hL (Fin.natAdd n i)
      have h2 := hp i
      simp only [Fin.coe_natAdd] at h1 h2 ⊢
      rw [dif_neg (by omega)] at h1
      have hi := i.2
      have hc : ((n + t - (n + (i : ℕ) + 1) : ℕ) : ℤ) = (t : ℤ) - 1 - (i : ℕ) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      push_cast at h1
      rw [hc]
      omega

end UpperTheory.Gal.TP.Sub
