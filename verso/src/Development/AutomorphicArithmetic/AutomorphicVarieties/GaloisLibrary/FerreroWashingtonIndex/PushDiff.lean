import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Introduce `k _ M m _ h N P g hg y`. Simplify using `only [push]`. Establish `shift : (∑ s ∈ Finset.univ.filter (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y - N), g s) = ∑ s ∈ Finset.univ.filter (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y), g (s - N)`. Apply `Finset.sum_nbij' (fun s : ZMod M => s + (N : ZMod M)) (fun s : ZMod M => s - (N : ZMod M))` to reduce the goal to its premises. Introduce `s hs`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢`. Rewrite using `[map_add, hs, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Introduce `s hs`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢`.

Rewrite using `[map_sub, hs, map_natCast]`. Introduce `s _`. Expand and normalize the polynomial expressions, which then agree. Introduce `s _`. Expand and normalize the polynomial expressions, which then agree.

Introduce `s _`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[shift, ← Finset.sum_sub_distrib]`. Repeatedly rewrite using `[hg]`.

Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[Finset.sum_ite_eq]`. Establish `key : (j : ZMod M) ∈ Finset.univ.filter (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y) ↔ (j : ZMod m) = y`.

Rewrite using `[Finset.mem_filter, ZMod.castHom_apply, ZMod.cast_natCast h]`. Simplify using the standard rewrite rules. Distinguish the cases in `hj : (j : ZMod m) = y`. Rewrite using `[if_pos (key.mpr hj), if_pos hj]`. Rewrite using `[if_neg (fun t => hj (key.mp t)), if_neg hj]`.
-/
theorem UpperTheory.V.FW.pushDiff :
    ∀ (k : Type) [CommRing k] (M m : ℕ) [NeZero M] (h : m ∣ M) (N : ℕ) (P : ℕ → k) (g : ZMod M → k), (∀ s, g s - g (s - N) = ∑ j ∈ Finset.range N, if (j : ZMod M) = s then P j else 0) → ∀ y : ZMod m, push h g y - push h g (y - N) = ∑ j ∈ Finset.range N, if (j : ZMod m) = y then P j else 0 := by
  intro k _ M m _ h N P g hg y
  simp only [push]
  have shift : (∑ s ∈ Finset.univ.filter (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y - N), g s)
      = ∑ s ∈ Finset.univ.filter (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y), g (s - N) := by
    apply Finset.sum_nbij' (fun s : ZMod M => s + (N : ZMod M)) (fun s : ZMod M => s - (N : ZMod M))
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [map_add, hs, map_natCast]
      ring
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [map_sub, hs, map_natCast]
    · intro s _
      ring
    · intro s _
      ring
    · intro s _
      congr 1
      ring
  rw [shift, ← Finset.sum_sub_distrib]
  simp_rw [hg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_ite_eq]
  have key : (j : ZMod M) ∈ Finset.univ.filter
      (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y) ↔ (j : ZMod m) = y := by
    rw [Finset.mem_filter, ZMod.castHom_apply, ZMod.cast_natCast h]
    simp
  by_cases hj : (j : ZMod m) = y
  · rw [if_pos (key.mpr hj), if_pos hj]
  · rw [if_neg (fun t => hj (key.mp t)), if_neg hj]
