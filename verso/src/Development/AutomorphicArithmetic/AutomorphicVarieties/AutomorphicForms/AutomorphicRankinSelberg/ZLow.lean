import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

/- English proof (translation)
Introduce `hB hL hW L _ s hs z hz`. Establish `hs' : s ∈ Set.Icc (1 : ℝ) 2` using `⟨hs.1.le, hs.2⟩`. Take `⟨-, h0, -, -, -, hub⟩` from `hB s hs'`. Establish `hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s))` using `hW.1 (2 * s) (by linarith [hs.1])`. Establish `hk : Summable fun x : Fin 2 → ℤ => UpperTheory.V.Af.Rs.ker s x z` using `Summable.of_nonneg_of_le (fun x => h0 x z) (fun x => hub x z hz) (hsum.mul_left _)`.

Establish `hv : ∀ v ∈ (Finset.univ : Finset (Fin 2 → ZMod L)), Summable fun x : Fin 2 → ℤ => if UpperTheory.V.Af.Rs.cls L x = v then UpperTheory.V.Af.Rs.ker s x z else 0`. Introduce `v _`. Use `Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hk` and prove the remaining obligations. Use `split_ifs`. Conclude with `h0 x z`.

Conclude with `le_rfl`. Use `split_ifs`. Conclude with `le_rfl`. Conclude with `h0 x z`. Establish `he : ∑ v, UpperTheory.V.Af.Rs.Zc L v s z = ∑' x : Fin 2 → ℤ, UpperTheory.V.Af.Rs.ker s x z`.

Unfold `UpperTheory.V.Af.Rs.Zc`. Rewrite using `[← Summable.tsum_finsetSum hv]`. Use `tsum_congr fun x => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[he, UpperTheory.V.Af.Rs.Wsum, ← tsum_mul_left]`.

Conclude with `(hsum.mul_left _).tsum_le_tsum (fun x => hL s hs' x z hz) hk`.
-/
theorem UpperTheory.V.Af.Rs.zLow :
    UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.KerLow → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZLow := by
  intro hB hL hW L _ s hs z hz
  have hs' : s ∈ Set.Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨-, h0, -, -, -, hub⟩ := hB s hs'
  have hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) := hW.1 (2 * s) (by linarith [hs.1])
  have hk : Summable fun x : Fin 2 → ℤ => UpperTheory.V.Af.Rs.ker s x z :=
    Summable.of_nonneg_of_le (fun x => h0 x z) (fun x => hub x z hz) (hsum.mul_left _)
  have hv : ∀ v ∈ (Finset.univ : Finset (Fin 2 → ZMod L)), Summable fun x : Fin 2 → ℤ =>
      if UpperTheory.V.Af.Rs.cls L x = v then UpperTheory.V.Af.Rs.ker s x z else 0 := by
    intro v _
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hk
    · split_ifs
      · exact h0 x z
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact h0 x z
  have he : ∑ v, UpperTheory.V.Af.Rs.Zc L v s z = ∑' x : Fin 2 → ℤ, UpperTheory.V.Af.Rs.ker s x z := by
    unfold UpperTheory.V.Af.Rs.Zc
    rw [← Summable.tsum_finsetSum hv]
    refine tsum_congr fun x => ?_
    simp
  rw [he, UpperTheory.V.Af.Rs.Wsum, ← tsum_mul_left]
  exact (hsum.mul_left _).tsum_le_tsum (fun x => hL s hs' x z hz) hk
