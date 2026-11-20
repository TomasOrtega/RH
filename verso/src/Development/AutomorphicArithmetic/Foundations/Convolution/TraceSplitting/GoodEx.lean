import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit

/- English proof (translation)
Introduce `n hn`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Use `set S : ℤ := ∑ k : Fin m, ((m : ℤ) + 1 - (k : ℕ)) with hS`. Establish `hS0 : 0 ≤ S`. Use `Finset.sum_nonneg fun k _ => ?_` and prove the remaining obligations.

Use `k.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Set `ν : Fin (m + 1) → ℤ` to `fun i => if i = Fin.last m then -S else (m : ℤ) + 1 - (i : ℕ)`. Establish `hlast : ν (Fin.last m) = -S` using `by simp [ν]`. Establish `hcast : ∀ k : Fin m, ν k.castSucc = (m : ℤ) + 1 - (k : ℕ)`.

Introduce `k`. Establish `: k.castSucc ≠ Fin.last m` using `(Fin.castSucc_lt_last k).ne`. Simplify using `[ν, this]`. Establish `hne : ∀ i : Fin (m + 1), i ≠ Fin.last m → ν i = (m : ℤ) + 1 - (i : ℕ)`. Introduce `i hi`.

Simplify using `[ν, hi]`. Establish `hpos : ∀ i : Fin (m + 1), i ≠ Fin.last m → 0 < ν i`. Introduce `i hi`. Rewrite using `[hne i hi]`. Use `i.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hsum : ∑ i, ν i = 0`. Rewrite using `[Fin.sum_univ_castSucc, hlast]`. Simplify using `only [hcast]`. Rewrite using `[← hS]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hJ : ∀ J : Finset (Fin (m + 1)), J.Nonempty → Fin.last m ∉ J → 0 < ∑ i ∈ J, ν i`. Introduce `J hJ hl`. Use `Finset.sum_pos (fun i hi => hpos i ?_) hJ` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `hl hi`. Use `⟨ν, ?_, hsum, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Distinguish the cases in `hj : j = Fin.last m`. Establish `hi : i ≠ Fin.last m`.

Introduce and unpack `rfl`. Substitute `hj` using the available equality. Conclude with `lt_irrefl _ hij`. Establish `h1` using `hpos i hi`. Establish `h2 : ν j = -S` using `by rw [hj, hlast]`.

Use `show ν j < ν i`. Use linear arithmetic over natural numbers and integers. Establish `hi : i ≠ Fin.last m`. Introduce and unpack `rfl`. Conclude with `absurd (Fin.le_last j) (not_le.mpr hij)`.

Use `show ν j < ν i`. Rewrite using `[hne i hi, hne j hj]`. Establish `: (i : ℕ) < (j : ℕ)` using `hij`. Use linear arithmetic over natural numbers and integers. Introduce `J hJne hJu`.

Distinguish the cases in `hl : Fin.last m ∈ J`. Establish `hc : Jᶜ.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce `h`. Conclude with `hJu (by simpa using h)`.

Establish `h1` using `hJ Jᶜ hc (by simpa using hl)`. Establish `h2 : ∑ i ∈ J, ν i + ∑ i ∈ Jᶜ, ν i = 0`. Rewrite using `[Finset.sum_add_sum_compl, hsum]`. Use linear arithmetic over natural numbers and integers. Conclude with `(hJ J hJne hl).ne'`.
-/
theorem UpperTheory.ConvolutionTheory.T.goodEx :
    UpperTheory.ConvolutionTheory.T.GoodEx := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set S : ℤ := ∑ k : Fin m, ((m : ℤ) + 1 - (k : ℕ)) with hS
  have hS0 : 0 ≤ S := by
    refine Finset.sum_nonneg fun k _ => ?_
    have := k.isLt
    omega
  let ν : Fin (m + 1) → ℤ := fun i => if i = Fin.last m then -S else (m : ℤ) + 1 - (i : ℕ)
  have hlast : ν (Fin.last m) = -S := by simp [ν]
  have hcast : ∀ k : Fin m, ν k.castSucc = (m : ℤ) + 1 - (k : ℕ) := by
    intro k
    have : k.castSucc ≠ Fin.last m := (Fin.castSucc_lt_last k).ne
    simp [ν, this]
  have hne : ∀ i : Fin (m + 1), i ≠ Fin.last m → ν i = (m : ℤ) + 1 - (i : ℕ) := by
    intro i hi
    simp [ν, hi]
  have hpos : ∀ i : Fin (m + 1), i ≠ Fin.last m → 0 < ν i := by
    intro i hi
    rw [hne i hi]
    have := i.isLt
    omega
  have hsum : ∑ i, ν i = 0 := by
    rw [Fin.sum_univ_castSucc, hlast]
    simp only [hcast]
    rw [← hS]
    ring
  have hJ : ∀ J : Finset (Fin (m + 1)), J.Nonempty → Fin.last m ∉ J → 0 < ∑ i ∈ J, ν i := by
    intro J hJ hl
    refine Finset.sum_pos (fun i hi => hpos i ?_) hJ
    rintro rfl
    exact hl hi
  refine ⟨ν, ?_, hsum, ?_⟩
  · intro i j hij
    by_cases hj : j = Fin.last m
    · have hi : i ≠ Fin.last m := by
        rintro rfl
        subst hj
        exact lt_irrefl _ hij
      have h1 := hpos i hi
      have h2 : ν j = -S := by rw [hj, hlast]
      show ν j < ν i
      omega
    · have hi : i ≠ Fin.last m := by
        rintro rfl
        exact absurd (Fin.le_last j) (not_le.mpr hij)
      show ν j < ν i
      rw [hne i hi, hne j hj]
      have : (i : ℕ) < (j : ℕ) := hij
      omega
  · intro J hJne hJu
    by_cases hl : Fin.last m ∈ J
    · have hc : Jᶜ.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        exact hJu (by simpa using h)
      have h1 := hJ Jᶜ hc (by simpa using hl)
      have h2 : ∑ i ∈ J, ν i + ∑ i ∈ Jᶜ, ν i = 0 := by
        rw [Finset.sum_add_sum_compl, hsum]
      omega
    · exact (hJ J hJne hl).ne'
