import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.Metric.Telescope

/- English proof (translation)
Introduce `N M _ f i`. Take `⟨n, hn⟩` from `i`. Proceed by induction on `n with`. Consider the case `zero`. Establish `hset : Finset.Iic (⟨0, hn⟩ : Fin N) = {⟨0, hn⟩}`.

Use extensionality with `k`. Simplify using `only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_iff_val_le_val, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hset, Finset.sum_singleton, dif_pos rfl, neg_neg]`. Consider the case `succ n ih`.

Establish `hn' : n < N` using `by omega`. Establish `hset : Finset.Iic (⟨n + 1, hn⟩ : Fin N) = insert ⟨n + 1, hn⟩ (Finset.Iic ⟨n, hn'⟩)`. Use extensionality with `k`. Simplify using `only [Finset.mem_Iic, Finset.mem_insert, Fin.le_iff_val_le_val, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.

Establish `hnot : (⟨n + 1, hn⟩ : Fin N) ∉ Finset.Iic ⟨n, hn'⟩`. Simplify using `only [Finset.mem_Iic, Fin.le_iff_val_le_val, not_le]`. Use linear arithmetic over natural numbers and integers. Establish `hs` using `(neg_eq_iff_eq_neg.mpr (ih hn')).symm`. Rewrite using `[hset, Finset.sum_insert hnot, dif_neg (by simp), hs]`.

Establish `e : ∀ p, f ⟨(⟨n + 1, hn⟩ : Fin N).val - 1, p⟩ = f ⟨n, hn'⟩` using `fun p => congrArg f (Fin.ext (by simp))`. Rewrite using `[e]`. Normalize the expressions using the abelian group laws.
-/
theorem fin_iic_telescope : ∀ (N : ℕ) (M : Type) [AddCommGroup M] (f : Fin N → M) (i : Fin N),
    f i = -∑ k ∈ Finset.Iic i, (if h : (k : ℕ) = 0 then -f k else
      f ⟨(k : ℕ) - 1, by have := k.2; omega⟩ - f k) := by
  intro N M _ f i
  obtain ⟨n, hn⟩ := i
  induction n with
  | zero =>
    have hset : Finset.Iic (⟨0, hn⟩ : Fin N) = {⟨0, hn⟩} := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    rw [hset, Finset.sum_singleton, dif_pos rfl, neg_neg]
  | succ n ih =>
    have hn' : n < N := by omega
    have hset : Finset.Iic (⟨n + 1, hn⟩ : Fin N) = insert ⟨n + 1, hn⟩ (Finset.Iic ⟨n, hn'⟩) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    have hnot : (⟨n + 1, hn⟩ : Fin N) ∉ Finset.Iic ⟨n, hn'⟩ := by
      simp only [Finset.mem_Iic, Fin.le_iff_val_le_val, not_le]
      omega
    have hs := (neg_eq_iff_eq_neg.mpr (ih hn')).symm
    rw [hset, Finset.sum_insert hnot, dif_neg (by simp), hs]
    have e : ∀ p, f ⟨(⟨n + 1, hn⟩ : Fin N).val - 1, p⟩ = f ⟨n, hn'⟩ :=
      fun p => congrArg f (Fin.ext (by simp))
    rw [e]
    abel

end GlobalTheory.CompanionTheory.Metric.Telescope
