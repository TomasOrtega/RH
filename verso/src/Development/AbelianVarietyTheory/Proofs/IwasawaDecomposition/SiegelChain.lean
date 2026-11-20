import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront

namespace GlobalTheory.SiegelChain

/- English proof (translation)
Introduce `n d u h m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `i j hij`. Establish `: i = j` using `Fin.ext (by simpa using hij.symm)`.

Substitute `this` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `i j hij`. Establish `hk : (i : ℕ) + m < n` using `by have := j.isLt; omega`.

Set `k : Fin n` to `⟨(i : ℕ) + m, hk⟩`. Establish `h1 : d i ≤ 4 ^ m * d k` using `ih i k rfl`. Establish `h2 : d k ≤ 4 * d j` using `h.step k j (by simp [k]; omega)`. Establish `h4 : (0 : ℝ) ≤ 4 ^ m` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem siegel_chain : ∀ {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ}, GlobalTheory.RedTh.IsSiegel d u →
    ∀ (m : ℕ) (i j : Fin n), (↑j : ℕ) = (↑i : ℕ) + m → d i ≤ (4 : ℝ) ^ m * d j := by
  intro n d u h m
  induction m with
  | zero =>
    intro i j hij
    have : i = j := Fin.ext (by simpa using hij.symm)
    subst this
    simp
  | succ m ih =>
    intro i j hij
    have hk : (i : ℕ) + m < n := by have := j.isLt; omega
    let k : Fin n := ⟨(i : ℕ) + m, hk⟩
    have h1 : d i ≤ 4 ^ m * d k := ih i k rfl
    have h2 : d k ≤ 4 * d j := h.step k j (by simp [k]; omega)
    have h4 : (0 : ℝ) ≤ 4 ^ m := by positivity
    calc d i ≤ 4 ^ m * d k := h1
      _ ≤ 4 ^ m * (4 * d j) := mul_le_mul_of_nonneg_left h2 h4
      _ = 4 ^ (m + 1) * d j := by ring

end GlobalTheory.SiegelChain
