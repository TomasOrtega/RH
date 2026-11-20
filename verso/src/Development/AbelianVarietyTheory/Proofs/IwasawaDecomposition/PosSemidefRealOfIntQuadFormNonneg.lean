import Mathlib

namespace GlobalTheory

open Matrix

/- English proof (translation)
Introduce `g B hB hQ`. Use `set M : Matrix (Fin g) (Fin g) ℝ := B.map (Int.cast : ℤ → ℝ) with hM`. Use `set f : (Fin g → ℝ) → ℝ := fun x => dotProduct x (M.mulVec x) with hf`. Establish `hcont : Continuous f`. Simplify using `only [hf, dotProduct, mulVec]`.

Use `fun_prop`. Establish `hscale : ∀ (c : ℝ) (x : Fin g → ℝ), f (c • x) = c ^ 2 * f x`. Introduce `c x`. Simplify using `only [hf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hint : ∀ v : Fin g → ℤ, f (fun i => (v i : ℝ)) = ((dotProduct v (B.mulVec v) : ℤ) : ℝ)`. Introduce `v`. Simplify using `only [hf, hM, dotProduct, mulVec, Matrix.map_apply]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hrat : ∀ q : Fin g → ℚ, 0 ≤ f (fun i => (q i : ℝ))`. Introduce `q`. Use `set N : ℕ := ∏ i, (q i).den with hN`. Establish `hNpos : 0 < N` using `Finset.prod_pos (fun i _ => (q i).den_pos)`. Establish `hdvd : ∀ i, (q i).den ∣ N` using `fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)`.

Set `v : Fin g → ℤ` to `fun i => (q i).num * ((N / (q i).den : ℕ) : ℤ)`. Establish `hv : (N : ℝ) • (fun i => (q i : ℝ)) = fun i => (v i : ℝ)`. Use function extensionality and compare the values at `i`. Establish `hd : ((q i).den : ℝ) ≠ 0` using `by exact_mod_cast (q i).den_nz`. Simplify using `only [Pi.smul_apply, smul_eq_mul, v, Int.cast_mul, Int.cast_natCast]`.

Rewrite using `[Nat.cast_div (hdvd i) hd, Rat.cast_def]`. Clear the denominators using the available nonvanishing facts. Establish `h1` using `hscale (N : ℝ) (fun i => (q i : ℝ))`. Rewrite `h1` using `[hv, hint]`. Establish `h2 : (0 : ℝ) ≤ ((dotProduct v (B.mulVec v) : ℤ) : ℝ)` using `by exact_mod_cast hQ v`.

Establish `h3 : (0 : ℝ) < (N : ℝ) ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hdense : DenseRange (fun q : Fin g → ℚ => fun i => (q i : ℝ))` using `DenseRange.piMap (fun _ => Rat.denseRange_cast)`. Establish `hall : ∀ x : Fin g → ℝ, 0 ≤ f x`. Introduce `x`.

Establish `hclosed : IsClosed {x : Fin g → ℝ | 0 ≤ f x}` using `isClosed_le continuous_const hcont`. Establish `hsub : Set.range (fun q : Fin g → ℚ => fun i => (q i : ℝ)) ⊆ {x | 0 ≤ f x}`. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `hrat q`. Use `hdense.closure_range ▸ (closure_minimal hsub hclosed)` as an intermediate fact.

Conclude with `this (Set.mem_univ x)`. Use `posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `[hM, conjTranspose_apply, hB.apply i j]`. Simplify `hall x` using `[hf]`.
-/
theorem intSymm_posSemidef_real :
    ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℤ), B.IsSymm →
      (∀ v : Fin g → ℤ, 0 ≤ dotProduct v (B.mulVec v)) →
      (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  intro g B hB hQ
  set M : Matrix (Fin g) (Fin g) ℝ := B.map (Int.cast : ℤ → ℝ) with hM

  set f : (Fin g → ℝ) → ℝ := fun x => dotProduct x (M.mulVec x) with hf
  have hcont : Continuous f := by
    simp only [hf, dotProduct, mulVec]
    fun_prop
  have hscale : ∀ (c : ℝ) (x : Fin g → ℝ), f (c • x) = c ^ 2 * f x := by
    intro c x
    simp only [hf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hint : ∀ v : Fin g → ℤ, f (fun i => (v i : ℝ)) = ((dotProduct v (B.mulVec v) : ℤ) : ℝ) := by
    intro v
    simp only [hf, hM, dotProduct, mulVec, Matrix.map_apply]
    push_cast
    rfl
  have hrat : ∀ q : Fin g → ℚ, 0 ≤ f (fun i => (q i : ℝ)) := by
    intro q
    set N : ℕ := ∏ i, (q i).den with hN
    have hNpos : 0 < N := Finset.prod_pos (fun i _ => (q i).den_pos)
    have hdvd : ∀ i, (q i).den ∣ N := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    let v : Fin g → ℤ := fun i => (q i).num * ((N / (q i).den : ℕ) : ℤ)
    have hv : (N : ℝ) • (fun i => (q i : ℝ)) = fun i => (v i : ℝ) := by
      funext i
      have hd : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_nz
      simp only [Pi.smul_apply, smul_eq_mul, v, Int.cast_mul, Int.cast_natCast]
      rw [Nat.cast_div (hdvd i) hd, Rat.cast_def]
      field_simp
    have h1 := hscale (N : ℝ) (fun i => (q i : ℝ))
    rw [hv, hint] at h1
    have h2 : (0 : ℝ) ≤ ((dotProduct v (B.mulVec v) : ℤ) : ℝ) := by exact_mod_cast hQ v
    have h3 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    nlinarith
  have hdense : DenseRange (fun q : Fin g → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hall : ∀ x : Fin g → ℝ, 0 ≤ f x := by
    intro x
    have hclosed : IsClosed {x : Fin g → ℝ | 0 ≤ f x} := isClosed_le continuous_const hcont
    have hsub : Set.range (fun q : Fin g → ℚ => fun i => (q i : ℝ)) ⊆ {x | 0 ≤ f x} := by
      rintro _ ⟨q, rfl⟩
      exact hrat q
    have := hdense.closure_range ▸ (closure_minimal hsub hclosed)
    exact this (Set.mem_univ x)
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · ext i j
    simp [hM, conjTranspose_apply, hB.apply i j]
  · simpa [hf] using hall x

end GlobalTheory
