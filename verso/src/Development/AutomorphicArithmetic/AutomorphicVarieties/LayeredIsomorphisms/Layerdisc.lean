import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layeremb
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Imports

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

/- English proof (translation)
Introduce `l j n1 N0 hl hN0`. Establish `hlj : 1 ≤ l ^ j` using `Nat.one_le_pow _ _ hl.pos`. Use `set n0 : ℕ := (n1 + 1) * l ^ j with hn0`. Establish `hn0pos : 1 ≤ n0`. Rewrite using `[hn0]`.

Conclude with `Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))`. Establish `hn0R : (1:ℝ) ≤ (n0:ℝ)` using `by exact_mod_cast hn0pos`. Establish `hN0R : (1:ℝ) ≤ (N0:ℝ)` using `by exact_mod_cast hN0`. Establish `hC1 : (1:ℝ) ≤ 2 * (n0:ℝ) * (N0:ℝ)` using `by nlinarith`. Establish `hlogC : 0 ≤ Real.log (2 * (n0:ℝ) * (N0:ℝ))` using `Real.log_nonneg hC1`.

Establish `hlog2 : 0 ≤ Real.log 2` using `Real.log_nonneg (by norm_num)`. Use `set A : ℝ := Real.log 2 + (n0:ℝ) * Real.log (2 * (n0:ℝ) * (N0:ℝ)) with hA`. Establish `hA0 : 0 ≤ A`. Establish `: 0 ≤ (n0:ℝ) * Real.log (2 * (n0:ℝ) * (N0:ℝ))` using `mul_nonneg (by linarith) hlogC`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨n0, A + n0, by linarith, ?_⟩` and prove the remaining obligations. Introduce `P w hP hw hlogP L₀ L₁ _ _ _ _ _ hdeg hemb hlay`. Establish `hdim : Module.finrank ℚ L₀ * Module.finrank L₀ L₁ = Module.finrank ℚ L₁` using `Module.finrank_mul_finrank ℚ L₀ L₁`. Establish `hrel : Module.finrank L₀ L₁ = l ^ j`. Unfold `IsLayer at hlay`.

Conclude with `hlay.2`. Establish `hd1 : Module.finrank ℚ L₁ ≤ n0`. Rewrite using `[← hdim, hrel, hn0]`. Conclude with `Nat.mul_le_mul_right _ (by omega)`. Use `⟨hd1, ?_⟩` and prove the remaining obligations.

Establish `hNP : 0 < N0 * P` using `Nat.mul_pos hN0 hP`. Take `⟨N', hN'pos, hN'le, hN'emb⟩` from `layeremb l j (N0 * P) hl hNP L₀ L₁ hemb hlay`. Establish `hdisc` using `disc L₁ N' hN'pos hN'emb`. Establish `hd1R : ((Module.finrank ℚ L₁ : ℕ) : ℝ) ≤ (n0:ℝ)` using `by exact_mod_cast hd1`. Establish `hPR : (1:ℝ) ≤ (P:ℝ)` using `by exact_mod_cast hP`.

Establish `hN'R : (1:ℝ) ≤ (N':ℝ)` using `by exact_mod_cast hN'pos`. Establish `hlogN' : 0 ≤ Real.log (N':ℝ)` using `Real.log_nonneg hN'R`. Establish `hN'le' : (N':ℝ) ≤ 2 * (n0:ℝ) * (N0:ℝ) * (P:ℝ)`. Establish `h1 : (N':ℝ) ≤ ((2 * Module.finrank ℚ L₁ * (N0 * P) : ℕ) : ℝ)` using `by exact_mod_cast hN'le`. Establish `h2 : ((2 * Module.finrank ℚ L₁ * (N0 * P) : ℕ) : ℝ) ≤ 2 * (n0:ℝ) * (N0:ℝ) * (P:ℝ)`.

Use `push_cast`. Establish `: (0:ℝ) ≤ (N0:ℝ) * (P:ℝ)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogle : Real.log (N':ℝ) ≤ Real.log (2 * (n0:ℝ) * (N0:ℝ)) + Real.log (P:ℝ)`.

Rewrite using `[← Real.log_mul (by linarith) (by linarith)]`. Conclude with `Real.log_le_log (by linarith) hN'le'`. Establish `hLP0 : 0 ≤ Real.log (P:ℝ)` using `Real.log_nonneg hPR`. Establish `hlog2D : Real.log (2 * ((discr L₁).natAbs : ℝ)) ≤ Real.log 2 + Real.log ((discr L₁).natAbs : ℝ)`. Break down `Nat.eq_zero_or_pos (discr L₁).natAbs with h | h` into its components or cases.

Rewrite using `[h]`. Simplify using `using hlog2`. Establish `hD : ((discr L₁).natAbs : ℝ) ≠ 0` using `by positivity`. Rewrite using `[Real.log_mul (by norm_num) hD]`. Establish `k1 : ((Module.finrank ℚ L₁ : ℕ) : ℝ) * Real.log (N':ℝ) ≤ (n0:ℝ) * Real.log (N':ℝ)` using `mul_le_mul_of_nonneg_right hd1R hlogN'`.

Establish `k2 : (n0:ℝ) * Real.log (N':ℝ) ≤ (n0:ℝ) * (Real.log (2 * (n0:ℝ) * (N0:ℝ)) + Real.log (P:ℝ))` using `mul_le_mul_of_nonneg_left hlogle (by linarith)`. Establish `k3 : (n0:ℝ) * Real.log (P:ℝ) ≤ (n0:ℝ) * w` using `mul_le_mul_of_nonneg_left hlogP (by linarith)`. Establish `k4 : A ≤ A * w` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem UpperTheory.V.Win.layerdisc :
    ∀ (l j n1 N0 : ℕ), l.Prime → 0 < N0 → ∃ (n0 : ℕ) (c0 : ℝ), 0 ≤ c0 ∧
      ∀ (P : ℕ) (w : ℝ), 0 < P → 1 ≤ w → Real.log (P : ℝ) ≤ w →
        ∀ (L₀ L₁ : Type) [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁] [Algebra L₀ L₁],
          Module.finrank ℚ L₀ ≤ n1 → Nonempty (L₀ →ₐ[ℚ] CyclotomicField (N0 * P) ℚ) → IsLayer l j L₀ L₁ →
            Module.finrank ℚ L₁ ≤ n0 ∧ Real.log (2 * ((discr L₁).natAbs : ℝ)) ≤ c0 * w := by
  intro l j n1 N0 hl hN0
  have hlj : 1 ≤ l ^ j := Nat.one_le_pow _ _ hl.pos
  set n0 : ℕ := (n1 + 1) * l ^ j with hn0
  have hn0pos : 1 ≤ n0 := by
    rw [hn0]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hn0R : (1:ℝ) ≤ (n0:ℝ) := by exact_mod_cast hn0pos
  have hN0R : (1:ℝ) ≤ (N0:ℝ) := by exact_mod_cast hN0
  have hC1 : (1:ℝ) ≤ 2 * (n0:ℝ) * (N0:ℝ) := by nlinarith
  have hlogC : 0 ≤ Real.log (2 * (n0:ℝ) * (N0:ℝ)) := Real.log_nonneg hC1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set A : ℝ := Real.log 2 + (n0:ℝ) * Real.log (2 * (n0:ℝ) * (N0:ℝ)) with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ (n0:ℝ) * Real.log (2 * (n0:ℝ) * (N0:ℝ)) := mul_nonneg (by linarith) hlogC
    linarith
  refine ⟨n0, A + n0, by linarith, ?_⟩
  intro P w hP hw hlogP L₀ L₁ _ _ _ _ _ hdeg hemb hlay
  have hdim : Module.finrank ℚ L₀ * Module.finrank L₀ L₁ = Module.finrank ℚ L₁ :=
    Module.finrank_mul_finrank ℚ L₀ L₁
  have hrel : Module.finrank L₀ L₁ = l ^ j := by
    unfold IsLayer at hlay
    exact hlay.2
  have hd1 : Module.finrank ℚ L₁ ≤ n0 := by
    rw [← hdim, hrel, hn0]
    exact Nat.mul_le_mul_right _ (by omega)
  refine ⟨hd1, ?_⟩
  have hNP : 0 < N0 * P := Nat.mul_pos hN0 hP
  obtain ⟨N', hN'pos, hN'le, hN'emb⟩ := layeremb l j (N0 * P) hl hNP L₀ L₁ hemb hlay
  have hdisc := disc L₁ N' hN'pos hN'emb
  have hd1R : ((Module.finrank ℚ L₁ : ℕ) : ℝ) ≤ (n0:ℝ) := by exact_mod_cast hd1
  have hPR : (1:ℝ) ≤ (P:ℝ) := by exact_mod_cast hP
  have hN'R : (1:ℝ) ≤ (N':ℝ) := by exact_mod_cast hN'pos
  have hlogN' : 0 ≤ Real.log (N':ℝ) := Real.log_nonneg hN'R
  have hN'le' : (N':ℝ) ≤ 2 * (n0:ℝ) * (N0:ℝ) * (P:ℝ) := by
    have h1 : (N':ℝ) ≤ ((2 * Module.finrank ℚ L₁ * (N0 * P) : ℕ) : ℝ) := by exact_mod_cast hN'le
    have h2 : ((2 * Module.finrank ℚ L₁ * (N0 * P) : ℕ) : ℝ) ≤ 2 * (n0:ℝ) * (N0:ℝ) * (P:ℝ) := by
      push_cast
      have : (0:ℝ) ≤ (N0:ℝ) * (P:ℝ) := by positivity
      nlinarith
    linarith
  have hlogle : Real.log (N':ℝ) ≤ Real.log (2 * (n0:ℝ) * (N0:ℝ)) + Real.log (P:ℝ) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) hN'le'
  have hLP0 : 0 ≤ Real.log (P:ℝ) := Real.log_nonneg hPR
  have hlog2D : Real.log (2 * ((discr L₁).natAbs : ℝ)) ≤ Real.log 2 + Real.log ((discr L₁).natAbs : ℝ) := by
    rcases Nat.eq_zero_or_pos (discr L₁).natAbs with h | h
    · rw [h]
      simpa using hlog2
    · have hD : ((discr L₁).natAbs : ℝ) ≠ 0 := by positivity
      rw [Real.log_mul (by norm_num) hD]
  have k1 : ((Module.finrank ℚ L₁ : ℕ) : ℝ) * Real.log (N':ℝ) ≤ (n0:ℝ) * Real.log (N':ℝ) :=
    mul_le_mul_of_nonneg_right hd1R hlogN'
  have k2 : (n0:ℝ) * Real.log (N':ℝ) ≤ (n0:ℝ) * (Real.log (2 * (n0:ℝ) * (N0:ℝ)) + Real.log (P:ℝ)) :=
    mul_le_mul_of_nonneg_left hlogle (by linarith)
  have k3 : (n0:ℝ) * Real.log (P:ℝ) ≤ (n0:ℝ) * w := mul_le_mul_of_nonneg_left hlogP (by linarith)
  have k4 : A ≤ A * w := by nlinarith
  nlinarith
