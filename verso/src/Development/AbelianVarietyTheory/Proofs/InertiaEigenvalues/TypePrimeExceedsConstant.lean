import Mathlib
import Formalism.LocalRingCardinality.DataParams

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory

/- English proof (translation)
Use `set y := k * b with hy`. Establish `hby : 5 * b ≤ y` using `by rw [hy]; nlinarith`. Establish `hy5 : 5 ≤ y` using `by linarith`. Establish `hy0 : 0 < y` using `by linarith`. Establish `h1 : F * N ^ 2 + N ^ 3 ≤ y * (3 * y) ^ 2 + (3 * y) ^ 3`.

Establish `hFy : F ≤ y` using `by linarith`. Use `gcongr`. Establish `h0 : 0 ≤ F * N ^ 2 + N ^ 3` using `by positivity`. Establish `h2 : C * (F * N ^ 2 + N ^ 3) ≤ y * (y * (3 * y) ^ 2 + (3 * y) ^ 3)` using `mul_le_mul (by linarith) h1 h0 hy0.le`. Establish `h3 : y * (y * (3 * y) ^ 2 + (3 * y) ^ 3) = 36 * y ^ 4` using `by ring`.

Establish `h4 : (5 : ℝ) ^ 4 ≤ y ^ 4` using `by gcongr`. Establish `h5 : 0 < y ^ 4` using `by positivity`. Establish `h6 : y ^ 8 = y ^ 4 * y ^ 4` using `by ring`. Rewrite using `[h6]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem typePrime_real_bound {C F N k b : ℝ} (hF0 : 0 ≤ F) (hN0 : 0 ≤ N)
    (hC : C ≤ b) (hF : F ≤ 5 * b) (hN : N ≤ 3 * (k * b)) (hk : 5 ≤ k) (hb : 1 ≤ b) :
    C * (F * N ^ 2 + N ^ 3) < (k * b) ^ 8 := by
  set y := k * b with hy
  have hby : 5 * b ≤ y := by rw [hy]; nlinarith
  have hy5 : 5 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have h1 : F * N ^ 2 + N ^ 3 ≤ y * (3 * y) ^ 2 + (3 * y) ^ 3 := by
    have hFy : F ≤ y := by linarith
    gcongr
  have h0 : 0 ≤ F * N ^ 2 + N ^ 3 := by positivity
  have h2 : C * (F * N ^ 2 + N ^ 3) ≤ y * (y * (3 * y) ^ 2 + (3 * y) ^ 3) :=
    mul_le_mul (by linarith) h1 h0 hy0.le
  have h3 : y * (y * (3 * y) ^ 2 + (3 * y) ^ 3) = 36 * y ^ 4 := by ring
  have h4 : (5 : ℝ) ^ 4 ≤ y ^ 4 := by gcongr
  have h5 : 0 < y ^ 4 := by positivity
  have h6 : y ^ 8 = y ^ 4 * y ^ 4 := by ring
  rw [h6]
  nlinarith

/- English proof (translation)
Introduce `D L P hsum hb CT hCT`. Establish `heta` using `L.etaSz_pos`. Establish `hSc` using `L.Sc_pos`. Establish `hfl : (⌊L.etaSz⌋₊ : ℝ) ≤ L.etaSz` using `Nat.floor_le heta.le`. Establish `ht0 : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`.

Use `⟨?_, by linarith, fun i => ?_⟩` and prove the remaining obligations. Establish `: ⌊L.etaSz⌋₊ + D.R.t ≤ ⌊3 * L.sc.b⌋₊`. Apply `Nat.le_floor` to reduce the goal to its premises. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Use linear arithmetic over natural numbers and integers. Take `⟨Y, hY, -, -, hg⟩` from `P.g_Y`. Establish `hgi` using `(hg i).1`. Establish `hm` using `D.R.m_add_three_le_k`. Establish `hm2` using `D.R.two_le_m`.

Establish `hk5 : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : 5 ≤ D.R.k)`. Establish `hnV : D.R.nV + 1 ≤ 2 * D.R.k + D.R.t`. Unfold `Ranks.nV Ranks.r`. Use linear arithmetic over natural numbers and integers. Establish `hnVR : (D.R.nV : ℝ) + 1 ≤ 2 * D.R.k + D.R.t` using `by exact_mod_cast hnV`.

Establish `hfl3 : (⌊3 * L.sc.b⌋₊ : ℝ) ≤ 3 * L.sc.b` using `Nat.floor_le (by linarith)`. Establish `hN : (D.R.nV : ℝ) + 1 ≤ 3 * ((D.R.k : ℝ) * L.sc.b)` using `by nlinarith`. Establish `key` using `typePrime_real_bound (C := (CT : ℝ)) (F := (⌊3 * L.sc.b⌋₊ : ℝ) + 2) (N := (D.R.nV : ℝ) + 1) (by positivity) (by positivity) hCT (by linarith) hN hk5 hb`. Establish `: ((CT * ((⌊3 * L.sc.b⌋₊ + 2 + 0) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) : ℕ) : ℝ) < (D.host.g i : ℝ)`. Use `push_cast`.

Simplify using `only [add_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions.
-/
theorem typePrime_exceeds_constant :
    ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → L.etaSz + D.R.t + L.Sc ≤ L.sc.b → 1 ≤ L.sc.b → ∀ CT : ℕ, (CT : ℝ) ≤ L.sc.b → (⌊L.etaSz⌋₊ + D.R.t + 1 < ⌊3 * L.sc.b⌋₊ + 2) ∧ ((⌊L.etaSz⌋₊ : ℝ) ≤ 2 * L.etaSz) ∧ ∀ k : Fin 2, CT * ((⌊3 * L.sc.b⌋₊ + 2 + 0) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k := by
  intro D L P hsum hb CT hCT
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hfl : (⌊L.etaSz⌋₊ : ℝ) ≤ L.etaSz := Nat.floor_le heta.le
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨?_, by linarith, fun i => ?_⟩
  · have : ⌊L.etaSz⌋₊ + D.R.t ≤ ⌊3 * L.sc.b⌋₊ := by
      apply Nat.le_floor
      push_cast
      linarith
    omega
  · obtain ⟨Y, hY, -, -, hg⟩ := P.g_Y
    have hgi := (hg i).1
    have hm := D.R.m_add_three_le_k
    have hm2 := D.R.two_le_m
    have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
    have hnV : D.R.nV + 1 ≤ 2 * D.R.k + D.R.t := by
      unfold Ranks.nV Ranks.r
      omega
    have hnVR : (D.R.nV : ℝ) + 1 ≤ 2 * D.R.k + D.R.t := by exact_mod_cast hnV
    have hfl3 : (⌊3 * L.sc.b⌋₊ : ℝ) ≤ 3 * L.sc.b := Nat.floor_le (by linarith)
    have hN : (D.R.nV : ℝ) + 1 ≤ 3 * ((D.R.k : ℝ) * L.sc.b) := by nlinarith
    have key := typePrime_real_bound (C := (CT : ℝ)) (F := (⌊3 * L.sc.b⌋₊ : ℝ) + 2)
      (N := (D.R.nV : ℝ) + 1) (by positivity) (by positivity) hCT (by linarith) hN hk5 hb
    have : ((CT * ((⌊3 * L.sc.b⌋₊ + 2 + 0) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) : ℕ) : ℝ) <
        (D.host.g i : ℝ) := by
      push_cast
      simp only [add_zero]
      linarith
    exact_mod_cast this

end GlobalTheory
