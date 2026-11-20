import Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementN

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

/- English proof (translation)
Establish `hP : (2:ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hP0 : (0:ℝ) < p` using `by linarith`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Rewrite using `[Finset.sum_range_succ]`. Establish `hx : (0:ℝ) < (p:ℝ)^(m0+n)` using `pow_pos hP0 _`. Establish `e : (2:ℝ) / (p:ℝ)^(m0+(n+1)) ≤ 1 / (p:ℝ)^(m0+n)`. Rewrite using `[← add_assoc, pow_succ, div_le_div_iff₀ (by positivity) hx]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `e2 : (2:ℝ) / (p:ℝ)^(m0+n) = 2 * (1 / (p:ℝ)^(m0+n))` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem geom_range_le (p m0 n : ℕ) (hp : 2 ≤ p) :
    ∑ i ∈ Finset.range n, (1 / (p : ℝ) ^ (m0 + i)) ≤ 2 / (p : ℝ) ^ m0 - 2 / (p : ℝ) ^ (m0 + n) := by
  have hP : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hP0 : (0:ℝ) < p := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hx : (0:ℝ) < (p:ℝ)^(m0+n) := pow_pos hP0 _
    have e : (2:ℝ) / (p:ℝ)^(m0+(n+1)) ≤ 1 / (p:ℝ)^(m0+n) := by
      rw [← add_assoc, pow_succ, div_le_div_iff₀ (by positivity) hx]
      nlinarith
    have e2 : (2:ℝ) / (p:ℝ)^(m0+n) = 2 * (1 / (p:ℝ)^(m0+n)) := by ring
    linarith

/- English proof (translation)
Introduce `p m0 s hp hs`. Establish `hP0 : (0:ℝ) < p`. Establish `: (2:ℝ) ≤ p` using `by exact_mod_cast hp`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨n, hn⟩ : ∃ n, ∀ D ∈ s, D < m0 + n` from `⟨s.sup (fun x => x) + 1, fun D hD => by`.

Use `Finset.le_sup (f := fun x => x) hD` as an intermediate fact. Use the proof step `omega⟩`. Establish `hsub : s ⊆ (Finset.range n).image (fun i => m0 + i)`. Introduce `D hD`. Simplify using `only [Finset.mem_image, Finset.mem_range]`.

Establish `h1` using `hn D hD`. Establish `h2` using `hs D hD`. Conclude with `⟨D - m0, by omega, by omega⟩`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_image (fun x _ y _ h => by simpa using h)]`.

Use `_ ≤ 2 / (p:ℝ)^m0 - 2 / (p:ℝ)^(m0+n) := geom_range_le p m0 n hp`. Use `_ ≤ 2 / (p:ℝ)^m0 := by`. Establish `: (0:ℝ) ≤ 2 / (p:ℝ)^(m0+n)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem geometricSumDistinct : GeomDistinct := by
  intro p m0 s hp hs
  have hP0 : (0:ℝ) < p := by
    have : (2:ℝ) ≤ p := by exact_mod_cast hp
    linarith
  obtain ⟨n, hn⟩ : ∃ n, ∀ D ∈ s, D < m0 + n :=
    ⟨s.sup (fun x => x) + 1, fun D hD => by
      have := Finset.le_sup (f := fun x => x) hD
      omega⟩
  have hsub : s ⊆ (Finset.range n).image (fun i => m0 + i) := by
    intro D hD
    simp only [Finset.mem_image, Finset.mem_range]
    have h1 := hn D hD
    have h2 := hs D hD
    exact ⟨D - m0, by omega, by omega⟩
  calc ∑ D ∈ s, (1 / (p:ℝ)^D)
      ≤ ∑ D ∈ (Finset.range n).image (fun i => m0 + i), (1 / (p:ℝ)^D) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ i ∈ Finset.range n, (1 / (p:ℝ)^(m0+i)) := by
        rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
    _ ≤ 2 / (p:ℝ)^m0 - 2 / (p:ℝ)^(m0+n) := geom_range_le p m0 n hp
    _ ≤ 2 / (p:ℝ)^m0 := by
        have : (0:ℝ) ≤ 2 / (p:ℝ)^(m0+n) := by positivity
        linarith

/- English proof (translation)
Introduce `p k Ns D1 L1 R R' a Y Qn be hp hk hNs hY ha hQn hL1 hbe h7 h8`. Establish `hP : (2:ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hP0 : (0:ℝ) < p` using `by linarith`. Establish `hk' : (1:ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hNs' : (1:ℝ) ≤ Ns` using `by exact_mod_cast hNs`.

Establish `hY0 : (0:ℝ) < Y` using `by linarith`. Establish `hk0 : (0:ℝ) < k` using `by linarith`. Establish `hNs0 : (0:ℝ) < Ns` using `by linarith`. Establish `hR : (0:ℝ) < (p:ℝ)^R` using `pow_pos hP0 _`. Establish `hR' : (0:ℝ) < (p:ℝ)^R'` using `pow_pos hP0 _`.

Establish `hD1 : (0:ℝ) < (p:ℝ)^D1` using `pow_pos hP0 _`. Establish `hL : (0:ℝ) < (p:ℝ)^L1` using `pow_pos hP0 _`. Establish `hT : (0:ℝ) < Qn * (p:ℝ)^R' / (p:ℝ)^R` using `by positivity`. Establish `sA : be / (Qn * (p:ℝ)^R' / (p:ℝ)^R) ≤ (4 * a / (p:ℝ)^(R+D1+L1+1)) / (Qn * (p:ℝ)^R' / (p:ℝ)^R)` using `div_le_div_of_nonneg_right hbe hT.le`. Establish `sB : (4 * a / (p:ℝ)^(R+D1+L1+1)) / (Qn * (p:ℝ)^R' / (p:ℝ)^R) = 4 * a / ((p:ℝ)^D1 * (p:ℝ)^L1 * p * (Qn * (p:ℝ)^R'))`.

Rewrite using `[show R+D1+L1+1 = R + D1 + L1 + 1 from rfl, pow_succ, pow_add, pow_add]`. Clear the denominators using the available nonvanishing facts. Establish `ha7 : a < (p:ℝ)^R' * (8 * p * Y * (k:ℝ)^2 * Ns * ((p:ℝ)^D1 * Qn))`. Rewrite `h7` using `[div_lt_iff₀ (by positivity)]`. Then use the resulting hypothesis. Establish `sC : 4 * a / ((p:ℝ)^D1 * (p:ℝ)^L1 * p * (Qn * (p:ℝ)^R')) < 32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1`.

Rewrite using `[div_lt_div_iff₀ (by positivity) hL]`. Use `mul_lt_mul_of_pos_left ha7 (show (0:ℝ) < 4 * (p:ℝ)^L1 by positivity)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hPL : (p:ℝ)^L1 = (p:ℝ)^(L1-1) * p`. Rewrite using `[← pow_succ]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `s2 : 32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 ≤ 1 / (4 * p * Y)`. Rewrite using `[div_le_div_iff₀ hL (by positivity), hPL]`. Use `mul_le_mul_of_nonneg_right h8 hP0.le` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `s1 : be / (Qn * (p:ℝ)^R' / (p:ℝ)^R) < 32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1`. Rewrite `sA` using `[sB]`. Conclude with `lt_of_le_of_lt sA sC`. Establish `s3 : 1 / (4 * p * Y) ≤ 1 / (4 * Y)` using `one_div_le_one_div_of_le (by positivity) (by nlinarith)`.

Conclude with `⟨s1, s2, by linarith⟩`.
-/
theorem admissibleSmallRatio : AdmissibleSmallRatio := by
  intro p k Ns D1 L1 R R' a Y Qn be hp hk hNs hY ha hQn hL1 hbe h7 h8
  have hP : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hP0 : (0:ℝ) < p := by linarith
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hNs' : (1:ℝ) ≤ Ns := by exact_mod_cast hNs
  have hY0 : (0:ℝ) < Y := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  have hNs0 : (0:ℝ) < Ns := by linarith
  have hR : (0:ℝ) < (p:ℝ)^R := pow_pos hP0 _
  have hR' : (0:ℝ) < (p:ℝ)^R' := pow_pos hP0 _
  have hD1 : (0:ℝ) < (p:ℝ)^D1 := pow_pos hP0 _
  have hL : (0:ℝ) < (p:ℝ)^L1 := pow_pos hP0 _
  have hT : (0:ℝ) < Qn * (p:ℝ)^R' / (p:ℝ)^R := by positivity
  have sA : be / (Qn * (p:ℝ)^R' / (p:ℝ)^R) ≤
      (4 * a / (p:ℝ)^(R+D1+L1+1)) / (Qn * (p:ℝ)^R' / (p:ℝ)^R) :=
    div_le_div_of_nonneg_right hbe hT.le
  have sB : (4 * a / (p:ℝ)^(R+D1+L1+1)) / (Qn * (p:ℝ)^R' / (p:ℝ)^R) =
      4 * a / ((p:ℝ)^D1 * (p:ℝ)^L1 * p * (Qn * (p:ℝ)^R')) := by
    rw [show R+D1+L1+1 = R + D1 + L1 + 1 from rfl, pow_succ, pow_add, pow_add]
    field_simp
  have ha7 : a < (p:ℝ)^R' * (8 * p * Y * (k:ℝ)^2 * Ns * ((p:ℝ)^D1 * Qn)) := by
    rwa [div_lt_iff₀ (by positivity)] at h7
  have sC : 4 * a / ((p:ℝ)^D1 * (p:ℝ)^L1 * p * (Qn * (p:ℝ)^R')) <
      32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 := by
    rw [div_lt_div_iff₀ (by positivity) hL]
    have := mul_lt_mul_of_pos_left ha7 (show (0:ℝ) < 4 * (p:ℝ)^L1 by positivity)
    nlinarith
  have hPL : (p:ℝ)^L1 = (p:ℝ)^(L1-1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have s2 : 32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 ≤ 1 / (4 * p * Y) := by
    rw [div_le_div_iff₀ hL (by positivity), hPL]
    have := mul_le_mul_of_nonneg_right h8 hP0.le
    nlinarith
  have s1 : be / (Qn * (p:ℝ)^R' / (p:ℝ)^R) < 32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 := by
    rw [sB] at sA
    exact lt_of_le_of_lt sA sC
  have s3 : 1 / (4 * p * Y) ≤ 1 / (4 * Y) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  exact ⟨s1, s2, by linarith⟩

end Formalism.InvariantFactorPaths.BranchingDimensions
