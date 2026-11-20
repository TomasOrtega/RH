import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHLocalA

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `hre : ((26 / 25 : ℂ) + t * I).re = 26 / 25`. Simplify using the standard rewrite rules. Establish `h1` using `abs_re_le_norm (z - ((26 / 25 : ℂ) + t * I))`. Rewrite `h1` using `[sub_re, hre]`. Establish `hn : ‖((26 / 25 : ℂ) + t * I)‖ ≤ 26 / 25 + |t|`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]`. Evaluate the numerical expressions. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(abs_le.mp (h1.trans hz)).1` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `norm_sub_norm_le z ((26 / 25 : ℂ) + t * I)` as an intermediate fact. Combine the linear relations using `[abs_nonneg t]`.
-/
lemma dhl_geom (t : ℝ) (z : ℂ) (hz : ‖z - ((26 / 25 : ℂ) + t * I)‖ ≤ 12 / 25) :
    1 / 2 ≤ z.re ∧ 1 + ‖z‖ ≤ 2 * (|t| + 2) := by
  have hre : ((26 / 25 : ℂ) + t * I).re = 26 / 25 := by
    simp
  have h1 := abs_re_le_norm (z - ((26 / 25 : ℂ) + t * I))
  rw [sub_re, hre] at h1
  have hn : ‖((26 / 25 : ℂ) + t * I)‖ ≤ 26 / 25 + |t| := by
    calc ‖((26 / 25 : ℂ) + t * I)‖ ≤ ‖(26 / 25 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 26 / 25 + |t| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        norm_num
  refine ⟨?_, ?_⟩
  · have := (abs_le.mp (h1.trans hz)).1; linarith
  · have := norm_sub_norm_le z ((26 / 25 : ℂ) + t * I)
    linarith [abs_nonneg t]

/- English proof (translation)
Establish `hB1 : 1 ≤ K * X ^ 2` using `by nlinarith`. Take `⟨Z, m, hZ, hm, hsum, hexp⟩` from `hCau f ((26 / 25 : ℂ) + t * I) (12 / 25) (K * X ^ 2) (by norm_num) hB1 hf.differentiableOn hf0 (fun z hz => hB z (by rwa [Metric.mem_closedBall, dist_eq] at hz))`. Establish `hlog` using `dhl_log K X hK hX`. Establish `hlog0 : 0 ≤ Real.log (K * X ^ 2)` using `Real.log_nonneg hB1`. Use `⟨Z, m, ?_, hm, ?_, ?_⟩` and prove the remaining obligations.

Introduce `ρ`. Rewrite using `[hZ ρ, Metric.mem_closedBall, dist_eq]`. Evaluate the numerical expressions. Use `hsum.trans ?_` and prove the remaining obligations. Establish `h2 : (1 / 2 : ℝ) ≤ Real.log 2` using `by linarith [Real.log_two_gt_d9]`.

Rewrite using `[div_le_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Introduce `k s hs hfs`. Use `hexp k s (by rw [Metric.mem_closedBall, dist_eq]; norm_num; linarith) hfs` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations.

Establish `e : (72 * Real.log (K * X ^ 2) / (12 / 25) * (12 / (12 / 25)) ^ k : ℝ) = 150 * Real.log (K * X ^ 2) * 25 ^ k` using `by norm_num; ring`. Rewrite using `[e]`. Establish `: (0 : ℝ) < 25 ^ k` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma dhl_core (hCau : DHCauchy) (f : ℂ → ℂ) (t K X : ℝ) (hK : 1 ≤ K) (hX : 3 ≤ X)
    (hf : Differentiable ℂ f) (hf0 : f ((26 / 25 : ℂ) + t * I) ≠ 0)
    (hB : ∀ z, ‖z - ((26 / 25 : ℂ) + t * I)‖ ≤ 12 / 25 →
      ‖f z‖ ≤ K * X ^ 2 * ‖f ((26 / 25 : ℂ) + t * I)‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ 150 * (Real.log K + 2) * Real.log X ∧
      ∀ (k : ℕ) (s : ℂ), ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 → f s ≠ 0 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z => -(deriv f z / f z)) s
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤
          150 * (Real.log K + 2) * Real.log X * 25 ^ k := by
  have hB1 : 1 ≤ K * X ^ 2 := by nlinarith
  obtain ⟨Z, m, hZ, hm, hsum, hexp⟩ := hCau f ((26 / 25 : ℂ) + t * I) (12 / 25) (K * X ^ 2)
    (by norm_num) hB1 hf.differentiableOn hf0
    (fun z hz => hB z (by rwa [Metric.mem_closedBall, dist_eq] at hz))
  have hlog := dhl_log K X hK hX
  have hlog0 : 0 ≤ Real.log (K * X ^ 2) := Real.log_nonneg hB1
  refine ⟨Z, m, ?_, hm, ?_, ?_⟩
  · intro ρ
    rw [hZ ρ, Metric.mem_closedBall, dist_eq]
    norm_num
  · refine hsum.trans ?_
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · intro k s hs hfs
    have := hexp k s (by rw [Metric.mem_closedBall, dist_eq]; norm_num; linarith) hfs
    refine this.trans ?_
    have e : (72 * Real.log (K * X ^ 2) / (12 / 25) * (12 / (12 / 25)) ^ k : ℝ)
        = 150 * Real.log (K * X ^ 2) * 25 ^ k := by
      norm_num; ring
    rw [e]
    have : (0 : ℝ) < 25 ^ k := by positivity
    nlinarith

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma dhl_z0re (t : ℝ) : ((26 / 25 : ℂ) + t * I).re = 26 / 25 := by
  simp

/- English proof (translation)
Establish `h` using `inverseBound M ψ ((26 / 25 : ℂ) + t * I) (by rw [dhl_z0re]; norm_num)`. Rewrite `h` using `[dhl_z0re]`. Establish `hne : DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I) ≠ 0` using `DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inr (by intro h; have := congrArg Complex.re h; rw [dhl_z0re] at this; norm_num at this)) (by rw [dhl_z0re]; norm_num)`. Establish `hpos : 0 < ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖` using `norm_pos_iff.mpr hne`. Rewrite `h` using `[inv_le_comm₀ hpos (by norm_num)]`.

Evaluate the numerical expressions using `at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma dhl_inv (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ) :
    1 ≤ 26 * ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by
  have h := inverseBound M ψ ((26 / 25 : ℂ) + t * I) (by rw [dhl_z0re]; norm_num)
  rw [dhl_z0re] at h
  have hne : DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ
      (Or.inr (by intro h; have := congrArg Complex.re h; rw [dhl_z0re] at this; norm_num at this))
      (by rw [dhl_z0re]; norm_num)
  have hpos : 0 < ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := norm_pos_iff.mpr hne
  rw [inv_le_comm₀ hpos (by norm_num)] at h
  norm_num at h
  linarith

def DHLocalAt (C : ℝ) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ) : Prop :=
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ IsLZero ψ ρ)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, ρ.re < 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ C * Real.log ((M : ℝ) * (|t| + 2)) ∧
      ∀ (k : ℕ) (s : ℂ), 1 < s.re → ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD ψ) s
            - (if ψ = 1 then 1 / (s - 1) ^ (k + 1) else 0)
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤ C * Real.log ((M : ℝ) * (|t| + 2)) * 25 ^ k

/- English proof (translation)
Establish `h3 : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Use polynomial arithmetic with `[abs_nonneg t]`.
-/
lemma dhl_X (M : ℕ) (t : ℝ) (hM : 3 ≤ M) : 3 ≤ (M : ℝ) * (|t| + 2) := by
  have h3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [abs_nonneg t]

/- English proof (translation)
Establish `hX` using `dhl_X M t hM`. Establish `h3 : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `hinv` using `dhl_inv M ψ t`. Establish `hf0 : DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I) ≠ 0`. Introduce `h`.

Rewrite `hinv` using `[h, norm_zero]`. Evaluate the numerical expressions using `at hinv`. Take `⟨Z, m, hZ, hm, hsum, hexp⟩` from `dhl_core hCau (DirichletCharacter.LFunction ψ) t K ((M : ℝ) * (|t| + 2)) hK1 hX (DirichletCharacter.differentiable_LFunction hψ) hf0 (by`. Introduce `z hz`. Take `⟨hre, hn⟩` from `dhl_geom t z hz`.

Establish `h1` using `hC0 M ψ hψ z hre`. Establish `hz0` using `norm_nonneg z`. Establish `ht` using `abs_nonneg t`. Combine the equalities or inequalities in the displayed calculation. Establish `: C0 ≤ K / 52` using `by linarith`.

Use `gcongr`. Use `_ ≤ (K / 52) * M * (2 * (|t| + 2)) := by gcongr`. Use `_ = K * ((M : ℝ) * (|t| + 2)) * (1 / 26) := by ring`. Use `_ ≤ K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by`. Establish `hXX : (M : ℝ) * (|t| + 2) ≤ ((M : ℝ) * (|t| + 2)) ^ 2` using `by nlinarith`.

Establish `: (1 / 26 : ℝ) ≤ ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖` using `by linarith`. Use the proof step `gcongr)`. Use `⟨Z, m, ?_, hm, ?_, hsum, ?_⟩` and prove the remaining obligations. Introduce `ρ`. Rewrite using `[hZ ρ]`.

Conclude with `and_congr_right (fun _ => ⟨fun h => ⟨Or.inl hψ, h⟩, fun h => h.2⟩)`. Introduce `ρ hρ`. Assume the negation of the conclusion as `hcon`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) (not_lt.mp hcon) ((hZ ρ).mp hρ).2`. Introduce `k s hs1 hs`.

Establish `h` using `hexp k s hs (DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) hs1.le)`. Rewrite using `[if_neg hψ, sub_zero]`. Conclude with `h`.
-/
lemma dhl_nontriv (hCau : DHCauchy) (C0 K : ℝ)
    (hC0 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C0 * q * (1 + ‖s‖))
    (hK1 : 1 ≤ K) (hK : 52 * C0 ≤ K) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (hψ : ψ ≠ 1)
    (t : ℝ) (hM : 3 ≤ M) : DHLocalAt (150 * (Real.log K + 2)) M ψ t := by
  have hX := dhl_X M t hM
  have h3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hinv := dhl_inv M ψ t
  have hf0 : DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hinv; norm_num at hinv
  obtain ⟨Z, m, hZ, hm, hsum, hexp⟩ := dhl_core hCau (DirichletCharacter.LFunction ψ) t K
    ((M : ℝ) * (|t| + 2)) hK1 hX (DirichletCharacter.differentiable_LFunction hψ) hf0 (by
      intro z hz
      obtain ⟨hre, hn⟩ := dhl_geom t z hz
      have h1 := hC0 M ψ hψ z hre
      have hz0 := norm_nonneg z
      have ht := abs_nonneg t
      calc ‖DirichletCharacter.LFunction ψ z‖ ≤ C0 * M * (1 + ‖z‖) := h1
        _ ≤ (K / 52) * M * (1 + ‖z‖) := by
            have : C0 ≤ K / 52 := by linarith
            gcongr
        _ ≤ (K / 52) * M * (2 * (|t| + 2)) := by gcongr
        _ = K * ((M : ℝ) * (|t| + 2)) * (1 / 26) := by ring
        _ ≤ K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by
            have hXX : (M : ℝ) * (|t| + 2) ≤ ((M : ℝ) * (|t| + 2)) ^ 2 := by nlinarith
            have : (1 / 26 : ℝ) ≤ ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by linarith
            gcongr)
  refine ⟨Z, m, ?_, hm, ?_, hsum, ?_⟩
  · intro ρ
    rw [hZ ρ]
    exact and_congr_right (fun _ => ⟨fun h => ⟨Or.inl hψ, h⟩, fun h => h.2⟩)
  · intro ρ hρ
    by_contra hcon
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) (not_lt.mp hcon)
      ((hZ ρ).mp hρ).2
  · intro k s hs1 hs
    have h := hexp k s hs (DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) hs1.le)
    rw [if_neg hψ, sub_zero]
    exact h

end Formalism.HermitianLattices.Ext.PrimesInProgressions
