import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RkNs

/- English proof (translation)
Introduce `K _ _ w r t hrt k hk`. Establish `hN : (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)`. Conclude with `GlobalTheory.LFun.one_lt_absNorm w` after adjusting the coercions. Establish `hN0 : (0 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)` using `by linarith`. Establish `hkabs : (r : ℤ) < k ∨ k < -(r : ℤ)`.

Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk`. Apply the tactic sequence `rcases hk with h | h | h | h <;> subst h <;> omega`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `β hβ0 h1 h2 heq`. Establish `hn : ‖β‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((k : ℝ) / 2)`.

Rewrite using `[heq, GlobalTheory.LFun.norm_npow]`. Use `congr 1`. Simplify using the standard rewrite rules. Break down `hkabs with hk' | hk'` into its components or cases. Establish `: ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((k : ℝ) / 2)`.

Apply `Real.rpow_lt_rpow_of_exponent_lt hN` to reduce the goal to its premises. Establish `: (r : ℝ) < (k : ℝ)` using `by exact_mod_cast hk'`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hinv : ‖β⁻¹‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-((k : ℝ) / 2))`.

Rewrite using `[norm_inv, hn, Real.rpow_neg hN0.le]`. Establish `: ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-((k : ℝ) / 2))`. Apply `Real.rpow_lt_rpow_of_exponent_lt hN` to reduce the goal to its premises. Establish `: (k : ℝ) < -(r : ℝ)` using `by exact_mod_cast hk'`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x hx1 hxne β hβ heq`. Simplify using `only [GlobalTheory.LFun.seg, Multiset.mem_map, Finset.mem_range] at hβ`. Take `⟨i, -, rfl⟩` from `hβ`. Use `set c : ℂ := (k : ℂ) / 2 - (((t : ℂ) - 1) / 2 - (i : ℂ)) with hc`.

Establish `hsplit : GlobalTheory.LFun.npow w ((k : ℂ) / 2) = GlobalTheory.LFun.npow w (((t : ℂ) - 1) / 2 - (i : ℂ)) * GlobalTheory.LFun.npow w c`. Rewrite using `[← GlobalTheory.LFun.npow_add]`. Use `congr 1`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `heq` using `[Units.val_mul, GlobalTheory.LFun.coe_npowU, hsplit, mul_comm]`. Establish `hx : (x : ℂ) = GlobalTheory.LFun.npow w c` using `mul_left_cancel₀ (GlobalTheory.LFun.npow_ne_zero w _) heq`. Establish `him : c.im = 0`. Rewrite using `[hc]`. Simplify using the standard rewrite rules.

Establish `hre : c.re = 0`. Establish `h1 : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ c.re = 1`. Rewrite using `[← GlobalTheory.LFun.norm_npow, ← hx, hx1]`. Break down `lt_trichotomy c.re 0 with h | h | h` into its components or cases. Use `Real.rpow_lt_one_of_one_lt_of_neg hN h` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h`. Use `Real.one_lt_rpow hN h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc0 : c = 0` using `Complex.ext hre him`.

Apply `hxne` to reduce the goal to its premises. Use `ext`. Rewrite using `[hx, hc0, GlobalTheory.LFun.npow, Complex.cpow_zero, Units.val_one]`.
-/
theorem small_entries_and_strings_avoid_excluded : ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (r t : ℕ), r + 2 ≤ t → ∀ k ∈ ({(t : ℤ) - 1, 1 - (t : ℤ), (t : ℤ) + 1, -((t : ℤ) + 1)} : Set ℤ), (∀ β : ℂ, β ≠ 0 → ‖β‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) → ‖β⁻¹‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) → β ≠ GlobalTheory.LFun.npow w ((k : ℂ) / 2)) ∧ ∀ x : ℂˣ, ‖(x : ℂ)‖ = 1 → x ≠ 1 → ∀ β ∈ GlobalTheory.LFun.seg w x t, (β : ℂ) ≠ GlobalTheory.LFun.npow w ((k : ℂ) / 2) := by
  intro K _ _ w r t hrt k hk
  have hN : (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast GlobalTheory.LFun.one_lt_absNorm w
  have hN0 : (0 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by linarith
  have hkabs : (r : ℤ) < k ∨ k < -(r : ℤ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with h | h | h | h <;> subst h <;> omega
  refine ⟨?_, ?_⟩
  · intro β hβ0 h1 h2 heq
    have hn : ‖β‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((k : ℝ) / 2) := by
      rw [heq, GlobalTheory.LFun.norm_npow]
      congr 1
      simp
    rcases hkabs with hk' | hk'
    · have : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) <
          ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((k : ℝ) / 2) := by
        apply Real.rpow_lt_rpow_of_exponent_lt hN
        have : (r : ℝ) < (k : ℝ) := by exact_mod_cast hk'
        linarith
      linarith
    · have hinv : ‖β⁻¹‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-((k : ℝ) / 2)) := by
        rw [norm_inv, hn, Real.rpow_neg hN0.le]
      have : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) <
          ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-((k : ℝ) / 2)) := by
        apply Real.rpow_lt_rpow_of_exponent_lt hN
        have : (k : ℝ) < -(r : ℝ) := by exact_mod_cast hk'
        linarith
      linarith
  · intro x hx1 hxne β hβ heq
    simp only [GlobalTheory.LFun.seg, Multiset.mem_map, Finset.mem_range] at hβ
    obtain ⟨i, -, rfl⟩ := hβ
    set c : ℂ := (k : ℂ) / 2 - (((t : ℂ) - 1) / 2 - (i : ℂ)) with hc
    have hsplit : GlobalTheory.LFun.npow w ((k : ℂ) / 2) =
        GlobalTheory.LFun.npow w (((t : ℂ) - 1) / 2 - (i : ℂ)) * GlobalTheory.LFun.npow w c := by
      rw [← GlobalTheory.LFun.npow_add]
      congr 1
      rw [hc]; ring
    rw [Units.val_mul, GlobalTheory.LFun.coe_npowU, hsplit, mul_comm] at heq
    have hx : (x : ℂ) = GlobalTheory.LFun.npow w c :=
      mul_left_cancel₀ (GlobalTheory.LFun.npow_ne_zero w _) heq
    have him : c.im = 0 := by
      rw [hc]; simp
    have hre : c.re = 0 := by
      have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ c.re = 1 := by
        rw [← GlobalTheory.LFun.norm_npow, ← hx, hx1]
      rcases lt_trichotomy c.re 0 with h | h | h
      · have := Real.rpow_lt_one_of_one_lt_of_neg hN h
        linarith
      · exact h
      · have := Real.one_lt_rpow hN h
        linarith
    have hc0 : c = 0 := Complex.ext hre him
    apply hxne
    ext
    rw [hx, hc0, GlobalTheory.LFun.npow, Complex.cpow_zero, Units.val_one]

end GlobalTheory.RkNs
