import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.StepIdentity

variable {r : ℕ}

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem update_add_single (i : Fin r) (m : Fin r → ℕ) (n k : ℕ) :
    Function.update (m + (Pi.single i n : Fin r → ℕ)) i k = Function.update m i k := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_apply, hj, Pi.single_apply]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem update_self_add (i : Fin r) (m : Fin r → ℕ) (e : ℕ) :
    Function.update m i (m i + e) = m + (Pi.single i e : Fin r → ℕ) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_apply, hj, Pi.single_apply]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem partialSum_succ (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) :
    partialSum i v (m + Pi.single i 1) = partialSum i v m + v m := by
  simp only [partialSum, update_add_single, Pi.add_apply, Pi.single_eq_same]
  rw [Finset.sum_range_succ, Function.update_eq_self]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem partialSum_of_zero (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (h : m i = 0) :
    partialSum i v m = 0 := by
  simp [partialSum, h]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem partialSumMean_add_single_one (l : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) :
    meanP l i v (m + Pi.single i 1) = meanP l i v m := by
  simp only [meanP, update_add_single]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem partialSum_period {l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (h : GoodAt l i v)
    (m : Fin r → ℕ) : partialSum i v (m + Pi.single i l) = partialSum i v m := by
  simp only [partialSum, update_add_single, Pi.add_apply, Pi.single_eq_same]
  rw [Finset.sum_range_add]
  have h2 : ∑ e ∈ Finset.range l, v (Function.update m i (m i + e)) = 0 := by
    simp only [update_self_add]
    exact h.2 m
  rw [h2, add_zero]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Chain the equalities or inequalities of the calculation. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. A detailed English derivation is pending.
-/
theorem partialSum_bound {l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l)
    (h : GoodAt l i v) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ m, |(v m : ℝ)| ≤ C) :
    ∀ m, |(partialSum i v m : ℝ)| ≤ l * C := by
  have key : ∀ n, ∀ m : Fin r → ℕ, m i = n → |(partialSum i v m : ℝ)| ≤ l * C := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m hm
      by_cases hn : n < l
      · simp only [partialSum, hm]
        push_cast
        calc |∑ k ∈ Finset.range n, (v (Function.update m i k) : ℝ)|
            ≤ ∑ k ∈ Finset.range n, |(v (Function.update m i k) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range n, C := Finset.sum_le_sum fun k _ => hC _
          _ = n * C := by simp
          _ ≤ l * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hn.le) hC0
      · rw [not_lt] at hn
        have hmm : m = Function.update m i (n - l) + Pi.single i l := by
          funext j
          by_cases hj : j = i
          · subst hj
            simp only [Pi.add_apply, Function.update_self, Pi.single_eq_same]
            omega
          · simp [Function.update_apply, hj, Pi.single_apply]
        rw [hmm, partialSum_period h]
        exact ih (n - l) (by omega) _ (by simp)
  exact fun m => key (m i) m rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem abs_partialSumMean_le {l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l)
    {K : ℝ} (hK : ∀ m, |(partialSum i v m : ℝ)| ≤ K) (m : Fin r → ℕ) :
    |(meanP l i v m : ℝ)| ≤ K := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  simp only [meanP]
  push_cast
  rw [abs_div, abs_of_pos hl', div_le_iff₀ hl']
  calc |∑ k ∈ Finset.range l, (partialSum i v (Function.update m i k) : ℝ)|
      ≤ ∑ k ∈ Finset.range l, |(partialSum i v (Function.update m i k) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range l, K := Finset.sum_le_sum fun k _ => hK _
    _ = K * l := by simp [mul_comm]

/- English proof (translation)
Establish an intermediate fact. Treat this case separately. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem summable_cast_mul {α : Type*} (w : α → ℚ) (K : ℝ) (hw : ∀ m, |(w m : ℝ)| ≤ K)
    {g : α → ℂ} (hg : Summable g) : Summable (fun m => (w m : ℂ) * g m) := by
  have hn : Summable (fun m => ‖g m‖) := by
    first
      | exact hg.norm
      | exact summable_norm_iff.mpr hg
  refine Summable.of_norm_bounded (hn.mul_left K) (fun m => ?_)
  rw [norm_mul, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hw m) (norm_nonneg _)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Move the embeddings inside the algebraic operations. Chain the equalities or inequalities of the calculation.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem stepIdentity (r l : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (g : (Fin r → ℕ) → ℂ)
    (hl : 0 < l) (hgood : GoodAt l i v) (hv : BddW v) (hg : Summable g) :
    ∑' m, (v m : ℂ) * g m = ∑' m, (Bop l i v m : ℂ) * g m - ∑' m, (Aop l i v m : ℂ) * fd i g m := by
  obtain ⟨C, hC⟩ := hv
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hlC : 0 ≤ (l : ℝ) * C := mul_nonneg (Nat.cast_nonneg _) hC0
  have hPS := partialSum_bound hl hgood hC0 hC
  have hMP : ∀ m, |(meanP l i v m : ℝ)| ≤ l * C := abs_partialSumMean_le hl hPS
  set δ : Fin r → ℕ := Pi.single i 1 with hδ
  have hsub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    simpa only [Real.norm_eq_abs] using norm_sub_le a b
  have hBb : ∀ m, |(Bop l i v m : ℝ)| ≤ l * C := by
    intro m
    unfold Bop
    split_ifs
    · exact hMP m
    · rw [Rat.cast_zero, abs_zero]
      exact hlC
  have hAb : ∀ m, |(Aop l i v m : ℝ)| ≤ 2 * (l * C) := by
    intro m
    simp only [Aop, Rat.cast_sub]
    calc _ ≤ |(partialSum i v (m + Pi.single i 1) : ℝ)| + |(meanP l i v m : ℝ)| := hsub _ _
      _ ≤ l * C + l * C := add_le_add (hPS _) (hMP m)
      _ = _ := by ring
  let T : (Fin r → ℕ) → ℂ := fun m =>
    ((partialSum i v m - meanP l i v m + Bop l i v m : ℚ) : ℂ) * g m
  have hTb : ∀ m, |((partialSum i v m - meanP l i v m + Bop l i v m : ℚ) : ℝ)| ≤ 3 * (l * C) := by
    intro m
    push_cast
    calc _ ≤ |(partialSum i v m : ℝ) - meanP l i v m| + |(Bop l i v m : ℝ)| := abs_add_le _ _
      _ ≤ (|(partialSum i v m : ℝ)| + |(meanP l i v m : ℝ)|) + |(Bop l i v m : ℝ)| :=
          add_le_add (hsub _ _) le_rfl
      _ ≤ (l * C + l * C) + l * C := add_le_add (add_le_add (hPS m) (hMP m)) (hBb m)
      _ = _ := by ring
  have hinj : Function.Injective (fun m : Fin r → ℕ => m + δ) := add_left_injective δ
  have hgs : Summable (fun m => g (m + δ)) := hg.comp_injective hinj
  have hfd : Summable (fd i g) := by
    have : fd i g = fun m => g (m + δ) - g m := rfl
    rw [this]
    exact hgs.sub hg
  have hsB : Summable (fun m => (Bop l i v m : ℂ) * g m) := summable_cast_mul _ _ hBb hg
  have hsA : Summable (fun m => (Aop l i v m : ℂ) * fd i g m) := summable_cast_mul _ _ hAb hfd
  have hsT : Summable T := summable_cast_mul _ _ hTb hg
  have hsT' : Summable (fun m => T (m + δ)) := hsT.comp_injective hinj
  have hT0 : ∀ m, m i = 0 → T m = 0 := by
    intro m hm
    simp [T, Bop, hm, partialSum_of_zero i v m hm]
  have hBs : ∀ m, Bop l i v (m + δ) = 0 := by
    intro m
    simp [Bop, δ]
  have hpt : ∀ m, (v m : ℂ) * g m =
      ((Bop l i v m : ℂ) * g m - (Aop l i v m : ℂ) * fd i g m) + (T (m + δ) - T m) := by
    intro m
    have h1 := partialSum_succ i v m
    have h2 := partialSumMean_add_single_one l i v m
    have h3 : Bop l i v (m + Pi.single i 1) = 0 := hBs m
    simp only [T, Aop, fd, hδ, h1, h2, h3]
    push_cast
    ring
  have hshift : ∑' m, T (m + δ) = ∑' m, T m := by
    refine hinj.tsum_eq (f := T) ?_
    intro m hm
    have hmi : m i ≠ 0 := fun h0 => hm (hT0 m h0)
    refine ⟨m - δ, ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.sub_apply, δ, Pi.single_eq_same]
      omega
    · simp [δ, Pi.single_apply, hj]
  calc ∑' m, (v m : ℂ) * g m
      = ∑' m, (((Bop l i v m : ℂ) * g m - (Aop l i v m : ℂ) * fd i g m) + (T (m + δ) - T m)) :=
        tsum_congr hpt
    _ = (∑' m, (Bop l i v m : ℂ) * g m - ∑' m, (Aop l i v m : ℂ) * fd i g m) +
          (∑' m, T (m + δ) - ∑' m, T m) := by
        rw [(hsB.sub hsA).tsum_add (hsT'.sub hsT), hsB.tsum_sub hsA, hsT'.tsum_sub hsT]
    _ = _ := by rw [hshift, sub_self, add_zero]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.StepIdentity
