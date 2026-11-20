import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => exact Summable.of_finite`. Consider the case `succ r ih`. Establish `h2` using `Summable.mul_of_nonneg hf ih (fun n => h0 n) (fun m => Finset.prod_nonneg fun i _ => h0 (m i))`. Rewrite using `[← (Fin.consEquiv (fun _ : Fin (r + 1) => ℕ)).summable_iff]`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using `[Fin.consEquiv, Fin.prod_univ_succ]`.
-/
theorem summable_prod_fin {f : ℕ → ℝ} (hf : Summable f) (h0 : ∀ n, 0 ≤ f n) (r : ℕ) :
    Summable (fun m : Fin r → ℕ => ∏ i, f (m i)) := by
  induction r with
  | zero => exact Summable.of_finite
  | succ r ih =>
    have h2 := Summable.mul_of_nonneg hf ih (fun n => h0 n)
      (fun m => Finset.prod_nonneg fun i _ => h0 (m i))
    rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => ℕ)).summable_iff]
    convert h2 using 1
    funext x
    simp [Fin.consEquiv, Fin.prod_univ_succ]

/- English proof (translation)
Set `T : Finset ℝ` to `Finset.univ.image b ∪ Finset.univ.image (fun p : ι × Fin r => a p.1 p.2)`. Distinguish the cases in `hT : T.Nonempty`. Use `⟨T.min' hT, ?_, fun j => T.min'_le _ ?_, fun j i => T.min'_le _ ?_⟩` and prove the remaining obligations. Establish `h` using `T.min'_mem hT`. Simplify using `only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h`.

Break down `h with ⟨j, hj⟩ | ⟨⟨j, i⟩, hj⟩` into its components or cases. Rewrite using `[← hj]`. Conclude with `hb j`. Rewrite using `[← hj]`. Conclude with `ha j i`.

Simplify using `only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]`. Conclude with `Or.inl ⟨j, rfl⟩`. Simplify using `only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]`. Conclude with `Or.inr ⟨(j, i), rfl⟩`. Use `⟨1, one_pos, fun j => ?_, fun j i => ?_⟩` and prove the remaining obligations.

Conclude with `absurd ⟨b j, by simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]; exact Or.inl ⟨j, rfl⟩⟩ hT`. Conclude with `absurd ⟨b j, by simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]; exact Or.inl ⟨j, rfl⟩⟩ hT`.
-/
private theorem exists_pos_lower_bound_of_forall_pos {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ)
    (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) :
    ∃ c : ℝ, 0 < c ∧ (∀ j, c ≤ b j) ∧ ∀ j i, c ≤ a j i := by
  classical
  let T : Finset ℝ := Finset.univ.image b ∪ Finset.univ.image (fun p : ι × Fin r => a p.1 p.2)
  by_cases hT : T.Nonempty
  · refine ⟨T.min' hT, ?_, fun j => T.min'_le _ ?_, fun j i => T.min'_le _ ?_⟩
    · have h := T.min'_mem hT
      simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
      rcases h with ⟨j, hj⟩ | ⟨⟨j, i⟩, hj⟩
      · rw [← hj]; exact hb j
      · rw [← hj]; exact ha j i
    · simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl ⟨j, rfl⟩
    · simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inr ⟨(j, i), rfl⟩
  · refine ⟨1, one_pos, fun j => ?_, fun j i => ?_⟩
    · exact absurd ⟨b j, by simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]; exact Or.inl ⟨j, rfl⟩⟩ hT
    · exact absurd ⟨b j, by simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]; exact Or.inl ⟨j, rfl⟩⟩ hT

/- English proof (translation)
Introduce `ι _ r a b hr ha hb s hs`. Take `⟨c, hc0, hcb, hca⟩` from `exists_pos_lower_bound_of_forall_pos a b ha hb`. Establish `hσ0 : 0 < s.re` using `by linarith`. Establish `hf : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-s.re))`. Establish `h` using `(summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))`.

Simplify `h` using `[Nat.cast_add, Nat.cast_one]`. Establish `hC : 0 ≤ (c ^ (-s.re)) ^ Fintype.card ι` using `pow_nonneg (Real.rpow_nonneg hc0.le _) _`. Establish `hg` using `(summable_prod_fin hf (fun k => Real.rpow_nonneg (by positivity) _) r).mul_left ((c ^ (-s.re)) ^ Fintype.card ι)`. Establish `key : ∀ {x y : ℝ}, 0 < x → x ≤ y → y ^ (-s.re) ≤ x ^ (-s.re)` using `fun hx hxy => by`. Rewrite using `[Real.rpow_neg hx.le, Real.rpow_neg (hx.le.trans hxy)]`.

Conclude with `inv_anti₀ (Real.rpow_pos_of_pos hx _) (Real.rpow_le_rpow hx.le hxy hσ0.le)`. Use `Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hg)` and prove the remaining obligations. Take `⟨S, hSdef⟩ : ∃ S : ℝ, S = 1 + ∑ i, (m i : ℝ)` from `⟨_, rfl⟩`. Establish `hsum0 : 0 ≤ ∑ i, (m i : ℝ)` using `Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (m i))`. Establish `hS1 : 1 ≤ S` using `by rw [hSdef]; linarith`.

Establish `hS0 : 0 < S` using `by linarith`. Establish `hL : ∀ j, c * S ≤ b j + ∑ i, a j i * (m i : ℝ)`. Introduce `j`. Rewrite using `[hSdef, mul_add, mul_one, Finset.mul_sum]`. Apply `add_le_add (hcb j)` to reduce the goal to its premises.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Conclude with `mul_le_mul_of_nonneg_right (hca j i) (Nat.cast_nonneg _)`. Establish `hLpos : ∀ j, 0 < b j + ∑ i, a j i * (m i : ℝ)` using `fun j => lt_of_lt_of_le (mul_pos hc0 hS0) (hL j)`. Establish `hv1 : S ^ (-s.re) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hS1 (by linarith)`.

Establish `hv0 : 0 ≤ S ^ (-s.re)` using `Real.rpow_nonneg hS0.le _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[coneTerm, norm_prod]`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Complex.norm_cpow_eq_rpow_re_of_pos (hLpos j), Complex.neg_re]`.

Use `_ ≤ ∏ _j : ι, (c * S) ^ (-s.re) := Finset.prod_le_prod (fun j _ => Real.rpow_nonneg (hLpos j).le _) (fun j _ => key (mul_pos hc0 hS0) (hL j))`. Use `_ = (c ^ (-s.re)) ^ Fintype.card ι * (S ^ (-s.re)) ^ Fintype.card ι := by`. Rewrite using `[Finset.prod_const, Finset.card_univ, Real.mul_rpow hc0.le hS0.le, mul_pow]`. Use `_ ≤ (c ^ (-s.re)) ^ Fintype.card ι * (S ^ (-s.re)) ^ r := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hv0 hv1 hr) hC`. Use `_ = (c ^ (-s.re)) ^ Fintype.card ι * ∏ _i : Fin r, S ^ (-s.re) := by`.

Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Use `_ ≤ (c ^ (-s.re)) ^ Fintype.card ι * ∏ i, ((m i : ℝ) + 1) ^ (-s.re) := by`. Apply `mul_le_mul_of_nonneg_left _ hC` to reduce the goal to its premises. Apply `Finset.prod_le_prod (fun i _ => hv0)` to reduce the goal to its premises. Introduce `i _`.

Apply `key (by positivity)` to reduce the goal to its premises. Establish `hi : (m i : ℝ) ≤ ∑ k, (m k : ℝ)` using `Finset.single_le_sum (fun k _ => Nat.cast_nonneg (m k)) (Finset.mem_univ i)`. Rewrite using `[hSdef]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem coneTerm_summable : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ),
    r ≤ Fintype.card ι → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ s : ℂ, 1 < s.re →
    Summable (coneTerm a b s) := by
  intro ι _ r a b hr ha hb s hs
  obtain ⟨c, hc0, hcb, hca⟩ := exists_pos_lower_bound_of_forall_pos a b ha hb
  have hσ0 : 0 < s.re := by linarith
  have hf : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-s.re)) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hC : 0 ≤ (c ^ (-s.re)) ^ Fintype.card ι := pow_nonneg (Real.rpow_nonneg hc0.le _) _
  have hg := (summable_prod_fin hf (fun k => Real.rpow_nonneg (by positivity) _) r).mul_left
    ((c ^ (-s.re)) ^ Fintype.card ι)
  have key : ∀ {x y : ℝ}, 0 < x → x ≤ y → y ^ (-s.re) ≤ x ^ (-s.re) := fun hx hxy => by
    rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.le.trans hxy)]
    exact inv_anti₀ (Real.rpow_pos_of_pos hx _) (Real.rpow_le_rpow hx.le hxy hσ0.le)
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hg)
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = 1 + ∑ i, (m i : ℝ) := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, (m i : ℝ) := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (m i))
  have hS1 : 1 ≤ S := by rw [hSdef]; linarith
  have hS0 : 0 < S := by linarith
  have hL : ∀ j, c * S ≤ b j + ∑ i, a j i * (m i : ℝ) := by
    intro j
    rw [hSdef, mul_add, mul_one, Finset.mul_sum]
    apply add_le_add (hcb j)
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hca j i) (Nat.cast_nonneg _)
  have hLpos : ∀ j, 0 < b j + ∑ i, a j i * (m i : ℝ) := fun j => lt_of_lt_of_le (mul_pos hc0 hS0) (hL j)
  have hv1 : S ^ (-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hS1 (by linarith)
  have hv0 : 0 ≤ S ^ (-s.re) := Real.rpow_nonneg hS0.le _
  calc ‖coneTerm a b s m‖ = ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ (-s.re) := by
        rw [coneTerm, norm_prod]
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (hLpos j), Complex.neg_re]
    _ ≤ ∏ _j : ι, (c * S) ^ (-s.re) :=
        Finset.prod_le_prod (fun j _ => Real.rpow_nonneg (hLpos j).le _)
          (fun j _ => key (mul_pos hc0 hS0) (hL j))
    _ = (c ^ (-s.re)) ^ Fintype.card ι * (S ^ (-s.re)) ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ, Real.mul_rpow hc0.le hS0.le, mul_pow]
    _ ≤ (c ^ (-s.re)) ^ Fintype.card ι * (S ^ (-s.re)) ^ r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hv0 hv1 hr) hC
    _ = (c ^ (-s.re)) ^ Fintype.card ι * ∏ _i : Fin r, S ^ (-s.re) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (c ^ (-s.re)) ^ Fintype.card ι * ∏ i, ((m i : ℝ) + 1) ^ (-s.re) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Finset.prod_le_prod (fun i _ => hv0)
        intro i _
        apply key (by positivity)
        have hi : (m i : ℝ) ≤ ∑ k, (m k : ℝ) :=
          Finset.single_le_sum (fun k _ => Nat.cast_nonneg (m k)) (Finset.mem_univ i)
        rw [hSdef]
        linarith

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
