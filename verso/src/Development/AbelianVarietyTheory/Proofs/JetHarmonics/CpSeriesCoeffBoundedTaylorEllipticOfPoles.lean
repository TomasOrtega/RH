import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEllipticFunctionMulProdEqXy

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.EllBdd

variable {q : ℕ} [Fact q.Prime]

/- English proof (translation)
Introduce `n`. Rewrite using `[coeff_C]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem bd_C (a : ℂ_[q]) : Bd ‖a‖ (C a : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs <;> simp

/- English proof (translation)
Introduce `n` and use `(h n).trans hAB`.
-/
theorem bd_mono {A B : ℝ} {f : ℂ_[q]⟦X⟧} (h : Bd A f) (hAB : A ≤ B) : Bd B f :=
  fun n => (h n).trans hAB

/- English proof (translation)
Introduce `n`. Rewrite using `[coeff_X_pow]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem bd_X_pow (k : ℕ) : Bd 1 (X ^ k : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_X_pow]
  split_ifs <;> simp

/- English proof (translation)
Simplify using `using ((sup_norm_laws q).1 f g 1 1 hf hg).2`.
-/
theorem bd_one_mul {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f * g) := by
  simpa using ((sup_norm_laws q).1 f g 1 1 hf hg).2

/- English proof (translation)
Simplify using `using ((sup_norm_laws q).1 f g 1 1 hf hg).1`.
-/
theorem bd_one_add {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f + g) := by
  simpa using ((sup_norm_laws q).1 f g 1 1 hf hg).1

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using (bd_X_pow (q := q) 0)`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `bd_one_mul ih hf`.
-/
theorem bd_one_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (k : ℕ) : Bd 1 (f ^ k) := by
  induction k with
  | zero => simpa using (bd_X_pow (q := q) 0)
  | succ k ih => rw [pow_succ]; exact bd_one_mul ih hf

/- English proof (translation)
The claim follows from `Finset.sum_induction f (Bd 1) (fun _ _ => bd_one_add) (fun n => by simp) h`.
-/
theorem bd_one_sum {α : Type*} (s : Finset α) (f : α → ℂ_[q]⟦X⟧) (h : ∀ i ∈ s, Bd 1 (f i)) :
    Bd 1 (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Bd 1) (fun _ _ => bd_one_add) (fun n => by simp) h

/- English proof (translation)
Take `⟨A, hA⟩` from `hf`. Take `⟨B, hB⟩` from `hg`. Conclude with `⟨_, ((sup_norm_laws q).1 f g A B hA hB).2⟩`.
-/
theorem bdd_mul {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f * g) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hA hB).2⟩

/- English proof (translation)
Take `⟨A, hA⟩` from `hf`. Take `⟨B, hB⟩` from `hg`. Conclude with `⟨_, ((sup_norm_laws q).1 f g A B hA hB).1⟩`.
-/
theorem bdd_add {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hA hB).1⟩

/- English proof (translation)
The claim follows from `Finset.sum_induction f Bdd (fun _ _ => bdd_add) ⟨0, fun n => by simp⟩ h`.
-/
theorem bdd_sum {α : Type*} (s : Finset α) (f : α → ℂ_[q]⟦X⟧) (h : ∀ i ∈ s, Bdd (f i)) :
    Bdd (∑ i ∈ s, f i) :=
  Finset.sum_induction f Bdd (fun _ _ => bdd_add) ⟨0, fun n => by simp⟩ h

/- English proof (translation)
Establish `h1 : tay (fun _ => 1) = 1`. Use extensionality with `n`. Rewrite using `[tay, coeff_mk, coeff_one, iteratedDeriv_const]`. Use `split_ifs with h`. Simplify using `[h]`.

Simplify using the standard rewrite rules. Establish `hs : HasSubst ℓ` using `HasSubst.of_constantCoeff_zero' hℓ`. Rewrite using `[hat, h1, map_one, ← coe_substAlgHom hs, map_one]`.
-/
theorem hat_one (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hℓ : constantCoeff ℓ = 0) :
    hat ι ℓ (fun _ => 1) = 1 := by
  have h1 : tay (fun _ => 1) = 1 := by
    ext n
    rw [tay, coeff_mk, coeff_one, iteratedDeriv_const]
    split_ifs with h
    · simp [h]
    · simp
  have hs : HasSubst ℓ := HasSubst.of_constantCoeff_zero' hℓ
  rw [hat, h1, map_one, ← coe_substAlgHom hs, map_one]

/- English proof (translation)
Use `revert n`. Use `Finset.prod_induction _ (fun p : Polynomial ℂ => ∀ n, ‖ι (p.coeff n)‖ ≤ 1) ?_ ?_ ?_` and prove the remaining obligations. Introduce `p r hp hr n`. Rewrite using `[Polynomial.coeff_mul, map_sum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_` and prove the remaining obligations.

Introduce `x _`. Rewrite using `[map_mul, norm_mul]`. Conclude with `mul_le_one₀ (hp _) (norm_nonneg _) (hr _)`. Introduce `n`. Rewrite using `[Polynomial.coeff_one]`.

Apply the tactic sequence `split_ifs <;> simp`. Introduce `i _ n`. Break down `n with _ | _ | n` into its components or cases. Simplify using `using ha i`. Simplify using the standard rewrite rules.

Simplify using `[Polynomial.coeff_X]`.
-/
theorem prod_coeff_le (ι : ℂ ≃+* ℂ_[q]) {m : ℕ} (a : Fin m → ℂ) (ha : ∀ i, ‖ι (a i)‖ ≤ 1) (n : ℕ) :
    ‖ι ((∏ i, (Polynomial.X - Polynomial.C (a i))).coeff n)‖ ≤ 1 := by
  revert n
  refine Finset.prod_induction _ (fun p : Polynomial ℂ => ∀ n, ‖ι (p.coeff n)‖ ≤ 1) ?_ ?_ ?_
  · intro p r hp hr n
    rw [Polynomial.coeff_mul, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
    intro x _
    rw [map_mul, norm_mul]
    exact mul_le_one₀ (hp _) (norm_nonneg _) (hr _)
  · intro n
    rw [Polynomial.coeff_one]
    split_ifs <;> simp
  · intro i _ n
    rcases n with _ | _ | n
    · simpa using ha i
    · simp
    · simp [Polynomial.coeff_X]

/- English proof (translation)
Introduce `q _ M ℓ φ hC hE hA hP`. Take `⟨m, P, A, B, hPi, hz⟩` from `GlobalTheory.EllipticModel.exists_mul_prod_eq_xy q M φ hC.1 hE`. Take `⟨-, v, xs, ys, -, hxs, hys, -, hx0, -, -, -, -, hmain⟩` from `GlobalTheory.MomOne.ChartXY.chart_xy q M ℓ hC`. Use `set D : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hD`. Establish `hmon : D.Monic` using `Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _`.

Establish `hdeg : D.natDegree = m`. Rewrite using `[hD, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]`. Simplify using the standard rewrite rules. Establish `hint : ∀ n, ‖M.ι (D.coeff n)‖ ≤ 1`. Use `prod_coeff_le M.ι (fun i => M.x (P i)) fun i => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Conclude with `hP _ (hPi i).2 (Or.inr (not_le.mp h))`. Establish `key` using `hmain φ A B (max A.natDegree B.natDegree) hA (le_max_left _ _) (le_max_right _ _) (fun _ => 1) analyticAt_const D m hdeg.le (by simpa using hz 0)`. Use `set k := max A.natDegree B.natDegree`. Use `set S := ∑ i ∈ Finset.range (m + 1), C (M.ι (D.coeff i)) * X ^ (2 * (m - i)) * xs ^ i with hS`.

Establish `hS1 : Bd 1 S` using `bd_one_sum _ _ fun i _ => bd_one_mul (bd_one_mul (bd_mono (bd_C _) (hint i)) (bd_X_pow _)) (bd_one_pow hxs i)`. Establish `hS0 : ‖constantCoeff S‖ = 1`. Rewrite using `[hS, Finset.sum_range_succ, map_add, map_sum, Finset.sum_eq_zero, zero_add]`. Establish `: D.coeff m = 1` using `by rw [← hdeg]; exact hmon.coeff_natDegree`. Simplify using `[this, hx0]`.

Introduce `i hi`. Establish `: 2 * (m - i) ≠ 0` using `by have := Finset.mem_range.mp hi; omega`. Simplify using `[this]`. Establish `hR : Bdd (hat M.ι ℓ φ * X ^ (2 * k + 3) * S)`. Rewrite using `[key, hat_one M.ι ℓ hC.2.1, one_mul]`.

Use `bdd_mul ⟨_, bd_X_pow _⟩ (bdd_sum _ _ fun i _ => bdd_add ?_ ?_)` and prove the remaining obligations. Conclude with `bdd_mul (bdd_mul ⟨_, bd_C _⟩ ⟨_, bd_X_pow _⟩) ⟨_, bd_one_pow hxs i⟩`. Conclude with `bdd_mul (bdd_mul (bdd_mul ⟨_, bd_C _⟩ ⟨_, bd_X_pow _⟩) ⟨_, bd_one_pow hxs i⟩) ⟨_, hys⟩`. Take `⟨R, hR⟩` from `hR`. Use `⟨R, (sup_norm_laws q).2.2.2.2.2 _ S (2 * k + 3) R hS1 hS0 ?_⟩` and prove the remaining obligations.

Rewrite using `[show X ^ (2 * k + 3) * S * hat M.ι ℓ φ = hat M.ι ℓ φ * X ^ (2 * k + 3) * S by ring]` and apply the resulting hypothesis.
-/
theorem bdd_hat_of_ell : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → Bdd (hat M.ι ℓ φ) := by
  intro q _ M ℓ φ hC hE hA hP
  obtain ⟨m, P, A, B, hPi, hz⟩ := GlobalTheory.EllipticModel.exists_mul_prod_eq_xy q M φ hC.1 hE
  obtain ⟨-, v, xs, ys, -, hxs, hys, -, hx0, -, -, -, -, hmain⟩ := GlobalTheory.MomOne.ChartXY.chart_xy q M ℓ hC
  set D : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hD
  have hmon : D.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hdeg : D.natDegree = m := by
    rw [hD, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  have hint : ∀ n, ‖M.ι (D.coeff n)‖ ≤ 1 := by
    refine prod_coeff_le M.ι (fun i => M.x (P i)) fun i => ?_
    by_contra h
    exact hP _ (hPi i).2 (Or.inr (not_le.mp h))
  have key := hmain φ A B (max A.natDegree B.natDegree) hA (le_max_left _ _) (le_max_right _ _)
    (fun _ => 1) analyticAt_const D m hdeg.le (by simpa using hz 0)
  set k := max A.natDegree B.natDegree
  set S := ∑ i ∈ Finset.range (m + 1), C (M.ι (D.coeff i)) * X ^ (2 * (m - i)) * xs ^ i with hS
  have hS1 : Bd 1 S := bd_one_sum _ _ fun i _ =>
    bd_one_mul (bd_one_mul (bd_mono (bd_C _) (hint i)) (bd_X_pow _)) (bd_one_pow hxs i)
  have hS0 : ‖constantCoeff S‖ = 1 := by
    rw [hS, Finset.sum_range_succ, map_add, map_sum, Finset.sum_eq_zero, zero_add]
    · have : D.coeff m = 1 := by rw [← hdeg]; exact hmon.coeff_natDegree
      simp [this, hx0]
    · intro i hi
      have : 2 * (m - i) ≠ 0 := by have := Finset.mem_range.mp hi; omega
      simp [this]
  have hR : Bdd (hat M.ι ℓ φ * X ^ (2 * k + 3) * S) := by
    rw [key, hat_one M.ι ℓ hC.2.1, one_mul]
    refine bdd_mul ⟨_, bd_X_pow _⟩ (bdd_sum _ _ fun i _ => bdd_add ?_ ?_)
    · exact bdd_mul (bdd_mul ⟨_, bd_C _⟩ ⟨_, bd_X_pow _⟩) ⟨_, bd_one_pow hxs i⟩
    · exact bdd_mul (bdd_mul (bdd_mul ⟨_, bd_C _⟩ ⟨_, bd_X_pow _⟩) ⟨_, bd_one_pow hxs i⟩) ⟨_, hys⟩
  obtain ⟨R, hR⟩ := hR
  refine ⟨R, (sup_norm_laws q).2.2.2.2.2 _ S (2 * k + 3) R hS1 hS0 ?_⟩
  rwa [show X ^ (2 * k + 3) * S * hat M.ι ℓ φ = hat M.ι ℓ φ * X ^ (2 * k + 3) * S by ring]

end GlobalTheory.MomOne.EllBdd
