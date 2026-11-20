import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtInUJLeOfSignColumnsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNetCardLeOfSubsetClosedBall
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace

namespace GlobalTheory.BallVol

/- English proof (translation)
The claim follows from `(pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 ((f1auxiliary_entry_le g i j).trans hg)`.
-/
lemma entry_le {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hR : 0 ≤ R) (hg : hs g ≤ R ^ 2)
    (i j : Fin n) : ‖g i j‖ ≤ R :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 ((f1auxiliary_entry_le g i j).trans hg)

/- English proof (translation)
Establish `: uMat g⁻¹ * uMat g = uMat (g⁻¹ * g)` using `rfl`. Rewrite using `[this, inv_mul_cancel]`. Both sides reduce to the same expression.
-/
lemma inv_mul_uMat {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  have : uMat g⁻¹ * uMat g = uMat (g⁻¹ * g) := rfl
  rw [this, inv_mul_cancel]; rfl

/- English proof (translation)
Establish `h1` using `(uJInv n ε (uMat g) g.2).1`. Establish `h2 : uMat g⁻¹ = Jm ε * (uMat g)ᴴ * Jm ε`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2]`. Unfold `Jm`.

Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma norm_inv_entry {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) (i k : Fin n) :
    ‖uMat g⁻¹ i k‖ = ‖uMat g k i‖ := by
  have h1 := (uJInv n ε (uMat g) g.2).1
  have h2 : uMat g⁻¹ = Jm ε * (uMat g)ᴴ * Jm ε := by
    calc uMat g⁻¹ = uMat g⁻¹ * (uMat g * (Jm ε * (uMat g)ᴴ * Jm ε)) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, inv_mul_uMat, Matrix.one_mul]
  rw [h2]
  unfold Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `e : uMat (t⁻¹ * g) = 1 + uMat t⁻¹ * (uMat g - uMat t)`. Rewrite using `[Matrix.mul_sub, inv_mul_uMat]`. Establish `: uMat (t⁻¹ * g) = uMat t⁻¹ * uMat g` using `rfl`. Rewrite using `[this]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e, Matrix.add_apply, Matrix.mul_apply]`. Establish `h3 : ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ 1`. Apply the tactic sequence `rw [Matrix.one_apply]; split_ifs <;> simp`. Use `(norm_add_le _ _).trans (add_le_add h3 ?_)` and prove the remaining obligations. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun k _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_inv_entry, Matrix.sub_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `_ = n := by simp`.
-/
lemma close_entry {n : ℕ} {ε : Fin n → Bool} (g t : UJ ε) {R : ℝ} (hR : 0 < R)
    (ht : hsG t ≤ R ^ 2) (j : Fin n) (hj : ∀ k, ‖uMat g k j - uMat t k j‖ ≤ 1 / R) (i : Fin n) :
    ‖uMat (t⁻¹ * g) i j‖ ≤ 1 + n := by
  have e : uMat (t⁻¹ * g) = 1 + uMat t⁻¹ * (uMat g - uMat t) := by
    rw [Matrix.mul_sub, inv_mul_uMat]
    have : uMat (t⁻¹ * g) = uMat t⁻¹ * uMat g := rfl
    rw [this]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply]
  have h3 : ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  refine (norm_add_le _ _).trans (add_le_add h3 ?_)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖uMat t⁻¹ i k * (uMat g - uMat t) k j‖ ≤ ∑ _k : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_inv_entry, Matrix.sub_apply]
        calc _ ≤ R * (1 / R) :=
              mul_le_mul (entry_le hR.le ht k i) (hj k) (norm_nonneg _) hR.le
          _ = 1 := by field_simp
    _ = n := by simp

/- English proof (translation)
Use `set q := (univ.filter fun a => ε a = s).card with hq`. Set `E` to `Fin n → {j // ε j = s} → ℂ`. Establish `hfr : Module.finrank ℝ E = 2 * n * q`. Simplify using `only [E, Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Fintype.card_subtype, ← hq]`. Expand and normalize the polynomial expressions, which then agree.

Set `Y : UJ ε → E` to `fun g i j => uMat g i j.1`. Set `W : Set (UJ ε)` to `{g | hsG g ≤ n + 4 * (n * (n * (1 + n) ^ 2))}`. Establish `hW : muG ε W < ⊤` using `ballFinite n ε _`. Use `⟨3 ^ (2 * n * q) * (muG ε W).toReal, by positivity, fun R hR => ?_⟩` and prove the remaining obligations. Establish `hR0 : 0 < R` using `by linarith`.

Use `set S : Set (UJ ε) := {g | hsG g ≤ R ^ 2} with hS`. Establish `hsub : Y '' S ⊆ Metric.closedBall 0 R`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Rewrite using `[mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0.le]`. Introduce `i`.

Rewrite using `[pi_norm_le_iff_of_nonneg hR0.le]`. Introduce `j`. Conclude with `entry_le hR0.le hg i j.1`. Take `⟨T, hT1, hT2, hT3⟩` from `GlobalTheory.exists_net_card_le_of_subset_closedBall E (Y '' S) R (1 / R) (by positivity) hR0.le hsub`. Establish `hch : ∀ x : E, ∃ t : UJ ε, x ∈ T → t ∈ S ∧ Y t = x`.

Introduce `x`. Distinguish the cases in `hx : x ∈ T`. Take `⟨t, ht, rfl⟩` from `hT1 hx`. Conclude with `⟨t, fun _ => ⟨ht, rfl⟩⟩`. Conclude with `⟨1, fun h => absurd h hx⟩`.

Use `choose τ hτ using hch`. Establish `hcov : S ⊆ ⋃ x ∈ T, (fun g => (τ x)⁻¹ * g) ⁻¹' W`. Introduce `g hg`. Take `⟨x, hx, hd⟩` from `hT3 (Y g) ⟨g, hg, rfl⟩`. Take `⟨h1, h2⟩` from `hτ x hx`.

Simplify using `only [Set.mem_iUnion]`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Use `show hs (uMat ((τ x)⁻¹ * g)) ≤ _`. Use `(GlobalTheory.T.hilbertSchmidt_inUJ_le_of_sign_columns n ε s _ ((τ x)⁻¹ * g).2).trans ?_` and prove the remaining obligations. Use `gcongr`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_` and prove the remaining obligations. Use `pow_le_pow_left₀ (norm_nonneg _) ?_ 2` and prove the remaining obligations. Apply the tactic sequence `refine close_entry g (τ x) hR0 h1 j (fun k => ?_) i`. Establish `hj' : ε j = s` using `(Finset.mem_filter.1 hj).2`.

Rewrite `hd` using `[← h2, dist_eq_norm]`. Conclude with `((norm_le_pi_norm ((Y g - Y (τ x)) k) ⟨j, hj'⟩).trans (norm_le_pi_norm (Y g - Y (τ x)) k)).trans hd`. Use `_ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ((1 : ℝ) + n) ^ 2 := Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity`. Use `_ = _ := by simp`. Establish `hcard : (T.card : ℝ) ≤ 3 ^ (2 * n * q) * R ^ (4 * n * q)`.

Use `hT2.trans ?_` and prove the remaining obligations. Rewrite using `[hfr, show 4 * n * q = 2 * (2 * n * q) by ring, pow_mul R, ← mul_pow]`. Use `pow_le_pow_left₀ (by positivity) ?_ _` and prove the remaining obligations. Establish `: 2 * R / (1 / R) = 2 * R ^ 2` using `by field_simp`. Rewrite using `[this]`.

Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hW.ne, ENNReal.ofReal_natCast]`. Use `_ ≤ _ := by`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma vol_sign (n : ℕ) (ε : Fin n → Bool) (s : Bool) : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
    muG ε {g | hsG g ≤ R ^ 2} ≤
      ENNReal.ofReal (C * R ^ (4 * n * (univ.filter fun a => ε a = s).card)) := by
  classical
  set q := (univ.filter fun a => ε a = s).card with hq
  let E := Fin n → {j // ε j = s} → ℂ
  have hfr : Module.finrank ℝ E = 2 * n * q := by
    simp only [E, Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Fintype.card_subtype, ← hq]
    ring
  let Y : UJ ε → E := fun g i j => uMat g i j.1
  let W : Set (UJ ε) := {g | hsG g ≤ n + 4 * (n * (n * (1 + n) ^ 2))}
  have hW : muG ε W < ⊤ := ballFinite n ε _
  refine ⟨3 ^ (2 * n * q) * (muG ε W).toReal, by positivity, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  set S : Set (UJ ε) := {g | hsG g ≤ R ^ 2} with hS
  have hsub : Y '' S ⊆ Metric.closedBall 0 R := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0.le]
    intro i
    rw [pi_norm_le_iff_of_nonneg hR0.le]
    intro j
    exact entry_le hR0.le hg i j.1
  obtain ⟨T, hT1, hT2, hT3⟩ := GlobalTheory.exists_net_card_le_of_subset_closedBall E (Y '' S) R (1 / R) (by positivity) hR0.le hsub
  have hch : ∀ x : E, ∃ t : UJ ε, x ∈ T → t ∈ S ∧ Y t = x := by
    intro x
    by_cases hx : x ∈ T
    · obtain ⟨t, ht, rfl⟩ := hT1 hx
      exact ⟨t, fun _ => ⟨ht, rfl⟩⟩
    · exact ⟨1, fun h => absurd h hx⟩
  choose τ hτ using hch
  have hcov : S ⊆ ⋃ x ∈ T, (fun g => (τ x)⁻¹ * g) ⁻¹' W := by
    intro g hg
    obtain ⟨x, hx, hd⟩ := hT3 (Y g) ⟨g, hg, rfl⟩
    obtain ⟨h1, h2⟩ := hτ x hx
    simp only [Set.mem_iUnion]
    refine ⟨x, hx, ?_⟩
    show hs (uMat ((τ x)⁻¹ * g)) ≤ _
    refine (GlobalTheory.T.hilbertSchmidt_inUJ_le_of_sign_columns n ε s _ ((τ x)⁻¹ * g).2).trans ?_
    gcongr
    calc ∑ i, ∑ j ∈ univ.filter (fun j => ε j = s), ‖uMat ((τ x)⁻¹ * g) i j‖ ^ 2
        ≤ ∑ _i : Fin n, ∑ _j ∈ univ.filter (fun j => ε j = s), ((1 : ℝ) + n) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          refine close_entry g (τ x) hR0 h1 j (fun k => ?_) i
          have hj' : ε j = s := (Finset.mem_filter.1 hj).2
          rw [← h2, dist_eq_norm] at hd
          exact ((norm_le_pi_norm ((Y g - Y (τ x)) k) ⟨j, hj'⟩).trans
            (norm_le_pi_norm (Y g - Y (τ x)) k)).trans hd
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ((1 : ℝ) + n) ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) fun _ _ _ => by positivity
      _ = _ := by simp
  have hcard : (T.card : ℝ) ≤ 3 ^ (2 * n * q) * R ^ (4 * n * q) := by
    refine hT2.trans ?_
    rw [hfr, show 4 * n * q = 2 * (2 * n * q) by ring, pow_mul R, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : 2 * R / (1 / R) = 2 * R ^ 2 := by field_simp
    rw [this]; nlinarith
  calc muG ε S ≤ muG ε (⋃ x ∈ T, (fun g => (τ x)⁻¹ * g) ⁻¹' W) := measure_mono hcov
    _ ≤ ∑ x ∈ T, muG ε ((fun g => (τ x)⁻¹ * g) ⁻¹' W) := measure_biUnion_finset_le _ _
    _ = ∑ _x ∈ T, muG ε W := Finset.sum_congr rfl fun x _ => measure_preimage_mul _ _ _
    _ = ENNReal.ofReal ((T.card : ℝ) * (muG ε W).toReal) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_toReal hW.ne, ENNReal.ofReal_natCast]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (T.card : ℝ) * (muG ε W).toReal
            ≤ 3 ^ (2 * n * q) * R ^ (4 * n * q) * (muG ε W).toReal := by gcongr
          _ = _ := by ring

/- English proof (translation)
Establish `h1 : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)‖ ≤ Real.exp r` using `Real.le_exp_of_log_le h`. Establish `h2 : ∀ i j, ‖g i j‖ ≤ Real.exp r`. Introduce `i j`. Establish `h3` using `(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)).le_opNorm (EuclideanSpace.single j (1 : ℂ))`. Establish `h4` using `PiLp.norm_apply_le ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)) (EuclideanSpace.single j (1 : ℂ))) i`.

Establish `h5 : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)) (EuclideanSpace.single j (1 : ℂ)) i = g i j`. Simplify using `[Matrix.toLpLin_apply]`. Rewrite `h4` using `[h5]`. Establish `h6 : ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ (Fin n))‖ = 1` using `by simp`. Rewrite `h3` using `[h6, mul_one]`.

Conclude with `h4.trans (h3.trans h1)`. Establish `hp` using `Real.exp_pos r`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma hs_le_of_dOp {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (h : dOp g ≤ r) :
    hs g ≤ ((n + 1) * Real.exp r) ^ 2 := by
  have h1 : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)‖ ≤ Real.exp r :=
    Real.le_exp_of_log_le h
  have h2 : ∀ i j, ‖g i j‖ ≤ Real.exp r := by
    intro i j
    have h3 := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)).le_opNorm
      (EuclideanSpace.single j (1 : ℂ))
    have h4 := PiLp.norm_apply_le ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g))
      (EuclideanSpace.single j (1 : ℂ))) i
    have h5 : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g))
      (EuclideanSpace.single j (1 : ℂ)) i = g i j := by
      simp [Matrix.toLpLin_apply]
    rw [h5] at h4
    have h6 : ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ (Fin n))‖ = 1 := by simp
    rw [h6, mul_one] at h3
    exact h4.trans (h3.trans h1)
  have hp := Real.exp_pos r
  calc hs g ≤ ∑ _i : Fin n, ∑ _j : Fin n, Real.exp r ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h2 i j) 2
    _ = (n * Real.exp r) ^ 2 := by simp; ring
    _ ≤ _ := by gcongr; linarith

/- English proof (translation)
Introduce `n ε`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs'⟩ : ∃ s : Bool, rkR ε = (univ.filter fun a => ε a = s).card := by`. Unfold `rkR`. Break down `min_choice (univ.filter fun a => ε a = true).card (univ.filter fun a => ε a = false).card with h | h` into its components or cases. Conclude with `⟨true, h⟩`.

Conclude with `⟨false, h⟩`. Take `⟨C, hC, h⟩` from `vol_sign n ε s`. Rewrite `h` using `[← hs']`. Establish `hn : (1 : ℝ) ≤ n + 1` using `by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith`. Establish `hn' : (1 : ℝ) ≤ (n + 1) ^ (4 * n * rkR ε)` using `one_le_pow₀ hn`.

Use `⟨C * (n + 1) ^ (4 * n * rkR ε), fun R hR => (h R hR).trans ?_, fun r hr => ?_⟩` and prove the remaining obligations. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `: 0 ≤ R ^ (4 * n * rkR ε)` using `by positivity`. Conclude with `mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC hn') this`. Establish `he : 1 ≤ Real.exp r` using `Real.one_le_exp hr`.

Establish `h1` using `h ((n + 1) * Real.exp r) (one_le_mul_of_one_le_of_one_le hn he)`. Use `(measure_mono fun g hg => ?_).trans (h1.trans (le_of_eq ?_))` and prove the remaining obligations. Conclude with `hs_le_of_dOp hg`. Rewrite using `[mul_pow, ← Real.exp_nat_mul, ← mul_assoc]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem ballVol : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ C : ℝ, (∀ R : ℝ, 1 ≤ R → muG ε {g | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (4 * n * rkR ε))) ∧ ∀ r : ℝ, 0 ≤ r → muG ε {g | dOp (uMat g) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r)) := by
  intro n ε
  obtain ⟨s, hs'⟩ : ∃ s : Bool, rkR ε = (univ.filter fun a => ε a = s).card := by
    unfold rkR
    rcases min_choice (univ.filter fun a => ε a = true).card
      (univ.filter fun a => ε a = false).card with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  obtain ⟨C, hC, h⟩ := vol_sign n ε s
  rw [← hs'] at h
  have hn : (1 : ℝ) ≤ n + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hn' : (1 : ℝ) ≤ (n + 1) ^ (4 * n * rkR ε) := one_le_pow₀ hn
  refine ⟨C * (n + 1) ^ (4 * n * rkR ε), fun R hR => (h R hR).trans ?_, fun r hr => ?_⟩
  · refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ R ^ (4 * n * rkR ε) := by positivity
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC hn') this
  · have he : 1 ≤ Real.exp r := Real.one_le_exp hr
    have h1 := h ((n + 1) * Real.exp r) (one_le_mul_of_one_le_of_one_le hn he)
    refine (measure_mono fun g hg => ?_).trans (h1.trans (le_of_eq ?_))
    · exact hs_le_of_dOp hg
    · rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc]
      push_cast
      rfl

end GlobalTheory.BallVol
