import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
import Development.AbelianVarietyTheory.Definitions.Foundations.CthFac
import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperations

noncomputable section

open scoped UpperHalfPlane
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Sieg.EisQ

/- English proof (translation)
Simplify using `only [ee, ← Complex.exp_int_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ee_int_mul' (n : ℤ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  simp only [ee, ← Complex.exp_int_mul]; congr 1; ring

/- English proof (translation)
Establish `hM' : (M : ℤ) ≠ 0` using `by exact_mod_cast hM.ne'`. Use `split_ifs with h`. Take `⟨n, hn⟩` from `h.symm.dvd`. Establish `hA : a + M * n = A` using `by linarith`. Use `hasSum_single (f := fun p : ℤ × ℤ => if p.2 = e ∧ a + M * p.1 = A then w (a + M * p.1) p.2 else 0) (n, e) (fun p hp => by` as an intermediate fact.

Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Apply `hp` to reduce the goal to its premises. Use `Prod.ext ?_ h1` and prove the remaining obligations. Apply `mul_left_cancel₀ hM'` to reduce the goal to its premises.

Simplify using `only`. Use the proof step `linarith)`. Simplify `this` using `[hA]`. Establish `: (fun p : ℤ × ℤ => if p.2 = e ∧ a + M * p.1 = A then w (a + M * p.1) p.2 else 0) = fun _ => 0`. Use function extensionality and compare the values at `p`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨-, h2⟩`. Conclude with `h (Int.ModEq.symm (Int.modEq_iff_dvd.2 ⟨p.1, by linarith⟩))`. Rewrite using `[this]`. Conclude with `hasSum_zero`.
-/
theorem hasSum_point {M : ℕ} (hM : 0 < M) (a A e : ℤ) (w : ℤ → ℤ → ℂ) :
    HasSum (fun p : ℤ × ℤ => if p.2 = e ∧ a + M * p.1 = A then w (a + M * p.1) p.2 else 0)
      (if A ≡ a [ZMOD M] then w A e else 0) := by
  have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  split_ifs with h
  · obtain ⟨n, hn⟩ := h.symm.dvd
    have hA : a + M * n = A := by linarith
    have := hasSum_single (f := fun p : ℤ × ℤ => if p.2 = e ∧ a + M * p.1 = A then w (a + M * p.1) p.2 else 0)
      (n, e) (fun p hp => by
        rw [if_neg]
        rintro ⟨h1, h2⟩
        apply hp
        refine Prod.ext ?_ h1
        apply mul_left_cancel₀ hM'
        simp only
        linarith)
    simpa [hA] using this
  · have : (fun p : ℤ × ℤ => if p.2 = e ∧ a + M * p.1 = A then w (a + M * p.1) p.2 else 0) = fun _ => 0 := by
      funext p
      rw [if_neg]
      rintro ⟨-, h2⟩
      exact h (Int.ModEq.symm (Int.modEq_iff_dvd.2 ⟨p.1, by linarith⟩))
    rw [this]
    exact hasSum_zero

/- English proof (translation)
Establish `key : ∀ d ∈ m.divisors, (((m / d : ℕ) : ℤ)) * d = m ∧ 0 < (d : ℤ)` using `fun d hd => by`. Use `⟨?_, by exact_mod_cast Nat.pos_of_mem_divisors hd⟩` and prove the remaining obligations. Conclude with `Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)` after adjusting the coercions. Use `split_ifs with h`. Establish `hd : e.natAbs ∈ m.divisors`.

Rewrite using `[Nat.mem_divisors]`. Use `⟨?_, hm⟩` and prove the remaining obligations. Rewrite using `[← Int.natCast_dvd_natCast, Int.natAbs_dvd]`. Conclude with `⟨A, by rw [← h, mul_comm]⟩`. Rewrite using `[Finset.sum_eq_single_of_mem _ hd]`.

Take `⟨k1, k2⟩` from `key _ hd`. Generalize the expression as in `((m / e.natAbs : ℕ) : ℤ) = B at *`. Break down `Int.natAbs_eq e with he | he` into its components or cases. Rewrite `k1`, `k2`, the goal using `[← he]`. Establish `: A = B` using `mul_right_cancel₀ k2.ne' (by rw [h, k1])`.

Rewrite using `[if_pos ⟨rfl, this⟩, if_neg (by omega), add_zero]`. Establish `he' : (e.natAbs : ℤ) = -e` using `by omega`. Rewrite `k1`, `k2`, the goal using `[he']`. Establish `: A = -B` using `mul_right_cancel₀ (b := e) (by omega) (by rw [h, ← k1]; ring)`. Rewrite using `[if_neg (by omega), if_pos ⟨by ring, this⟩, zero_add]`.

Introduce `d _ hne`. Rewrite using `[if_neg (by omega), if_neg (by omega), add_zero]`. Use `Finset.sum_eq_zero fun d hd => ?_` and prove the remaining obligations. Take `⟨k1, k2⟩` from `key _ hd`. Rewrite using `[if_neg, if_neg, add_zero]`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `h (by rw [h1, h2, ← k1]; ring)`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `h (by rw [h1, h2, ← k1])`.
-/
theorem sum_div_point {m : ℕ} (hm : m ≠ 0) (A e : ℤ) (v : ℂ) :
    ∑ d ∈ m.divisors, ((if e = (d : ℤ) ∧ A = ((m / d : ℕ) : ℤ) then v else 0) +
      (if e = -(d : ℤ) ∧ A = -((m / d : ℕ) : ℤ) then v else 0)) = if A * e = m then v else 0 := by
  have key : ∀ d ∈ m.divisors, (((m / d : ℕ) : ℤ)) * d = m ∧ 0 < (d : ℤ) := fun d hd => by
    refine ⟨?_, by exact_mod_cast Nat.pos_of_mem_divisors hd⟩
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
  split_ifs with h
  · have hd : e.natAbs ∈ m.divisors := by
      rw [Nat.mem_divisors]
      refine ⟨?_, hm⟩
      rw [← Int.natCast_dvd_natCast, Int.natAbs_dvd]
      exact ⟨A, by rw [← h, mul_comm]⟩
    rw [Finset.sum_eq_single_of_mem _ hd]
    · obtain ⟨k1, k2⟩ := key _ hd
      generalize ((m / e.natAbs : ℕ) : ℤ) = B at *
      rcases Int.natAbs_eq e with he | he
      · rw [← he] at k1 k2 ⊢
        have : A = B := mul_right_cancel₀ k2.ne' (by rw [h, k1])
        rw [if_pos ⟨rfl, this⟩, if_neg (by omega), add_zero]
      · have he' : (e.natAbs : ℤ) = -e := by omega
        rw [he'] at k1 k2 ⊢
        have : A = -B := mul_right_cancel₀ (b := e) (by omega) (by rw [h, ← k1]; ring)
        rw [if_neg (by omega), if_pos ⟨by ring, this⟩, zero_add]
    · intro d _ hne
      rw [if_neg (by omega), if_neg (by omega), add_zero]
  · refine Finset.sum_eq_zero fun d hd => ?_
    obtain ⟨k1, k2⟩ := key _ hd
    rw [if_neg, if_neg, add_zero]
    · rintro ⟨h1, h2⟩
      exact h (by rw [h1, h2, ← k1]; ring)
    · rintro ⟨h1, h2⟩
      exact h (by rw [h1, h2, ← k1])

/- English proof (translation)
Establish `hQ : (0 : ℚ) < M` using `by exact_mod_cast hM`. Establish `hC : (M : ℂ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `hc : (0 < ((a : ℚ) / M + p.1) * p.2) ↔ 0 < (a + M * p.1) * p.2`. Establish `: ((a : ℚ) / M + p.1) * p.2 = (((a + M * p.1) * p.2 : ℤ) : ℚ) / M` using `by push_cast; field_simp`. Rewrite using `[this, div_pos_iff_of_pos_right hQ, Int.cast_pos]`.

Unfold `fTerm`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, hc]`. Use `split_ifs with h`. Rewrite using `[← ee_int_mul', mul_right_comm]`. Use `congr 1`.

Use `congr 1`. Use `congr 2 push_cast`. Clear the denominators using the available nonvanishing facts. Use `congr 1 push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `congr 1 push_cast`. Clear the denominators using the available nonvanishing facts. Both sides reduce to the same expression.
-/
theorem fTerm_eq (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) (τ : ℍ) (p : ℤ × ℤ) :
    fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ p =
      if 0 < (a + M * p.1) * p.2 then
        (Int.sign p.2 : ℂ) * (((a + M * p.1 : ℤ) : ℂ) / M) ^ (j - 1) * ee (1 / (M : ℂ)) ^ (b * p.2) *
          ee ((((a + M * p.1) * p.2 : ℤ) : ℂ) * τ / M)
      else 0 := by
  have hQ : (0 : ℚ) < M := by exact_mod_cast hM
  have hC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hc : (0 < ((a : ℚ) / M + p.1) * p.2) ↔ 0 < (a + M * p.1) * p.2 := by
    have : ((a : ℚ) / M + p.1) * p.2 = (((a + M * p.1) * p.2 : ℤ) : ℚ) / M := by
      push_cast; field_simp
    rw [this, div_pos_iff_of_pos_right hQ, Int.cast_pos]
  unfold fTerm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hc]
  split_ifs with h
  · rw [← ee_int_mul', mul_right_comm]
    congr 1
    · congr 1
      · congr 2
        push_cast; field_simp
      · congr 1
        push_cast; ring
    · congr 1
      push_cast; field_simp
  · rfl

/- English proof (translation)
Use `split_ifs with hm`. Establish `: Set.indicator ((fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat) ⁻¹' {m}) (fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ) = fun _ => 0`. Use function extensionality and compare the values at `p`. Rewrite using `[Set.indicator_apply_eq_zero]`. Introduce `hp`.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at hp`. Rewrite using `[fTerm_eq j hM, if_neg (by omega)]`. Rewrite using `[this, zero_mul]`. Conclude with `hasSum_zero`. Use `set E := Complex.exp (2 * Real.pi * Complex.I * m * τ / M) with hE`.

Set `w : ℤ → ℤ → ℂ` to `fun A e => (Int.sign e : ℂ) * ((A : ℂ) / M) ^ (j - 1) * ee (1 / (M : ℂ)) ^ (b * e) * E`. Establish `h1` using `hasSum_sum (s := m.divisors) fun d _ => (hasSum_point hM a ((m / d : ℕ) : ℤ) (d : ℤ) w).add (hasSum_point hM a (-((m / d : ℕ) : ℤ)) (-(d : ℤ)) w)`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p classical`. Rewrite using `[sum_div_point hm, Set.indicator_apply, fTerm_eq j hM]`.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff]`. Distinguish the cases in `h : (a + M * p.1) * p.2 = m`. Rewrite using `[if_pos (by omega), if_pos (by omega), if_pos h, h]`. Simplify using `only [w, hE, ee]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (by omega), if_neg h]`. Unfold `coefPos`. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hd' : (0 : ℤ) < d` using `by exact_mod_cast Nat.pos_of_mem_divisors hd`. Establish `s1 : Int.sign (d : ℤ) = 1` using `Int.sign_eq_one_of_pos hd'`. Simplify using `only [w, Int.sign_neg, s1, mul_neg, Int.cast_neg, Int.cast_one, Int.cast_natCast, neg_div]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem hasSum_fibre (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) (τ : ℍ) (m : ℕ) :
    HasSum (Set.indicator ((fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat) ⁻¹' {m})
        (fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ))
      ((if m = 0 then 0 else coefPos j M (ee (1 / (M : ℂ))) a b m) *
        Complex.exp (2 * Real.pi * Complex.I * m * τ / M)) := by
  split_ifs with hm
  · have : Set.indicator ((fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat) ⁻¹' {m})
        (fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ) = fun _ => 0 := by
      funext p
      rw [Set.indicator_apply_eq_zero]
      intro hp
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp
      rw [fTerm_eq j hM, if_neg (by omega)]
    rw [this, zero_mul]
    exact hasSum_zero
  · set E := Complex.exp (2 * Real.pi * Complex.I * m * τ / M) with hE
    let w : ℤ → ℤ → ℂ := fun A e => (Int.sign e : ℂ) * ((A : ℂ) / M) ^ (j - 1) * ee (1 / (M : ℂ)) ^ (b * e) * E
    have h1 := hasSum_sum (s := m.divisors) fun d _ =>
      (hasSum_point hM a ((m / d : ℕ) : ℤ) (d : ℤ) w).add (hasSum_point hM a (-((m / d : ℕ) : ℤ)) (-(d : ℤ)) w)
    convert h1 using 1
    · funext p
      classical
      rw [sum_div_point hm, Set.indicator_apply, fTerm_eq j hM]
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      by_cases h : (a + M * p.1) * p.2 = m
      · rw [if_pos (by omega), if_pos (by omega), if_pos h, h]
        simp only [w, hE, ee]
        congr 2
        push_cast; ring
      · rw [if_neg (by omega), if_neg h]
    · unfold coefPos
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
      have s1 : Int.sign (d : ℤ) = 1 := Int.sign_eq_one_of_pos hd'
      simp only [w, Int.sign_neg, s1, mul_neg, Int.cast_neg, Int.cast_one, Int.cast_natCast, neg_div]
      split_ifs <;> ring

/- English proof (translation)
Unfold `frc`. Conclude with `Int.fract_div_intCast_eq_div_intCast_mod`.
-/
theorem fract_eq {M : ℕ} (a : ℤ) : Int.fract ((a : ℚ) / M) = frc M a := by
  unfold frc
  exact Int.fract_div_intCast_eq_div_intCast_mod

/- English proof (translation)
Establish `hQ : (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `h0 : frc M a = 0 ↔ (M : ℤ) ∣ a`. Unfold `frc`. Rewrite using `[div_eq_zero_iff, or_iff_left hQ, Int.cast_eq_zero, Int.dvd_iff_emod_eq_zero]`. Establish `he : ee ((((b : ℚ) / M : ℚ)) : ℂ) = ee (1 / (M : ℂ)) ^ b`.

Rewrite using `[← ee_int_mul']`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Unfold `f0 const0`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, fract_eq, h0, he]`. Use `split_ifs`. Both sides reduce to the same expression. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eisensteinFxConstantTerm_rationalIndex_eq (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) :
    f0 j ![(a : ℚ) / M, (b : ℚ) / M] = const0 j M (ee (1 / (M : ℂ))) a b := by
  have hQ : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have h0 : frc M a = 0 ↔ (M : ℤ) ∣ a := by
    unfold frc
    rw [div_eq_zero_iff, or_iff_left hQ, Int.cast_eq_zero, Int.dvd_iff_emod_eq_zero]
  have he : ee ((((b : ℚ) / M : ℚ)) : ℂ) = ee (1 / (M : ℂ)) ^ b := by
    rw [← ee_int_mul']; congr 1; push_cast; ring
  unfold f0 const0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fract_eq, h0, he]
  split_ifs
  · rfl
  · push_cast; ring
  · push_cast; ring

/- English proof (translation)
Establish `h1 : HasQ M (fun τ => ∑' p : ℤ × ℤ, fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ p) (fun m => if m = 0 then 0 else coefPos j M (ee (1 / (M : ℂ))) a b m)` using `fun τ => by`. Use `(Model.summable_fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ).hasSum.tsum_fiberwise (fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat)` as an intermediate fact. Establish `e : ∀ m : ℕ, ∑' q : ((fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat) ⁻¹' {m}), fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ q = _` using `fun m => by`. Rewrite using `[tsum_subtype, (hasSum_fibre j hM a b τ m).tsum_eq]`. Simplify `this` using `only [e]`.

Establish `h2` using `(HasQ.const M (f0 j ![(a : ℚ) / M, (b : ℚ) / M])).add h1`. Establish `e : eisF j M (ee (1 / (M : ℂ))) a b = fun n => (if n = 0 then f0 j ![(a : ℚ) / M, (b : ℚ) / M] else 0) + (if n = 0 then 0 else coefPos j M (ee (1 / (M : ℂ))) a b n)`. Use function extensionality and compare the values at `n`. Unfold `eisF`. Use `split_ifs`.

Rewrite using `[eisensteinFxConstantTerm_rationalIndex_eq j hM, add_zero]`. Rewrite using `[zero_add]`. Rewrite using `[e]`. Conclude with `h2`.
-/
theorem hasQ_F (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) :
    HasQ M (F j ![(a : ℚ) / M, (b : ℚ) / M]) (eisF j M (ee (1 / (M : ℂ))) a b) := by
  have h1 : HasQ M (fun τ => ∑' p : ℤ × ℤ, fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ p)
      (fun m => if m = 0 then 0 else coefPos j M (ee (1 / (M : ℂ))) a b m) := fun τ => by
    have := (Model.summable_fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ).hasSum.tsum_fiberwise
      (fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat)
    have e : ∀ m : ℕ, ∑' q : ((fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat) ⁻¹' {m}),
        fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ q = _ := fun m => by
      rw [tsum_subtype, (hasSum_fibre j hM a b τ m).tsum_eq]
    simpa only [e] using this
  have h2 := (HasQ.const M (f0 j ![(a : ℚ) / M, (b : ℚ) / M])).add h1
  have e : eisF j M (ee (1 / (M : ℂ))) a b = fun n => (if n = 0 then f0 j ![(a : ℚ) / M, (b : ℚ) / M] else 0) +
      (if n = 0 then 0 else coefPos j M (ee (1 / (M : ℂ))) a b n) := by
    funext n
    unfold eisF
    split_ifs
    · rw [eisensteinFxConstantTerm_rationalIndex_eq j hM, add_zero]
    · rw [zero_add]
  rw [e]
  exact h2

/- English proof (translation)
Establish `hx : c • ![(a : ℚ) / M, (b : ℚ) / M] = ![(((c : ℤ) * a : ℤ) : ℚ) / M, (((c : ℤ) * b : ℤ) : ℚ) / M]`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [mul_div_assoc]`. Use `((hasQ_F j hM a b).const_mul ((c : ℂ) ^ 2)).sub ((hasQ_F j hM (c * a) (c * b)).const_mul ((c : ℂ) ^ (2 - (j : ℤ))))` as an intermediate fact. Rewrite `this` using `[← hx]`.

Unfold `smF`. Simplify using `only [Int.cast_natCast]`. Conclude with `this`.
-/
theorem hasQ_cF_weight (c j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) :
    HasQ M (cF c j ![(a : ℚ) / M, (b : ℚ) / M]) (smF (c : ℤ) j M (ee (1 / (M : ℂ))) a b) := by
  have hx : c • ![(a : ℚ) / M, (b : ℚ) / M] = ![(((c : ℤ) * a : ℤ) : ℚ) / M, (((c : ℤ) * b : ℤ) : ℚ) / M] := by
    funext i
    fin_cases i <;> simp [mul_div_assoc]
  have := ((hasQ_F j hM a b).const_mul ((c : ℂ) ^ 2)).sub
    ((hasQ_F j hM (c * a) (c * b)).const_mul ((c : ℂ) ^ (2 - (j : ℤ))))
  rw [← hx] at this
  unfold smF
  simp only [Int.cast_natCast]
  exact this

/- English proof (translation)
Introduce `c _ a b hM` and use `hasQ_cF_weight c 1 hM a b`.
-/
theorem hasQ_cF_one : ∀ (c M : ℕ) (a b : ℤ), 0 < M → GlobalTheory.QFam.HasQ M (GlobalTheory.Sieg.cF c 1 ![(a : ℚ) / M, (b : ℚ) / M])
    (GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M (GlobalTheory.Sieg.ee (1 / (M : ℂ))) a b) :=
  fun c _ a b hM => hasQ_cF_weight c 1 hM a b

end GlobalTheory.Sieg.EisQ
