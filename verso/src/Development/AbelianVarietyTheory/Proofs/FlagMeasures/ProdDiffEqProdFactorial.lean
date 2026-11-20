import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FormalDegreeDatum

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => simp`. Consider the case `succ m`. Establish `h` using `Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) m`. Rewrite `h` using `[Matrix.det_vandermonde, ← Nat.prod_range_succ_factorial]`.

Move the coercions through the operations in `at h`. Rewrite using `[← h]`. Use `Finset.prod_congr rfl fun a _ => Finset.prod_congr ?_ fun b _ => rfl` and prove the remaining obligations. Use extensionality with `b`. Simplify using the standard rewrite rules.
-/
theorem prod_diff_eq_prod_factorial (n : ℕ) :
    (∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) =
      ∏ i ∈ Finset.range n, (i.factorial : ℝ) := by
  cases n with
  | zero => simp
  | succ m =>
    have h := Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) m
    rw [Matrix.det_vandermonde, ← Nat.prod_range_succ_factorial] at h
    push_cast at h
    rw [← h]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr ?_ fun b _ => rfl
    ext b; simp

/- English proof (translation)
Establish `hd : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).1 hP`. Establish `hPP : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hd`. Unfold `Formalism.REAL.inUJ`. Establish `: (Q * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (Q * P⁻¹) = (P⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * P⁻¹`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Rewrite using `[this, h2, ← h1]`. Establish `: (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹)`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[this, hPP]`. Simplify using the standard rewrite rules.
-/
theorem inUJ_of_cayley {n : ℕ} (ε : Fin n → Bool) (P Q G : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (h1 : Pᴴ * Formalism.REAL.Jm ε * P = G) (h2 : Qᴴ * Formalism.REAL.Jm ε * Q = G) :
    Formalism.REAL.inUJ ε (Q * P⁻¹) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  unfold Formalism.REAL.inUJ
  have : (Q * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (Q * P⁻¹) = (P⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * P⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [this, h2, ← h1]
  have : (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [this, hPP]; simp

/- English proof (translation)
Establish `hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε` using `fun g => g.2`. Establish `hmul : ∀ g h : Formalism.REAL.UJ ε, σ₁ (umat (g * h)) w = σ₁ (umat g) (σ₁ (umat h) w)`. Introduce `g h`. Use `hu.1.2 _ (hmem g) _ (hmem h)` as an intermediate fact. Establish `e : umat (g * h) = umat g * umat h` using `rfl`.

Rewrite using `[e, this]`. Both sides reduce to the same expression. Establish `hv : ‖σ₁ (umat a) w‖ = ‖w‖` using `hu.2.1 _ (hmem a) w`. Use `set v := σ₁ (umat a) w with hvdef`. Establish `h1 : ∫ g, ‖inner ℂ w (σ₁ (umat g) w)‖ ^ 2 ∂μ = ∫ g, ‖coefOn σ₀ v w g‖ ^ 2 ∂μ`.

Rewrite using `[← integral_mul_left_eq_self (fun g : Formalism.REAL.UJ ε => ‖inner ℂ w (σ₁ (umat g) w)‖ ^ 2) a]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only [coefOn, hc, hvdef, ← hmul]`. Rewrite using `[inv_mul_cancel_right]`. Establish `h2` using `(hd.2 v w v w).2`.

Establish `h3 : ∀ g : Formalism.REAL.UJ ε, coefOn σ₀ v w g * star (coefOn σ₀ v w g) = ((‖coefOn σ₀ v w g‖ ^ 2 : ℝ) : ℂ)`. Introduce `g`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Simplify using `only [h3] at h2`. Rewrite `h2` using `[integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hv]`.

Establish `h4 : ∫ g, ‖coefOn σ₀ v w g‖ ^ 2 ∂μ = ‖w‖ ^ 2 * ‖w‖ ^ 2 / d`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[h2]`. Simplify using the standard rewrite rules. Establish `hn : ‖w‖ ≠ 0` using `norm_ne_zero_iff.2 hw`.

Establish `hd0 : d ≠ 0` using `hd.1.ne'`. Rewrite using `[h1, h4]`. Clear the denominators using the available nonvanishing facts.
-/
theorem fdeg_of_conj {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsMulLeftInvariant]
    (σ₀ σ₁ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (a : Formalism.REAL.UJ ε)
    (hc : ∀ g : Formalism.REAL.UJ ε, σ₀ (umat g) = σ₁ (umat (a * g * a⁻¹)))
    (hu : IsURepOn (UJset ε) σ₁) (d : ℝ) (hd : IsFdeg μ σ₀ d) (w : H) (hw : w ≠ 0) :
    ‖w‖ ^ 4 / ∫ g, ‖inner ℂ w (σ₁ (umat g) w)‖ ^ 2 ∂μ = d := by
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hmul : ∀ g h : Formalism.REAL.UJ ε, σ₁ (umat (g * h)) w = σ₁ (umat g) (σ₁ (umat h) w) := by
    intro g h
    have := hu.1.2 _ (hmem g) _ (hmem h)
    have e : umat (g * h) = umat g * umat h := rfl
    rw [e, this]; rfl
  have hv : ‖σ₁ (umat a) w‖ = ‖w‖ := hu.2.1 _ (hmem a) w
  set v := σ₁ (umat a) w with hvdef
  have h1 : ∫ g, ‖inner ℂ w (σ₁ (umat g) w)‖ ^ 2 ∂μ = ∫ g, ‖coefOn σ₀ v w g‖ ^ 2 ∂μ := by
    rw [← integral_mul_left_eq_self (fun g : Formalism.REAL.UJ ε => ‖inner ℂ w (σ₁ (umat g) w)‖ ^ 2) a]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [coefOn, hc, hvdef, ← hmul]
    rw [inv_mul_cancel_right]
  have h2 := (hd.2 v w v w).2
  have h3 : ∀ g : Formalism.REAL.UJ ε, coefOn σ₀ v w g * star (coefOn σ₀ v w g) =
      ((‖coefOn σ₀ v w g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h3] at h2
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hv] at h2
  have h4 : ∫ g, ‖coefOn σ₀ v w g‖ ^ 2 ∂μ = ‖w‖ ^ 2 * ‖w‖ ^ 2 / d := by
    apply Complex.ofReal_injective
    rw [h2]
    simp
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have hd0 : d ≠ 0 := hd.1.ne'
  rw [h1, h4]
  field_simp

/- English proof (translation)
Introduce `hF k r H _ _ _ σ ε lam cd sc P d hsc hlam hDS hP hd`. Take `⟨Q, ⟨hQ, -⟩, hDS⟩` from `hDS`. Establish `hPd : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).1 hP.1`. Establish `hQd : IsUnit Q.det` using `(Matrix.isUnit_iff_isUnit_det Q).1 hQ.1`. Establish `hPP : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hPd`.

Establish `hPP' : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hPd`. Establish `hQQ : Q * Q⁻¹ = 1` using `Matrix.mul_nonsing_inv Q hQd`. Establish `hQQ' : Q⁻¹ * Q = 1` using `Matrix.nonsing_inv_mul Q hQd`. Set `u : (Mat k r)ˣ` to `⟨Q * P⁻¹, P * Q⁻¹, by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, hPP', Matrix.one_mul, hQQ], by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q⁻¹, hQQ', Matrix.one_mul, hPP]⟩`. Set `a : Formalism.REAL.UJ ε` to `⟨u, inUJ_of_cayley ε P Q _ hP.1 hP.2 hQ.2⟩`.

Use `haveI := hDS.2.1`. Take `⟨w, hw⟩` from `exists_ne (0 : H)`. Establish `h1` using `hF cd sc hsc _ ε lam hlam H _ w hDS hw`. Establish `h2` using `fdeg_of_conj ((sc _ ε : ℝ≥0∞) • Formalism.REAL.muG ε) (fun g => σ (P⁻¹ * g * P)) (fun g => σ (Q⁻¹ * g * Q)) a (fun g => by`. Establish `e : umat (a * g * a⁻¹) = Q * P⁻¹ * umat g * (P * Q⁻¹)` using `rfl`.

Establish `e2 : Q⁻¹ * (Q * P⁻¹ * umat g * (P * Q⁻¹)) * Q = (Q⁻¹ * Q) * (P⁻¹ * umat g * P) * (Q⁻¹ * Q)`. Simplify using `only [Matrix.mul_assoc]`. Simplify using `only [e, e2, hQQ', Matrix.one_mul, Matrix.mul_one]) hDS.2.2.1 d hd w hw`. Rewrite `h1` using `[h2, prod_diff_eq_prod_factorial]`. Establish `hne : (∏ i ∈ Finset.range (2 * r + k + 1), (i.factorial : ℝ)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast i.factorial_ne_zero`.

Rewrite using `[h1, div_mul_cancel₀ _ hne]`. Unfold `vand`. Use `Finset.prod_congr rfl fun x _ => Finset.prod_congr rfl fun y hy => ?_` and prove the remaining obligations. Establish `: x < y` using `(Finset.mem_filter.1 hy).2`. Conclude with `abs_of_pos (sub_pos.2 (hlam.1 this))`.
-/
theorem fdeg_mul_prod_factorial : GlobalTheory.Published.FormalDegreeCompactDual → ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (cd : Formalism.BasicNotions.CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal) (P : Mat k r) (d : ℝ), GlobalTheory.Mem.Vol.CdScaleIs cd sc → IsHCParam lam → IsDSHpk k r ε lam σ → IsCayley k r ε P → IsFdeg ((sc _ ε : ℝ≥0∞) • Formalism.REAL.muG ε) (fun g => σ (P⁻¹ * g * P)) d → d * (∏ i ∈ Finset.range (2 * r + k + 1), (i.factorial : ℝ)) = vand lam := by
  intro hF k r H _ _ _ σ ε lam cd sc P d hsc hlam hDS hP hd
  obtain ⟨Q, ⟨hQ, -⟩, hDS⟩ := hDS
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQd
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQd
  let u : (Mat k r)ˣ := ⟨Q * P⁻¹, P * Q⁻¹,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, hPP', Matrix.one_mul, hQQ],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q⁻¹, hQQ', Matrix.one_mul, hPP]⟩
  let a : Formalism.REAL.UJ ε := ⟨u, inUJ_of_cayley ε P Q _ hP.1 hP.2 hQ.2⟩
  haveI := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have h1 := hF cd sc hsc _ ε lam hlam H _ w hDS hw
  have h2 := fdeg_of_conj ((sc _ ε : ℝ≥0∞) • Formalism.REAL.muG ε) (fun g => σ (P⁻¹ * g * P))
    (fun g => σ (Q⁻¹ * g * Q)) a (fun g => by
      have e : umat (a * g * a⁻¹) = Q * P⁻¹ * umat g * (P * Q⁻¹) := rfl
      have e2 : Q⁻¹ * (Q * P⁻¹ * umat g * (P * Q⁻¹)) * Q = (Q⁻¹ * Q) * (P⁻¹ * umat g * P) * (Q⁻¹ * Q) := by
        simp only [Matrix.mul_assoc]
      simp only [e, e2, hQQ', Matrix.one_mul, Matrix.mul_one]) hDS.2.2.1 d hd w hw
  rw [h2, prod_diff_eq_prod_factorial] at h1
  have hne : (∏ i ∈ Finset.range (2 * r + k + 1), (i.factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast i.factorial_ne_zero
  rw [h1, div_mul_cancel₀ _ hne]
  unfold vand
  refine Finset.prod_congr rfl fun x _ => Finset.prod_congr rfl fun y hy => ?_
  have : x < y := (Finset.mem_filter.1 hy).2
  exact abs_of_pos (sub_pos.2 (hlam.1 this))

end GlobalTheory.FormalDegreeDatum
