import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.Development

noncomputable section

namespace PI.DefPosDefWork

open Matrix ComplexOrder

/- English proof (translation)
Establish `hQc : Continuous fun w : Fin k → ℂ => (star w ⬝ᵥ (M *ᵥ w)).re` using `by show Continuous fun w : Fin k → ℂ => (∑ i, star (w i) * ∑ j, M i j * w j).re`. Conclude with `Complex.continuous_re.comp (continuous_finset_sum _ fun i _ => (continuous_star.comp (continuous_apply i)).mul (continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_apply j)))`. Set `ψ : (Fin k → ℝ) × (Fin k → ℝ) → (Fin k → ℂ)` to `fun p i => (p.1 i : ℂ) + (p.2 i : ℂ) * z`. Establish `hψ : Continuous ψ` using `by fun_prop`. Set `d : (Fin k → ℚ) × (Fin k → ℚ) → (Fin k → ℝ) × (Fin k → ℝ)` to `Prod.map (fun α i => (α i : ℝ)) (fun β i => (β i : ℝ))`.

Establish `hd : DenseRange d` using `(DenseRange.piMap fun _ => Rat.denseRange_cast).prodMap (DenseRange.piMap fun _ => Rat.denseRange_cast)`. Establish `key : ∀ p : (Fin k → ℝ) × (Fin k → ℝ), 0 ≤ (star (ψ p) ⬝ᵥ (M *ᵥ ψ p)).re` using `fun p => hd.induction_on p (isClosed_le continuous_const (hQc.comp hψ)) (fun q => by simpa [ψ, d] using h q.1 q.2)`. Set `p : (Fin k → ℝ) × (Fin k → ℝ)` to `(fun i => (v i).re - (v i).im / z.im * z.re, fun i => (v i).im / z.im)`. Establish `hp : ψ p = v`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `apply Complex.ext <;> simp [ψ, p] <;> (try field_simp) <;> (try ring)`. Establish `h1` using `key p`. Rewrite `h1` using `[hp]`. Then use the resulting hypothesis.
-/
theorem re_nonneg_of_rat {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (z : ℂ) (hz : z.im ≠ 0)
    (h : ∀ α β : Fin k → ℚ, 0 ≤ (star (fun i => (α i : ℂ) + (β i : ℂ) * z) ⬝ᵥ
      (M *ᵥ (fun i => (α i : ℂ) + (β i : ℂ) * z))).re)
    (v : Fin k → ℂ) : 0 ≤ (star v ⬝ᵥ (M *ᵥ v)).re := by
  have hQc : Continuous fun w : Fin k → ℂ => (star w ⬝ᵥ (M *ᵥ w)).re := by
    show Continuous fun w : Fin k → ℂ => (∑ i, star (w i) * ∑ j, M i j * w j).re
    exact Complex.continuous_re.comp (continuous_finset_sum _ fun i _ =>
      (continuous_star.comp (continuous_apply i)).mul
        (continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_apply j)))
  let ψ : (Fin k → ℝ) × (Fin k → ℝ) → (Fin k → ℂ) := fun p i => (p.1 i : ℂ) + (p.2 i : ℂ) * z
  have hψ : Continuous ψ := by fun_prop
  let d : (Fin k → ℚ) × (Fin k → ℚ) → (Fin k → ℝ) × (Fin k → ℝ) :=
    Prod.map (fun α i => (α i : ℝ)) (fun β i => (β i : ℝ))
  have hd : DenseRange d :=
    (DenseRange.piMap fun _ => Rat.denseRange_cast).prodMap (DenseRange.piMap fun _ => Rat.denseRange_cast)
  have key : ∀ p : (Fin k → ℝ) × (Fin k → ℝ), 0 ≤ (star (ψ p) ⬝ᵥ (M *ᵥ ψ p)).re := fun p =>
    hd.induction_on p (isClosed_le continuous_const (hQc.comp hψ)) (fun q => by simpa [ψ, d] using h q.1 q.2)
  let p : (Fin k → ℝ) × (Fin k → ℝ) := (fun i => (v i).re - (v i).im / z.im * z.re, fun i => (v i).im / z.im)
  have hp : ψ p = v := by
    funext i
    apply Complex.ext <;> simp [ψ, p] <;> (try field_simp) <;> (try ring)
  have h1 := key p
  rwa [hp] at h1

/- English proof (translation)
Simplify using `only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im, hN]`. Rewrite using `[← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[← Finset.sum_add_distrib]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem re_quad {k : ℕ} (N : Matrix (Fin k) (Fin k) ℂ) (hN : ∀ i j, (N i j).im = 0) (a b : Fin k → ℝ) :
    (star (fun i => (a i : ℂ) + (b i : ℂ) * Complex.I) ⬝ᵥ (N *ᵥ (fun i => (a i : ℂ) + (b i : ℂ) * Complex.I))).re
      = (star (fun i => (a i : ℂ)) ⬝ᵥ (N *ᵥ (fun i => (a i : ℂ)))).re
        + (star (fun i => (b i : ℂ)) ⬝ᵥ (N *ᵥ (fun i => (b i : ℂ)))).re := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im, hN]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/- English proof (translation)
Use `haveI : CharZero E := RingHom.charZero φ`. Establish `hPSD : ∀ v : Fin k → ℂ, 0 ≤ (star v ⬝ᵥ (N *ᵥ v)).re`. Distinguish the cases in `hreal : ∀ t : E, (φ t).im = 0`. Establish `hNr'` using `hNr hreal`. Establish `hQc : Continuous fun a : Fin k → ℝ => (star (fun i => (a i : ℂ)) ⬝ᵥ (N *ᵥ fun i => (a i : ℂ))).re` using `by show Continuous fun a : Fin k → ℝ => (∑ i, star ((a i : ℂ)) * ∑ j, N i j * (a j : ℂ)).re`.

Conclude with `Complex.continuous_re.comp (continuous_finset_sum _ fun i _ => (continuous_star.comp (Complex.continuous_ofReal.comp (continuous_apply i))).mul (continuous_finset_sum _ fun j _ => continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j))))`. Establish `hd : DenseRange (fun α : Fin k → ℚ => fun i => (α i : ℝ))` using `DenseRange.piMap fun _ => Rat.denseRange_cast`. Establish `hreal' : ∀ a : Fin k → ℝ, 0 ≤ (star (fun i => (a i : ℂ)) ⬝ᵥ (N *ᵥ fun i => (a i : ℂ))).re` using `fun a => hd.induction_on a (isClosed_le continuous_const hQc) (fun α => by`. Establish `h1` using `hpt (fun i => (α i : E))`. Simplify `h1)` using `[map_ratCast]`.

Introduce `v`. Establish `e` using `re_quad N hNr' (fun i => (v i).re) (fun i => (v i).im)`. Establish `hv : (fun i => ((v i).re : ℂ) + ((v i).im : ℂ) * Complex.I) = v`. Use function extensionality and compare the values at `fun i => Complex.re_add_im (v i)`. Rewrite `e` using `[hv]`.

Rewrite using `[e]`. Conclude with `add_nonneg (hreal' _) (hreal' _)`. Use `push_neg at hreal`. Take `⟨t, ht⟩` from `hreal`. Use `re_nonneg_of_rat N (φ t) ht (fun α β => ?_)` and prove the remaining obligations.

Establish `h1` using `hpt (fun i => (α i : E) + (β i : E) * t)`. Simplify `h1` using `[map_add, map_mul, map_ratCast]`. Establish `hpsd : N.PosSemidef`. Rewrite using `[Matrix.posSemidef_iff_dotProduct_mulVec]`. Use `⟨hN, fun v => ?_⟩` and prove the remaining obligations.

Rewrite using `[Complex.nonneg_iff]`. Conclude with `⟨hPSD v, (hN.im_star_dotProduct_mulVec_self v).symm⟩`. Conclude with `hpsd.posDef_iff_isUnit.2 hu`.
-/
theorem posDef_of_points {E : Type} [Field E] (φ : E →+* ℂ) {k : ℕ} (N : Matrix (Fin k) (Fin k) ℂ)
    (hN : N.IsHermitian) (hu : IsUnit N) (hNr : (∀ t : E, (φ t).im = 0) → ∀ i j, (N i j).im = 0)
    (hpt : ∀ x : Fin k → E, 0 ≤ (star (fun i => φ (x i)) ⬝ᵥ (N *ᵥ (fun i => φ (x i)))).re) : N.PosDef := by
  haveI : CharZero E := RingHom.charZero φ
  have hPSD : ∀ v : Fin k → ℂ, 0 ≤ (star v ⬝ᵥ (N *ᵥ v)).re := by
    by_cases hreal : ∀ t : E, (φ t).im = 0
    · have hNr' := hNr hreal
      have hQc : Continuous fun a : Fin k → ℝ =>
          (star (fun i => (a i : ℂ)) ⬝ᵥ (N *ᵥ fun i => (a i : ℂ))).re := by
        show Continuous fun a : Fin k → ℝ => (∑ i, star ((a i : ℂ)) * ∑ j, N i j * (a j : ℂ)).re
        exact Complex.continuous_re.comp (continuous_finset_sum _ fun i _ =>
          (continuous_star.comp (Complex.continuous_ofReal.comp (continuous_apply i))).mul
            (continuous_finset_sum _ fun j _ =>
              continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j))))
      have hd : DenseRange (fun α : Fin k → ℚ => fun i => (α i : ℝ)) :=
        DenseRange.piMap fun _ => Rat.denseRange_cast
      have hreal' : ∀ a : Fin k → ℝ, 0 ≤ (star (fun i => (a i : ℂ)) ⬝ᵥ (N *ᵥ fun i => (a i : ℂ))).re :=
        fun a => hd.induction_on a (isClosed_le continuous_const hQc) (fun α => by
          have h1 := hpt (fun i => (α i : E))
          simpa [map_ratCast] using h1)
      intro v
      have e := re_quad N hNr' (fun i => (v i).re) (fun i => (v i).im)
      have hv : (fun i => ((v i).re : ℂ) + ((v i).im : ℂ) * Complex.I) = v :=
        funext fun i => Complex.re_add_im (v i)
      rw [hv] at e
      rw [e]
      exact add_nonneg (hreal' _) (hreal' _)
    · push_neg at hreal
      obtain ⟨t, ht⟩ := hreal
      refine re_nonneg_of_rat N (φ t) ht (fun α β => ?_)
      have h1 := hpt (fun i => (α i : E) + (β i : E) * t)
      simpa [map_add, map_mul, map_ratCast] using h1
  have hpsd : N.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hN, fun v => ?_⟩
    rw [Complex.nonneg_iff]
    exact ⟨hPSD v, (hN.im_star_dotProduct_mulVec_self v).symm⟩
  exact hpsd.posDef_iff_isUnit.2 hu

/- English proof (translation)
Introduce `F E _ _ _ _ _ hF σ k J _ hH hD h1 φ`. Take `⟨r, hr⟩` from `hF (φ.comp (algebraMap F E))`. Establish `hr' : ∀ a, φ (algebraMap F E a) = (r a : ℂ)` using `fun a => hr a`. Establish `hJ : ∀ i j, σ (J j i) = J i j` using `fun i j => congrFun (congrFun hH i) j`. Establish `hst : ∀ y, star (φ y) = φ (σ y)` using `fun y => (h1 φ y).symm`.

Establish `hMh : (J.map φ).IsHermitian`. Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply, hst, hJ]`. Establish `hQ : ∀ x : Fin k → E, star (fun i => φ (x i)) ⬝ᵥ (J.map φ *ᵥ (fun i => φ (x i))) = φ (hform (σ : E →+* E) J x x)`. Introduce `x`.

Simplify using `only [dotProduct, mulVec, hform, Pi.star_apply, hst, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, mul_assoc]`. Both sides reduce to the same expression. Establish `hdet : J.det ≠ 0`. Introduce `h0`. Take `⟨v, hv, hJv⟩` from `(Matrix.exists_mulVec_eq_zero_iff).mpr h0`.

Establish `h0' : hform (σ : E →+* E) J v v = 0`. Establish `e : hform (σ : E →+* E) J v v = ∑ i, (σ : E →+* E) (v i) * (J *ᵥ v) i`. Simplify using `only [hform, mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Rewrite using `[e, hJv]`. Simplify using the standard rewrite rules.

Break down `hD r with h | h` into its components or cases. Take `⟨a, ha, ha'⟩` from `h v hv`. Rewrite `ha` using `[h0']`. Establish `ha0 : a = 0` using `(map_eq_zero_iff _ (algebraMap F E).injective).mp ha`. Rewrite `ha'` using `[ha0, map_zero]`.

Conclude with `lt_irrefl _ ha'`. Take `⟨a, ha, ha'⟩` from `h v hv`. Rewrite `ha` using `[h0']`. Establish `ha0 : a = 0` using `(map_eq_zero_iff _ (algebraMap F E).injective).mp ha`. Rewrite `ha'` using `[ha0, map_zero]`.

Conclude with `lt_irrefl _ ha'`. Establish `hMu : IsUnit (J.map φ)`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(map_ne_zero φ).mpr hdet`. Establish `hMr : (∀ t : E, (φ t).im = 0) → ∀ i j, ((J.map φ) i j).im = 0` using `fun ht i j => ht (J i j)`.

Establish `hQ0 : ∀ x : Fin k → E, x = 0 → hform (σ : E →+* E) J x x = 0`. Introduce `x hx`. Substitute `hx` using the available equality. Simplify using `[hform]`. Break down `hD r with h | h` into its components or cases.

Use `left`. Use `posDef_of_points φ _ hMh hMu hMr fun x => ?_` and prove the remaining obligations. Rewrite using `[hQ]`. Distinguish the cases in `hx : x = 0`. Rewrite using `[hQ0 x hx]`.

Simplify using the standard rewrite rules. Take `⟨a, ha, ha'⟩` from `h x hx`. Rewrite using `[← ha, hr']`. Simplify using `using ha'.le`. Use `right`.

Use `posDef_of_points φ _ hMh.neg hMu.neg (fun ht i j => by simpa using hMr ht i j) fun x => ?_` and prove the remaining obligations. Rewrite using `[Matrix.neg_mulVec, dotProduct_neg, hQ]`. Distinguish the cases in `hx : x = 0`. Rewrite using `[hQ0 x hx]`. Simplify using the standard rewrite rules.

Take `⟨a, ha, ha'⟩` from `h x hx`. Rewrite using `[← ha, hr']`. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem positive_definite_second : Step2 := by
  intro F E _ _ _ _ _ hF σ k J _ hH hD h1 φ
  obtain ⟨r, hr⟩ := hF (φ.comp (algebraMap F E))
  have hr' : ∀ a, φ (algebraMap F E a) = (r a : ℂ) := fun a => hr a
  have hJ : ∀ i j, σ (J j i) = J i j := fun i j => congrFun (congrFun hH i) j
  have hst : ∀ y, star (φ y) = φ (σ y) := fun y => (h1 φ y).symm
  have hMh : (J.map φ).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, hst, hJ]
  have hQ : ∀ x : Fin k → E, star (fun i => φ (x i)) ⬝ᵥ (J.map φ *ᵥ (fun i => φ (x i)))
      = φ (hform (σ : E →+* E) J x x) := by
    intro x
    simp only [dotProduct, mulVec, hform, Pi.star_apply, hst, Matrix.map_apply, map_sum, map_mul,
      Finset.mul_sum, mul_assoc]
    rfl
  have hdet : J.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hJv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr h0
    have h0' : hform (σ : E →+* E) J v v = 0 := by
      have e : hform (σ : E →+* E) J v v = ∑ i, (σ : E →+* E) (v i) * (J *ᵥ v) i := by
        simp only [hform, mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      rw [e, hJv]
      simp
    rcases hD r with h | h
    · obtain ⟨a, ha, ha'⟩ := h v hv
      rw [h0'] at ha
      have ha0 : a = 0 := (map_eq_zero_iff _ (algebraMap F E).injective).mp ha
      rw [ha0, map_zero] at ha'
      exact lt_irrefl _ ha'
    · obtain ⟨a, ha, ha'⟩ := h v hv
      rw [h0'] at ha
      have ha0 : a = 0 := (map_eq_zero_iff _ (algebraMap F E).injective).mp ha
      rw [ha0, map_zero] at ha'
      exact lt_irrefl _ ha'
  have hMu : IsUnit (J.map φ) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).mpr hdet
  have hMr : (∀ t : E, (φ t).im = 0) → ∀ i j, ((J.map φ) i j).im = 0 := fun ht i j => ht (J i j)
  have hQ0 : ∀ x : Fin k → E, x = 0 → hform (σ : E →+* E) J x x = 0 := by
    intro x hx
    subst hx
    simp [hform]
  rcases hD r with h | h
  · left
    refine posDef_of_points φ _ hMh hMu hMr fun x => ?_
    rw [hQ]
    by_cases hx : x = 0
    · rw [hQ0 x hx]
      simp
    · obtain ⟨a, ha, ha'⟩ := h x hx
      rw [← ha, hr']
      simpa using ha'.le
  · right
    refine posDef_of_points φ _ hMh.neg hMu.neg (fun ht i j => by simpa using hMr ht i j) fun x => ?_
    rw [Matrix.neg_mulVec, dotProduct_neg, hQ]
    by_cases hx : x = 0
    · rw [hQ0 x hx]
      simp
    · obtain ⟨a, ha, ha'⟩ := h x hx
      rw [← ha, hr']
      simp
      linarith

end PI.DefPosDefWork
