import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

namespace GlobalTheory

open Complex ReciprocityTheory.ChartRestriction.G.I2

namespace FockTranslation

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Simplify using `[Hf, add_mul, Finset.sum_add_distrib]`.
-/
theorem herm_add_left (u v w : EuclideanSpace ℂ ι) : Hf (u + v) w = Hf u w + Hf v w := by
  simp [Hf, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[Hf, mul_add, Finset.sum_add_distrib]`.
-/
theorem herm_add_right (u v w : EuclideanSpace ℂ ι) : Hf u (v + w) = Hf u v + Hf u w := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[Hf, sub_mul, Finset.sum_sub_distrib]`.
-/
theorem herm_sub_left (u v w : EuclideanSpace ℂ ι) : Hf (u - v) w = Hf u w - Hf v w := by
  simp [Hf, sub_mul, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `[Hf, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem herm_sub_right (u v w : EuclideanSpace ℂ ι) : Hf u (v - w) = Hf u v - Hf u w := by
  simp [Hf, mul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `[Hf]`.
-/
theorem herm_neg_left (u w : EuclideanSpace ℂ ι) : Hf (-u) w = -Hf u w := by
  simp [Hf]

/- English proof (translation)
Simplify using `[Hf]`.
-/
theorem herm_neg_right (u w : EuclideanSpace ℂ ι) : Hf u (-w) = -Hf u w := by
  simp [Hf]

/- English proof (translation)
Simplify using `[Hf]`.
-/
theorem herm_zero_right (u : EuclideanSpace ℂ ι) : Hf u 0 = 0 := by
  simp [Hf]

/- English proof (translation)
Simplify using `only [Hf, PiLp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem herm_smul_right (c : ℂ) (u w : EuclideanSpace ℂ ι) :
    Hf u (c • w) = (starRingEnd ℂ) c * Hf u w := by
  simp only [Hf, PiLp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Simplify using `only [Hf, map_sum, map_mul, Complex.conj_conj]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem herm_conj (u w : EuclideanSpace ℂ ι) : (starRingEnd ℂ) (Hf u w) = Hf w u := by
  simp only [Hf, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Establish `h` using `Complex.sub_conj (Hf u w)`. Rewrite `h` using `[herm_conj]`. Move the coercions through the operations in `at h`. Take the linear combination `-h`.
-/
theorem herm_sub_swap (u w : EuclideanSpace ℂ ι) :
    Hf w u = Hf u w - 2 * I * ((Hf u w).im : ℂ) := by
  have h := Complex.sub_conj (Hf u w)
  rw [herm_conj] at h
  push_cast at h
  linear_combination -h

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq]`. Simplify using `only [Hf, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem herm_self (x : EuclideanSpace ℂ ι) : Hf x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Hf, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/- English proof (translation)
Rewrite using `[herm_self, Complex.ofReal_re]`.
-/
theorem herm_self_re (x : EuclideanSpace ℂ ι) : (Hf x x).re = ‖x‖ ^ 2 := by
  rw [herm_self, Complex.ofReal_re]

/- English proof (translation)
Rewrite using `[herm_self, Complex.ofReal_im]`.
-/
theorem herm_self_im (x : EuclideanSpace ℂ ι) : (Hf x x).im = 0 := by
  rw [herm_self, Complex.ofReal_im]

/- English proof (translation)
Rewrite using `[← herm_conj u w, Complex.conj_re]`.
-/
theorem herm_re_swap (u w : EuclideanSpace ℂ ι) : (Hf w u).re = (Hf u w).re := by
  rw [← herm_conj u w, Complex.conj_re]

/- English proof (translation)
Rewrite using `[← herm_conj u w, Complex.conj_im]`.
-/
theorem herm_im_swap (u w : EuclideanSpace ℂ ι) : (Hf w u).im = -(Hf u w).im := by
  rw [← herm_conj u w, Complex.conj_im]

/- English proof (translation)
Unfold `Hf`. Use `fun_prop`.
-/
theorem herm_differentiable (a : EuclideanSpace ℂ ι) :
    Differentiable ℂ fun v : EuclideanSpace ℂ ι => Hf v a := by
  unfold Hf
  fun_prop

end FockTranslation

open FockTranslation in

/- English proof (translation)
Establish `h1 : ∀ a b F, U q a (U q b F) = cexp (-(q * Real.pi * I * (Hf a b).im)) • U q (a + b) F`. Introduce `a b F`. Use function extensionality and compare the values at `v`. Simplify using `only [hU, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add, sub_sub]`.

Use `congr 2`. Simplify using `only [herm_add_left, herm_add_right, herm_sub_left]`. Rewrite using `[herm_sub_swap a b]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∀ F, U q 0 F = F`.

Introduce `F`. Use function extensionality and compare the values at `v`. Simplify using `[hU, herm_zero_right]`. Establish `h6 : ∀ (Y : GT ι) F, F ∈ Y.Sec q ↔ Differentiable ℂ F ∧ ∀ γ ∈ lat Y.b, Y.ka γ • U q γ F = F`. Introduce `Y F`.

Establish `key : ∀ γ v, (Y.ka γ • U q γ F) (v + γ) = Y.ka γ * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * F v`. Introduce `γ v`. Simplify using `only [hU, Pi.smul_apply, smul_eq_mul, add_sub_cancel_right, herm_add_left]`. Rewrite using `[← mul_assoc]`. Use `congr 3`.

Expand and normalize the polynomial expressions, which then agree. Use `and_congr_right fun _ => forall₂_congr fun γ _ => ⟨fun h => ?_, fun h v => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Use `key γ (w - γ)` as an intermediate fact. Rewrite `this` using `[← h, sub_add_cancel]`.

Conclude with `this`. Rewrite using `[← key, h]`. Use `⟨h1, h2, ?_, ?_, ?_, h6, ?_, ?_⟩` and prove the remaining obligations. Introduce `a F`. Use function extensionality and compare the values at `v`.

Simplify using `only [hU, herm_neg_left, herm_neg_right, neg_neg]`. Use `congr 2`. Normalize the expressions using the abelian group laws. Introduce `a F M`. Proceed by induction on `M with`.

Consider the case `zero => simp [h2]`. Consider the case `succ M ih`. Rewrite using `[Function.iterate_succ_apply', ih, h1]`. Establish `: (Hf a ((M : ℂ) • a)).im = 0`. Rewrite using `[herm_smul_right]`.

Simplify using `[herm_self_im]`. Rewrite using `[this]`. Establish `e : a + (M : ℂ) • a = ((M + 1 : ℕ) : ℂ) • a`. Use `push_cast`. Rewrite using `[add_smul, one_smul, add_comm]`.

Simplify using `[e]`. Introduce `a F v`. Rewrite using `[hU, norm_mul, mul_pow, Complex.norm_exp, mul_comm (_ ^ 2) (‖F (v - a)‖ ^ 2), mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]`. Use `congr 2`. Rewrite using `[← herm_self_re v, ← herm_self_re (v - a)]`.

Establish `e : (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2 : ℂ) = ((q * Real.pi : ℝ) : ℂ) * Hf v a - ((q * Real.pi / 2 : ℝ) : ℂ) * Hf a a`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Simplify using `only [herm_sub_left, herm_sub_right, Complex.sub_re, Complex.re_ofReal_mul, herm_re_swap v a]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `Y a ha F hF`. Rewrite `hF`, the goal using `[h6]`. Take `⟨hd, hF⟩` from `hF`.

Use `⟨?_, fun γ hγ => ?_⟩` and prove the remaining obligations. Establish `e : U q a F = fun v => cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a)`. Use function extensionality and compare the values at `fun v => hU q a F v`. Rewrite using `[e]`. Use `herm_differentiable a` as an intermediate fact.

Use `fun_prop`. Take `⟨k, hk⟩` from `ha γ hγ`. Establish `hk' : (q : ℂ) * ((Hf a γ).im : ℂ) = k` using `by exact_mod_cast hk`. Establish `hc : U q γ (U q a F) = U q a (U q γ F)`. Rewrite using `[h1, h1, add_comm γ a]`.

Use `congr 1`. Rewrite using `[Complex.exp_eq_exp_iff_exists_int]`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[herm_im_swap a γ, ← hk']`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc]`. Use `conv_rhs => rw [← hF γ hγ]`. Use function extensionality and compare the values at `v`. Simplify using `only [Pi.smul_apply, smul_eq_mul, hU q a]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `φ N hφ a F`. Use function extensionality and compare the values at `v`. Simplify using `only [hU, Function.comp_apply, hφ, map_sub]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fock_translation_laws {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a)) (q : ℕ) :
    (∀ a b F, U q a (U q b F) = cexp (-(q * Real.pi * I * (Hf a b).im)) • U q (a + b) F) ∧ (∀ F, U q 0 F = F) ∧
    (∀ a F, (fun v => U q a F (-v)) = U q (-a) (fun v => F (-v))) ∧
    (∀ a F (M : ℕ), (U q a)^[M] F = U q ((M : ℂ) • a) F) ∧
    (∀ a F v, ‖U q a F v‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) = ‖F (v - a)‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v - a‖ ^ 2)) ∧
    (∀ (Y : GT ι) F, F ∈ Y.Sec q ↔ Differentiable ℂ F ∧ ∀ γ ∈ lat Y.b, Y.ka γ • U q γ F = F) ∧
    (∀ (Y : GT ι) a, (∀ γ ∈ lat Y.b, ∃ k : ℤ, q * (Hf a γ).im = k) → ∀ F ∈ Y.Sec q, U q a F ∈ Y.Sec q) ∧
    (∀ (φ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (N : ℕ), (∀ v w, Hf (φ v) (φ w) = N * Hf v w) →
      ∀ a F, U (q * N) a (F ∘ φ) = U q (φ a) F ∘ φ) := by
  have h1 : ∀ a b F, U q a (U q b F) =
      cexp (-(q * Real.pi * I * (Hf a b).im)) • U q (a + b) F := by
    intro a b F
    funext v
    simp only [hU, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add, sub_sub]
    congr 2
    simp only [herm_add_left, herm_add_right, herm_sub_left]
    rw [herm_sub_swap a b]
    ring
  have h2 : ∀ F, U q 0 F = F := by
    intro F
    funext v
    simp [hU, herm_zero_right]
  have h6 : ∀ (Y : GT ι) F, F ∈ Y.Sec q ↔
      Differentiable ℂ F ∧ ∀ γ ∈ lat Y.b, Y.ka γ • U q γ F = F := by
    intro Y F
    have key : ∀ γ v, (Y.ka γ • U q γ F) (v + γ) =
        Y.ka γ * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * F v := by
      intro γ v
      simp only [hU, Pi.smul_apply, smul_eq_mul, add_sub_cancel_right, herm_add_left]
      rw [← mul_assoc]
      congr 3
      ring
    refine and_congr_right fun _ => forall₂_congr fun γ _ => ⟨fun h => ?_, fun h v => ?_⟩
    · funext w
      have := key γ (w - γ)
      rw [← h, sub_add_cancel] at this
      exact this
    · rw [← key, h]
  refine ⟨h1, h2, ?_, ?_, ?_, h6, ?_, ?_⟩
  · intro a F
    funext v
    simp only [hU, herm_neg_left, herm_neg_right, neg_neg]
    congr 2
    abel
  · intro a F M
    induction M with
    | zero => simp [h2]
    | succ M ih =>
      rw [Function.iterate_succ_apply', ih, h1]
      have : (Hf a ((M : ℂ) • a)).im = 0 := by
        rw [herm_smul_right]
        simp [herm_self_im]
      rw [this]
      have e : a + (M : ℂ) • a = ((M + 1 : ℕ) : ℂ) • a := by
        push_cast
        rw [add_smul, one_smul, add_comm]
      simp [e]
  · intro a F v
    rw [hU, norm_mul, mul_pow, Complex.norm_exp, mul_comm (_ ^ 2) (‖F (v - a)‖ ^ 2), mul_assoc,
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    rw [← herm_self_re v, ← herm_self_re (v - a)]
    have e : (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2 : ℂ) =
        ((q * Real.pi : ℝ) : ℂ) * Hf v a - ((q * Real.pi / 2 : ℝ) : ℂ) * Hf a a := by
      push_cast
      ring
    rw [e]
    simp only [herm_sub_left, herm_sub_right, Complex.sub_re, Complex.re_ofReal_mul,
      herm_re_swap v a]
    push_cast
    ring
  · intro Y a ha F hF
    rw [h6] at hF ⊢
    obtain ⟨hd, hF⟩ := hF
    refine ⟨?_, fun γ hγ => ?_⟩
    · have e : U q a F = fun v =>
          cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a) :=
        funext fun v => hU q a F v
      rw [e]
      have := herm_differentiable a
      fun_prop
    · obtain ⟨k, hk⟩ := ha γ hγ
      have hk' : (q : ℂ) * ((Hf a γ).im : ℂ) = k := by exact_mod_cast hk
      have hc : U q γ (U q a F) = U q a (U q γ F) := by
        rw [h1, h1, add_comm γ a]
        congr 1
        rw [Complex.exp_eq_exp_iff_exists_int]
        refine ⟨k, ?_⟩
        rw [herm_im_swap a γ, ← hk']
        push_cast
        ring
      rw [hc]
      conv_rhs => rw [← hF γ hγ]
      funext v
      simp only [Pi.smul_apply, smul_eq_mul, hU q a]
      ring
  · intro φ N hφ a F
    funext v
    simp only [hU, Function.comp_apply, hφ, map_sub]
    congr 2
    push_cast
    ring

end GlobalTheory
