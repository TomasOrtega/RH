import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.IKDiscrete

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

/- English proof (translation)
Simplify using `[z, Hf, add_mul, Finset.sum_add_distrib]`.
-/
theorem z_add {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (k : Fin (dK K))
    (v w : EuclideanSpace ℂ ι) : z K k (v + w) = z K k v + z K k w := by
  simp [z, Hf, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[z, Hf, Finset.mul_sum, mul_assoc]`.
-/
theorem z_rsmul {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (k : Fin (dK K))
    (t : ℝ) (v : EuclideanSpace ℂ ι) : z K k (t • v) = t * z K k v := by
  simp [z, Hf, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Use `Finset.induction_on F ?_ ?_` and prove the remaining obligations. Simplify using `[z, Hf]`. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, z_add, ih]`.
-/
theorem z_sum {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (k : Fin (dK K))
    {κ : Type} (F : Finset κ) (f : κ → EuclideanSpace ℂ ι) :
    z K k (∑ j ∈ F, f j) = ∑ j ∈ F, z K k (f j) := by
  classical
  refine Finset.induction_on F ?_ ?_
  · simp [z, Hf]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, z_add, ih]

/- English proof (translation)
Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`.
-/
theorem conj_eq (ξ : ℂ) : (starRingEnd ℂ) ξ = ξ - 2 * (ξ.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp <;> ring

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

def gaugeExp (I : Submodule ℤ (Vsp X.dim)) (γ v : Vsp X.dim) : ℂ :=
  -(2 * Real.pi * Complex.I * ∑ k, ((z (IR I) k γ).im : ℂ) * z (IR I) k v) -
    Real.pi * Complex.I * ∑ k, z (IR I) k γ * ((z (IR I) k γ).im : ℂ) +
    Real.pi * Hf (p2 (IR I) v) (p2 (IR I) γ) + Real.pi * Hf (p2 (IR I) γ) (p2 (IR I) γ) / 2

/- English proof (translation)
Simplify using `[Hf, add_mul, Finset.sum_add_distrib]`.
-/
private theorem Hf_add_left_euclidean {ι : Type} [Fintype ι] (x x' y : EuclideanSpace ℂ ι) :
    Hf (x + x') y = Hf x y + Hf x' y := by
  simp [Hf, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[Hf, Finset.mul_sum, mul_assoc]`.
-/
private theorem Hf_real_smul_left {ι : Type} [Fintype ι] (t : ℝ) (x y : EuclideanSpace ℂ ι) :
    Hf (t • x) y = t * Hf x y := by
  simp [Hf, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `[Hf, mul_add, Finset.sum_add_distrib]`.
-/
private theorem Hf_add_right_euclidean {ι : Type} [Fintype ι] (x y y' : EuclideanSpace ℂ ι) :
    Hf x (y + y') = Hf x y + Hf x y' := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[Hf, Finset.mul_sum, mul_left_comm]`.
-/
private theorem Hf_real_smul_right' {ι : Type} [Fintype ι] (t : ℝ) (x y : EuclideanSpace ℂ ι) :
    Hf x (t • y) = t * Hf x y := by
  simp [Hf, Finset.mul_sum, mul_left_comm]

/- English proof (translation)
Introduce `a ha b hb`. Express the relevant statement in the definitionally equal form `a ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) at ha`. Express the relevant statement in the definitionally equal form `b ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) at hb`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem y hy`.

Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx => exact hI.iso x hx y hy`. Consider the case `zero => simp [Hf]`. Consider the case `add x x' _ _ h1 h2 => rw [Hf_add_left_euclidean, Complex.add_im, h1, h2, add_zero]`. Consider the case `smul t x _ h => rw [Hf_real_smul_left, Complex.im_ofReal_mul, h, mul_zero]`.

Consider the case `zero => simp [Hf]`. Consider the case `add y y' _ _ h1 h2 => rw [Hf_add_right_euclidean, Complex.add_im, h1, h2, add_zero]`. Consider the case `smul t y _ h => rw [Hf_real_smul_right', Complex.im_ofReal_mul, h, mul_zero]`.
-/
private theorem Hf_im_eq_zero_on_IR_of_isSplit (hI : IsSplit P I) :
    ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0 := by
  intro a ha b hb
  change a ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) at ha
  change b ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) at hb
  induction hb using Submodule.span_induction with
  | mem y hy =>
    induction ha using Submodule.span_induction with
    | mem x hx => exact hI.iso x hx y hy
    | zero => simp [Hf]
    | add x x' _ _ h1 h2 => rw [Hf_add_left_euclidean, Complex.add_im, h1, h2, add_zero]
    | smul t x _ h => rw [Hf_real_smul_left, Complex.im_ofReal_mul, h, mul_zero]
  | zero => simp [Hf]
  | add y y' _ _ h1 h2 => rw [Hf_add_right_euclidean, Complex.add_im, h1, h2, add_zero]
  | smul t y _ h => rw [Hf_real_smul_right', Complex.im_ofReal_mul, h, mul_zero]

/- English proof (translation)
Establish `hsec` using `hs.2 (fun _ => γ) (fun _ => hγ) (fun _ => v)`. Establish `hfun : (fun _ : Fin 1 => v + γ) = (fun _ => v) + (fun _ => γ)` using `rfl`. Establish `hkey : ∀ a b c d : ℂ, a + b = c + d → (X.eps γ : ℂ) * Complex.exp a * s (fun _ => v) * Complex.exp b = (X.eps γ : ℂ) * Complex.exp c * (s (fun _ => v) * Complex.exp d)`. Introduce `a b c d h`. Establish `hab : Complex.exp a * Complex.exp b = Complex.exp c * Complex.exp d`.

Rewrite using `[← Complex.exp_add, ← Complex.exp_add, h]`. Take the linear combination `((X.eps γ : ℂ) * s (fun _ => v)) * hab`. Establish `e1 : ∑ k, z (IR I) k v * (starRingEnd ℂ) (z (IR I) k γ) = ∑ k, z (IR I) k v * z (IR I) k γ - 2 * Complex.I * ∑ k, ((z (IR I) k γ).im : ℂ) * z (IR I) k v`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[conj_eq]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∑ k, z (IR I) k γ * (starRingEnd ℂ) (z (IR I) k γ) = ∑ k, z (IR I) k γ ^ 2 - 2 * Complex.I * ∑ k, z (IR I) k γ * ((z (IR I) k γ).im : ℂ)`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[conj_eq]`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : Col.S (IR I) (v + γ) = Col.S (IR I) v + 2 * ∑ k, z (IR I) k v * z (IR I) k γ + ∑ k, z (IR I) k γ ^ 2`. Simplify using `only [Col.S, z_add, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Unfold `zmG`. Rewrite using `[hfun, hsec]`. Simplify using `only [Fin.prod_univ_one, pow_one]`. Apply `hkey` to reduce the goal to its premises.

Simplify using `only [HC, Fin.sum_univ_one, Nat.cast_one, one_mul]`. Rewrite using `[e3, Col.Hf_decomp (K := IR I) (Hf_im_eq_zero_on_IR_of_isSplit hI) v γ, Col.Hf_decomp (K := IR I) (Hf_im_eq_zero_on_IR_of_isSplit hI) γ γ, e1, e2]`. Unfold `gaugeExp`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zmG_add (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    {γ : Vsp X.dim} (hγ : γ ∈ X.L) (v : Vsp X.dim) :
    zmG I s (v + γ) = (X.eps γ : ℂ) * Complex.exp (gaugeExp I γ v) * zmG I s v := by
  have hsec := hs.2 (fun _ => γ) (fun _ => hγ) (fun _ => v)
  have hfun : (fun _ : Fin 1 => v + γ) = (fun _ => v) + (fun _ => γ) := rfl
  have hkey : ∀ a b c d : ℂ, a + b = c + d →
      (X.eps γ : ℂ) * Complex.exp a * s (fun _ => v) * Complex.exp b =
        (X.eps γ : ℂ) * Complex.exp c * (s (fun _ => v) * Complex.exp d) := by
    intro a b c d h
    have hab : Complex.exp a * Complex.exp b = Complex.exp c * Complex.exp d := by
      rw [← Complex.exp_add, ← Complex.exp_add, h]
    linear_combination ((X.eps γ : ℂ) * s (fun _ => v)) * hab
  have e1 : ∑ k, z (IR I) k v * (starRingEnd ℂ) (z (IR I) k γ) =
      ∑ k, z (IR I) k v * z (IR I) k γ -
        2 * Complex.I * ∑ k, ((z (IR I) k γ).im : ℂ) * z (IR I) k v := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conj_eq]
    ring
  have e2 : ∑ k, z (IR I) k γ * (starRingEnd ℂ) (z (IR I) k γ) =
      ∑ k, z (IR I) k γ ^ 2 -
        2 * Complex.I * ∑ k, z (IR I) k γ * ((z (IR I) k γ).im : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conj_eq]
    ring
  have e3 : Col.S (IR I) (v + γ) =
      Col.S (IR I) v + 2 * ∑ k, z (IR I) k v * z (IR I) k γ + ∑ k, z (IR I) k γ ^ 2 := by
    simp only [Col.S, z_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold zmG
  rw [hfun, hsec]
  simp only [Fin.prod_univ_one, pow_one]
  apply hkey
  simp only [HC, Fin.sum_univ_one, Nat.cast_one, one_mul]
  rw [e3, Col.Hf_decomp (K := IR I) (Hf_im_eq_zero_on_IR_of_isSplit hI) v γ, Col.Hf_decomp (K := IR I) (Hf_im_eq_zero_on_IR_of_isSplit hI) γ γ, e1, e2]
  unfold gaugeExp
  push_cast
  ring

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
