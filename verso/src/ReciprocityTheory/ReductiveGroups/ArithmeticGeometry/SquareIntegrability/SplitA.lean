import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

section basic

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Simplify using `[Hf, PiLp.inner_apply, RCLike.inner_apply]`.
-/
private theorem Hf_eq_inner_swap_complex (v w : EuclideanSpace ℂ ι) : Hf v w = inner ℂ w v := by
  simp [Hf, PiLp.inner_apply, RCLike.inner_apply]

/- English proof (translation)
Use `first`. Consider the case `exact real_inner_eq_re_inner ℂ x y`. Consider the case `simp [PiLp.inner_apply, Complex.inner, Complex.re_sum, RCLike.inner_apply, mul_comm]`.
-/
private theorem real_inner_eq_re_inner' (x y : EuclideanSpace ℂ ι) : ⟪x, y⟫_ℝ = (inner ℂ x y).re := by
  first
  | exact real_inner_eq_re_inner ℂ x y
  | simp [PiLp.inner_apply, Complex.inner, Complex.re_sum, RCLike.inner_apply, mul_comm]

/- English proof (translation)
Rewrite using `[Hf_eq_inner_swap_complex, Hf_eq_inner_swap_complex]`. Conclude with `(inner_conj_symm _ _).symm`.
-/
theorem Hf_conj (v w : EuclideanSpace ℂ ι) : Hf w v = (starRingEnd ℂ) (Hf v w) := by
  rw [Hf_eq_inner_swap_complex, Hf_eq_inner_swap_complex]
  exact (inner_conj_symm _ _).symm

/- English proof (translation)
Rewrite using `[Hf_eq_inner_swap_complex, Hf_eq_inner_swap_complex, inner_smul_left]`.
-/
theorem Hf_smul_right (c : ℂ) (v w : EuclideanSpace ℂ ι) :
    Hf v (c • w) = (starRingEnd ℂ) c * Hf v w := by
  rw [Hf_eq_inner_swap_complex, Hf_eq_inner_swap_complex, inner_smul_left]

/- English proof (translation)
Rewrite using `[Hf_eq_inner_swap_complex, real_inner_eq_re_inner']`.
-/
theorem real_inner_eq_Hf (x y : EuclideanSpace ℂ ι) : ⟪x, y⟫_ℝ = (Hf y x).re := by
  rw [Hf_eq_inner_swap_complex, real_inner_eq_re_inner']

/- English proof (translation)
Rewrite using `[real_inner_eq_re_inner', inner_smul_left, Hf_eq_inner_swap_complex]`. Simplify using the standard rewrite rules.
-/
theorem Hf_im_eq (v w : EuclideanSpace ℂ ι) : (Hf v w).im = ⟪Complex.I • w, v⟫_ℝ := by
  rw [real_inner_eq_re_inner', inner_smul_left, Hf_eq_inner_swap_complex]
  simp

/- English proof (translation)
Rewrite using `[Hf_conj w v, Complex.conj_im, Hf_im_eq w v, inner_neg_left]`.
-/
theorem Hf_im_eq' (v w : EuclideanSpace ℂ ι) : (Hf v w).im = ⟪-(Complex.I • v), w⟫_ℝ := by
  rw [Hf_conj w v, Complex.conj_im, Hf_im_eq w v, inner_neg_left]

/- English proof (translation)
Rewrite using `[Hf_conj w v, Complex.conj_im]`.
-/
theorem Hf_im_antisymm (v w : EuclideanSpace ℂ ι) : (Hf v w).im = -(Hf w v).im := by
  rw [Hf_conj w v, Complex.conj_im]

/- English proof (translation)
Simplify using `only [Hf_eq_inner_swap_complex, inner_add_right, Complex.add_im]`.
-/
theorem Hf_im_add_left (v v' w : EuclideanSpace ℂ ι) :
    (Hf (v + v') w).im = (Hf v w).im + (Hf v' w).im := by
  simp only [Hf_eq_inner_swap_complex, inner_add_right, Complex.add_im]

/- English proof (translation)
Simplify using `only [Hf_eq_inner_swap_complex, inner_add_left, Complex.add_im]`.
-/
theorem Hf_im_add_right (v w w' : EuclideanSpace ℂ ι) :
    (Hf v (w + w')).im = (Hf v w).im + (Hf v w').im := by
  simp only [Hf_eq_inner_swap_complex, inner_add_left, Complex.add_im]

/- English proof (translation)
Simplify using `[Hf, Complex.im_sum, Finset.mul_sum, mul_assoc]`.
-/
theorem Hf_im_smul_left (r : ℝ) (v w : EuclideanSpace ℂ ι) :
    (Hf (r • v) w).im = r * (Hf v w).im := by
  simp [Hf, Complex.im_sum, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `[Hf, Complex.im_sum, Finset.mul_sum, mul_left_comm]`.
-/
theorem Hf_im_smul_right (r : ℝ) (v w : EuclideanSpace ℂ ι) :
    (Hf v (r • w)).im = r * (Hf v w).im := by
  simp [Hf, Complex.im_sum, Finset.mul_sum, mul_left_comm]

/- English proof (translation)
Simplify using `[Hf]`.
-/
theorem Hf_im_zero_left (w : EuclideanSpace ℂ ι) : (Hf 0 w).im = 0 := by
  simp [Hf]

/- English proof (translation)
Simplify using `[Hf]`.
-/
theorem Hf_im_zero_right (v : EuclideanSpace ℂ ι) : (Hf v 0).im = 0 := by
  simp [Hf]

/- English proof (translation)
Rewrite using `[Hf_eq_inner_swap_complex, mul_comm]`. Conclude with `(Complex.abs_im_le_norm _).trans (norm_inner_le_norm w v)`.
-/
theorem abs_Hf_im_le (v w : EuclideanSpace ℂ ι) : |(Hf v w).im| ≤ ‖v‖ * ‖w‖ := by
  rw [Hf_eq_inner_swap_complex, mul_comm]
  exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm w v)

/- English proof (translation)
Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx`. Consider the case `zero => exact Hf_im_zero_left w`. Consider the case `add x y _ _ hx hy => rw [Hf_im_add_left, hx, hy, add_zero]`.

Consider the case `smul a x _ hx => rw [Hf_im_smul_left, hx, mul_zero]`.
-/
theorem Hf_im_span_left (S : Set (EuclideanSpace ℂ ι)) (w : EuclideanSpace ℂ ι)
    (h : ∀ v ∈ S, (Hf v w).im = 0) : ∀ v ∈ Submodule.span ℝ S, (Hf v w).im = 0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact Hf_im_zero_left w
  | add x y _ _ hx hy => rw [Hf_im_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [Hf_im_smul_left, hx, mul_zero]

/- English proof (translation)
Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx`. Consider the case `zero => exact Hf_im_zero_right v`. Consider the case `add x y _ _ hx hy => rw [Hf_im_add_right, hx, hy, add_zero]`.

Consider the case `smul a x _ hx => rw [Hf_im_smul_right, hx, mul_zero]`.
-/
theorem Hf_im_span_right (S : Set (EuclideanSpace ℂ ι)) (v : EuclideanSpace ℂ ι)
    (h : ∀ w ∈ S, (Hf v w).im = 0) : ∀ w ∈ Submodule.span ℝ S, (Hf v w).im = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact Hf_im_zero_right v
  | add x y _ _ hx hy => rw [Hf_im_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [Hf_im_smul_right, hx, mul_zero]

/- English proof (translation)
Introduce `v hv w hw`. Conclude with `Hf_im_span_right S v (fun w' hw' => Hf_im_span_left S w' (fun v' hv' => h v' hv' w' hw') v hv) w hw`.
-/
theorem Hf_im_span_iso (S : Set (EuclideanSpace ℂ ι)) (h : ∀ v ∈ S, ∀ w ∈ S, (Hf v w).im = 0) :
    ∀ v ∈ Submodule.span ℝ S, ∀ w ∈ Submodule.span ℝ S, (Hf v w).im = 0 := by
  intro v hv w hw
  exact Hf_im_span_right S v (fun w' hw' => Hf_im_span_left S w' (fun v' hv' => h v' hv' w' hw') v hv) w hw

end basic

variable {E : Type} [Field E] [NumberField E]

section vecU

variable {dim : (E →+* ℂ) → ℕ}

/- English proof (translation)
Set `K` to `IR I`. Set `f : K →ₗ[ℝ] ℝ` to `{ toFun := fun a => (Hf x (a : Vsp dim)).im map_add' := fun a b => by simp only [Submodule.coe_add, Hf_im_add_right] map_smul' := fun c a => by`. Simplify using `only [Submodule.coe_smul, Hf_im_smul_right, smul_eq_mul, RingHom.id_apply] }`. Set `u : K` to `(InnerProductSpace.toDual ℝ K).symm (LinearMap.toContinuousLinearMap f)`. Use `⟨(u : Vsp dim), u.2, fun a ha => ?_⟩` and prove the remaining obligations.

Establish `h1` using `InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := K) (x := ⟨a, ha⟩) (y := LinearMap.toContinuousLinearMap f)`. Conclude with `h1`.
-/
theorem exists_isU (I : Submodule ℤ (Vsp dim)) (x : Vsp dim) : ∃ u, IsU I x u := by
  let K := IR I
  let f : K →ₗ[ℝ] ℝ :=
    { toFun := fun a => (Hf x (a : Vsp dim)).im
      map_add' := fun a b => by simp only [Submodule.coe_add, Hf_im_add_right]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul, Hf_im_smul_right, smul_eq_mul, RingHom.id_apply] }
  let u : K := (InnerProductSpace.toDual ℝ K).symm (LinearMap.toContinuousLinearMap f)
  refine ⟨(u : Vsp dim), u.2, fun a ha => ?_⟩
  have h1 := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := K) (x := ⟨a, ha⟩)
    (y := LinearMap.toContinuousLinearMap f)
  exact h1

/- English proof (translation)
Establish `hd : u - u' ∈ IR I` using `Submodule.sub_mem _ h.1 h'.1`. Establish `h0 : inner ℝ (u - u') (u - u') = (0 : ℝ)`. Rewrite using `[inner_sub_left, h.2 _ hd, h'.2 _ hd, sub_self]`. Conclude with `sub_eq_zero.1 (inner_self_eq_zero.1 h0)`.
-/
theorem IsU.unique {I : Submodule ℤ (Vsp dim)} {x u u' : Vsp dim} (h : IsU I x u)
    (h' : IsU I x u') : u = u' := by
  have hd : u - u' ∈ IR I := Submodule.sub_mem _ h.1 h'.1
  have h0 : inner ℝ (u - u') (u - u') = (0 : ℝ) := by
    rw [inner_sub_left, h.2 _ hd, h'.2 _ hd, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

/- English proof (translation)
Rewrite using `[← real_inner_self_eq_norm_sq, h.2 u h.1]`.
-/
theorem IsU.norm_sq {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim} (h : IsU I x u) :
    ‖u‖ ^ 2 = (Hf x u).im := by
  rw [← real_inner_self_eq_norm_sq, h.2 u h.1]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl a ha`. Rewrite using `[← h.2 a (Submodule.subset_span ha), inner_zero_left]`. Introduce `hI`. Establish `hs` using `Hf_im_span_right (I : Set (Vsp dim)) x (fun w hw => hI w hw) u h.1`.

Establish `h0 : inner ℝ u u = (0 : ℝ)` using `by rw [h.2 u h.1, hs]`. Conclude with `inner_self_eq_zero.1 h0`.
-/
theorem IsU.eq_zero_iff {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim} (h : IsU I x u) :
    u = 0 ↔ ∀ a ∈ I, (Hf x a).im = 0 := by
  constructor
  · rintro rfl a ha
    rw [← h.2 a (Submodule.subset_span ha), inner_zero_left]
  · intro hI
    have hs := Hf_im_span_right (I : Set (Vsp dim)) x (fun w hw => hI w hw) u h.1
    have h0 : inner ℝ u u = (0 : ℝ) := by rw [h.2 u h.1, hs]
    exact inner_self_eq_zero.1 h0

/- English proof (translation)
The claim follows from `Submodule.subset_span h`.
-/
theorem mem_IR {I : Submodule ℤ (Vsp dim)} {x : Vsp dim} (h : x ∈ I) : x ∈ IR I := Submodule.subset_span h

end vecU

end

end ReciprocityTheory.ChartRestriction.G.I2
