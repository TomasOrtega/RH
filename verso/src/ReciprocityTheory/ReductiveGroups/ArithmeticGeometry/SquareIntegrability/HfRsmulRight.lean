import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

/- English proof (translation)
Unfold `Hf`. Rewrite using `[PiLp.inner_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[RCLike.inner_apply, mul_comm]`.
-/
lemma Hf_eq_inner {ι : Type} [Fintype ι] (v w : EuclideanSpace ℂ ι) : Hf v w = inner ℂ w v := by
  unfold Hf
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply, mul_comm]

/- English proof (translation)
Unfold `Hf`. Rewrite using `[PiLp.inner_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma re_Hf {ι : Type} [Fintype ι] (v w : EuclideanSpace ℂ ι) : (Hf v w).re = inner ℝ v w := by
  unfold Hf
  rw [PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/- English proof (translation)
Simplify using `only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
lemma Hf_add_left {ι : Type} [Fintype ι] (v v' w : EuclideanSpace ℂ ι) :
    Hf (v + v') w = Hf v w + Hf v' w := by
  simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[Hf]`.
-/
lemma Hf_zero_left {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) : Hf 0 v = 0 := by
  simp [Hf]

open Classical in

def prj {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Vsp dim →ₗ[ℂ] Vsp dim where
  toFun v := WithLp.toLp 2 fun i => if i.1 = σ then v i else 0
  map_add' v w := by ext i; simp only [PiLp.add_apply]; split_ifs <;> simp
  map_smul' c v := by ext i; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma prj_apply {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) (i : Idx dim) :
    prj σ v i = if i.1 = σ then v i else 0 := rfl

/- English proof (translation)
Introduce `j hj`. Rewrite using `[prj_apply, if_neg hj]`.
-/
lemma prj_inPart {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : InPart σ (prj σ v) := by
  intro j hj
  rw [prj_apply, if_neg hj]

/- English proof (translation)
Unfold `Hf`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[prj_apply]`. Use `split_ifs with h`. Both sides reduce to the same expression.

Rewrite using `[hv i h, zero_mul, zero_mul]`.
-/
lemma Hf_prj_right {dim : (E →+* ℂ) → ℕ} {σ : E →+* ℂ} {v : Vsp dim} (hv : InPart σ v) (x : Vsp dim) :
    Hf v (prj σ x) = Hf v x := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prj_apply]
  split_ifs with h
  · rfl
  · rw [hv i h, zero_mul, zero_mul]

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[prj_apply]`.

Use `split_ifs`. Conclude with `le_rfl`. Rewrite using `[norm_zero, zero_pow two_ne_zero]`. Check the signs of the components of the expression.
-/
lemma norm_prj_le {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : ‖prj σ v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  rw [prj_apply]
  split_ifs
  · exact le_rfl
  · rw [norm_zero, zero_pow two_ne_zero]
    positivity

/- English proof (translation)
Introduce `h`. Establish `hc` using `NumberField.IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk σ)`. Rewrite `hc` using `[NumberField.InfinitePlace.isComplex_mk_iff]`. Conclude with `hc (ComplexEmbedding.isReal_iff.mpr h)`.
-/
lemma ne_conj [IsCMField E] (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ≠ σ := by
  intro h
  have hc := NumberField.IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk σ)
  rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
  exact hc (ComplexEmbedding.isReal_iff.mpr h)

open Classical in

def Mc {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) : Vsp dim →ₗ[ℂ] Vsp dim where
  toFun v := WithLp.toLp 2 fun i => if i.1 = σ then c * v i else
    if i.1 = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c * v i else 0
  map_add' v w := by ext i; simp only [PiLp.add_apply]; split_ifs <;> ring
  map_smul' a v := by ext i; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma Mc_apply {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v : Vsp dim) (i : Idx dim) :
    Mc σ c v i = if i.1 = σ then c * v i else
      if i.1 = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c * v i else 0 := rfl

/- English proof (translation)
Rewrite using `[PiLp.inner_apply, PiLp.inner_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Mc_apply, Mc_apply]`. Apply the tactic sequence `split_ifs <;> simp only [Complex.inner, map_mul, Complex.conj_conj, mul_zero, zero_mul, map_zero] <;> ring_nf`.
-/
lemma real_inner_Mc {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v w : Vsp dim) :
    inner ℝ (Mc σ c v) w = inner ℝ v (Mc σ ((starRingEnd ℂ) c) w) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Mc_apply, Mc_apply]
  split_ifs <;> simp only [Complex.inner, map_mul, Complex.conj_conj, mul_zero, zero_mul,
    map_zero] <;> ring_nf

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[prj_apply, PiLp.smul_apply, prj_apply, Mc_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma prj_Mc {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v : Vsp dim) :
    prj σ (Mc σ c v) = c • prj σ v := by
  ext i
  rw [prj_apply, PiLp.smul_apply, prj_apply, Mc_apply, smul_eq_mul]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [prj_apply, PiLp.smul_apply, PiLp.sub_apply, Mc_apply, smul_eq_mul, map_one, Complex.conj_I]`. Use `split_ifs`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`.

Expand and normalize the polynomial expressions, which then agree. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
lemma prj_eq_Mc [IsCMField E] {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) :
    prj σ v = (1 / 2 : ℂ) • (Mc σ 1 v - Complex.I • Mc σ Complex.I v) := by
  ext i
  simp only [prj_apply, PiLp.smul_apply, PiLp.sub_apply, Mc_apply, smul_eq_mul, map_one,
    Complex.conj_I]
  split_ifs
  · ring_nf
    rw [Complex.I_sq]
    ring
  · ring_nf
    rw [Complex.I_sq]
    ring
  · ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨add_mem hu.1 hv.1, fun a ha => by rw [inner_add_left, hu.2 a ha, hv.2 a ha, Hf_add_left, Complex.add_im]⟩`.
-/
lemma isU_add {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)} {x y u v : Vsp dim}
    (hu : IsU I x u) (hv : IsU I y v) : IsU I (x + y) (u + v) :=
    ⟨add_mem hu.1 hv.1, fun a ha => by
      rw [inner_add_left, hu.2 a ha, hv.2 a ha, Hf_add_left, Complex.add_im]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨neg_mem hu.1, fun a ha => by have hn : Hf (-x) a = -Hf x a := by simp [Hf, Finset.sum_neg_distrib] rw [inner_neg_left, hu.2 a ha, hn, Complex.neg_im]⟩`.
-/
lemma isU_neg {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim}
    (hu : IsU I x u) : IsU I (-x) (-u) :=
    ⟨neg_mem hu.1, fun a ha => by
      have hn : Hf (-x) a = -Hf x a := by simp [Hf, Finset.sum_neg_distrib]
      rw [inner_neg_left, hu.2 a ha, hn, Complex.neg_im]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨zero_mem _, fun a _ => by rw [inner_zero_left, Hf_zero_left, Complex.zero_im]⟩`.
-/
lemma isU_zero {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : IsU I 0 0 :=
    ⟨zero_mem _, fun a _ => by rw [inner_zero_left, Hf_zero_left, Complex.zero_im]⟩

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
