import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.RowLim

noncomputable def symS (f : ℤ → ℂ) (R : ℕ) : ℂ := ∑ d ∈ Finset.Icc (-(R : ℤ)) R, f d

/- English proof (translation)
Unfold `symS`. Establish `h : Finset.Icc (-((R + 1 : ℕ) : ℤ)) ((R + 1 : ℕ) : ℤ) = insert (-((R : ℤ) + 1)) (insert ((R : ℤ) + 1) (Finset.Icc (-(R : ℤ)) R))`. Use extensionality with `x`. Simplify using `only [Finset.mem_Icc, Finset.mem_insert]`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[h, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega), Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]`.
-/
lemma symS_succ (f : ℤ → ℂ) (R : ℕ) :
    symS f (R + 1) = f (-((R : ℤ) + 1)) + (f ((R : ℤ) + 1) + symS f R) := by
  unfold symS
  have h : Finset.Icc (-((R + 1 : ℕ) : ℤ)) ((R + 1 : ℕ) : ℤ)
      = insert (-((R : ℤ) + 1)) (insert ((R : ℤ) + 1) (Finset.Icc (-(R : ℤ)) R)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
  rw [h, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]

/- English proof (translation)
Proceed by induction on `R with`. Consider the case `zero => simp [symS]`. Consider the case `succ R ih`. Rewrite using `[symS_succ, symS_succ]`. Use `push_cast`.

Establish `e1 : -((R : ℤ) + 1) + 1 = -(R : ℤ)` using `by ring`. Rewrite using `[e1]`. Take the linear combination `ih`.
-/
lemma symS_shift_one (f : ℤ → ℂ) (R : ℕ) :
    symS (fun d => f (d + 1)) R - symS f R = f ((R : ℤ) + 1) - f (-(R : ℤ)) := by
  induction R with
  | zero => simp [symS]
  | succ R ih =>
    rw [symS_succ, symS_succ]
    push_cast
    have e1 : -((R : ℤ) + 1) + 1 = -(R : ℤ) := by ring
    rw [e1]
    linear_combination ih

/- English proof (translation)
The claim follows from `hf.mono_left (by rw [Int.cofinite_eq]; exact le_sup_right)`.
-/
lemma tendsto_atTop_of_cofinite {f : ℤ → ℂ} (hf : Tendsto f cofinite (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := hf.mono_left (by rw [Int.cofinite_eq]; exact le_sup_right)

/- English proof (translation)
The claim follows from `hf.mono_left (by rw [Int.cofinite_eq]; exact le_sup_left)`.
-/
lemma tendsto_atBot_of_cofinite {f : ℤ → ℂ} (hf : Tendsto f cofinite (𝓝 0)) :
    Tendsto f atBot (𝓝 0) := hf.mono_left (by rw [Int.cofinite_eq]; exact le_sup_left)

/- English proof (translation)
The claim follows from `hf.comp (add_left_injective r).tendsto_cofinite`.
-/
lemma shift_tendsto {f : ℤ → ℂ} (hf : Tendsto f cofinite (𝓝 0)) (r : ℤ) :
    Tendsto (fun d => f (d + r)) cofinite (𝓝 0) :=
  hf.comp (add_left_injective r).tendsto_cofinite

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => intro f _`. Simplify using the standard rewrite rules. Consider the case `succ r ih`. Introduce `f hf`.

Establish `h1` using `ih (fun e => f (e + 1)) (shift_tendsto hf 1)`. Establish `hR : Tendsto (fun R : ℕ => (R : ℤ)) atTop atTop` using `tendsto_natCast_atTop_atTop`. Establish `h2 : Tendsto (fun R : ℕ => f ((R : ℤ) + 1) - f (-(R : ℤ))) atTop (𝓝 0)`. Establish `a` using `(tendsto_atTop_of_cofinite hf).comp (tendsto_atTop_add_const_right _ 1 hR)`. Establish `b` using `(tendsto_atBot_of_cofinite hf).comp (tendsto_neg_atTop_atBot.comp hR)`.

Simplify using `using a.sub b`. Use `h1.add ((tendsto_congr (fun R => (symS_shift_one f R).symm)).1 h2)` as an intermediate fact. Rewrite `this` using `[add_zero]`. Use `(tendsto_congr fun R => ?_).1 this` and prove the remaining obligations. Establish `e : (fun d : ℤ => f (d + ((r + 1 : ℕ) : ℤ))) = fun d => f (d + (r : ℤ) + 1)`.

Use function extensionality and compare the values at `d`. Use `push_cast`. Put the polynomial expressions in normal form. Use `beta_reduce`. Rewrite using `[e]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma symS_shift_tendsto (r : ℕ) : ∀ f : ℤ → ℂ, Tendsto f cofinite (𝓝 0) →
    Tendsto (fun R => symS (fun d => f (d + r)) R - symS f R) atTop (𝓝 0) := by
  induction r with
  | zero => intro f _; simp
  | succ r ih =>
    intro f hf
    have h1 := ih (fun e => f (e + 1)) (shift_tendsto hf 1)
    have hR : Tendsto (fun R : ℕ => (R : ℤ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun R : ℕ => f ((R : ℤ) + 1) - f (-(R : ℤ))) atTop (𝓝 0) := by
      have a := (tendsto_atTop_of_cofinite hf).comp (tendsto_atTop_add_const_right _ 1 hR)
      have b := (tendsto_atBot_of_cofinite hf).comp (tendsto_neg_atTop_atBot.comp hR)
      simpa using a.sub b
    have := h1.add ((tendsto_congr (fun R => (symS_shift_one f R).symm)).1 h2)
    rw [add_zero] at this
    refine (tendsto_congr fun R => ?_).1 this
    have e : (fun d : ℤ => f (d + ((r + 1 : ℕ) : ℤ))) = fun d => f (d + (r : ℤ) + 1) := by
      funext d; push_cast; ring_nf
    beta_reduce
    rw [e]; ring

noncomputable def mean (L : ℕ) (k : ℤ → ℂ) (d : ℤ) : ℂ := (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, k (d + r)

/- English proof (translation)
Establish `: Tendsto (fun d => ∑ r ∈ Finset.range L, k (d + r)) cofinite (𝓝 0)`. Simplify using `using tendsto_finset_sum (Finset.range L) fun r _ => shift_tendsto hk r`. Establish `h2` using `this.const_mul ((L : ℂ)⁻¹)`. Rewrite `h2` using `[mul_zero]`. Conclude with `h2`.
-/
lemma mean_tendsto {L : ℕ} {k : ℤ → ℂ} (hk : Tendsto k cofinite (𝓝 0)) :
    Tendsto (mean L k) cofinite (𝓝 0) := by
  have : Tendsto (fun d => ∑ r ∈ Finset.range L, k (d + r)) cofinite (𝓝 0) := by
    simpa using tendsto_finset_sum (Finset.range L) fun r _ => shift_tendsto hk r
  have h2 := this.const_mul ((L : ℂ)⁻¹)
  rw [mul_zero] at h2
  exact h2

/- English proof (translation)
Rewrite `hk`, the goal using `[tendsto_zero_iff_norm_tendsto_zero]`. Use `squeeze_zero (fun _ => norm_nonneg _) (fun d => ?_) (by simpa using hk.const_mul C)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hA d) (norm_nonneg _)`.
-/
lemma bdd_mul_tendsto {A k : ℤ → ℂ} {C : ℝ} (hA : ∀ d, ‖A d‖ ≤ C)
    (hk : Tendsto k cofinite (𝓝 0)) : Tendsto (fun d => A d * k d) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at hk ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun d => ?_) (by simpa using hk.const_mul C)
  rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hA d) (norm_nonneg _)

/- English proof (translation)
Use `set f : ℕ → ℤ → ℂ := fun r e => A (e - r) * k e with hf`. Establish `eq : ∀ R, symS (fun d => A d * mean L k d) R = (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, (symS (fun d => f r (d + r)) R - symS (f r) R)`. Introduce `R`. Establish `h0 : ∑ r ∈ Finset.range L, symS (f r) R = 0`. Simplify using `only [symS, hf]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul, hsum, zero_mul]`. Rewrite using `[Finset.sum_sub_distrib, h0, sub_zero]`. Simplify using `only [symS, mean, hf, add_sub_cancel_right]`.

Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[show (symS fun d => A d * mean L k d) = _ from funext eq]`. Use `tendsto_finset_sum (Finset.range L) fun r _ => symS_shift_tendsto r (f r) (bdd_mul_tendsto (fun d => hA (d - r)) hk)` as an intermediate fact. Simplify using `using this.const_mul ((L : ℂ)⁻¹)`.
-/
lemma symS_mul_mean_tendsto {L : ℕ} {A k : ℤ → ℂ} {C : ℝ} (hA : ∀ d, ‖A d‖ ≤ C)
    (hsum : ∀ d, ∑ r ∈ Finset.range L, A (d - r) = 0) (hk : Tendsto k cofinite (𝓝 0)) :
    Tendsto (symS fun d => A d * mean L k d) atTop (𝓝 0) := by
  set f : ℕ → ℤ → ℂ := fun r e => A (e - r) * k e with hf
  have eq : ∀ R, symS (fun d => A d * mean L k d) R
      = (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, (symS (fun d => f r (d + r)) R - symS (f r) R) := by
    intro R
    have h0 : ∑ r ∈ Finset.range L, symS (f r) R = 0 := by
      simp only [symS, hf]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [← Finset.sum_mul, hsum, zero_mul]
    rw [Finset.sum_sub_distrib, h0, sub_zero]
    simp only [symS, mean, hf, add_sub_cancel_right]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [show (symS fun d => A d * mean L k d) = _ from funext eq]
  have := tendsto_finset_sum (Finset.range L) fun r _ =>
    symS_shift_tendsto r (f r) (bdd_mul_tendsto (fun d => hA (d - r)) hk)
  simpa using this.const_mul ((L : ℂ)⁻¹)

/- English proof (translation)
Introduce `L A g G c _ ⟨C, hA⟩ hsum hG hg hS`. Establish `hpt : ∀ (F : ℤ × ℤ → ℂ) (d : ℤ), dif L (0, 1) F (c, d) = F (c, d) - mean L (fun e => F (c, e)) d`. Introduce `F d`. Establish `e : ∀ r : ℕ, (c, d) + (r : ℤ) • ((0 : ℤ), (1 : ℤ)) = (c, d + r)`. Apply the tactic sequence `intro r; ext <;> simp`.

Simplify using `only [dif, mean, e]`. Use `set h : ℤ → ℂ := fun d => g d - mean L g d with hh`. Establish `hG1 : ∀ d, dif L (0, 1) G (c, d) = h d`. Introduce `d`. Rewrite using `[hpt]`.

Simplify using `only [hh, hG]`. Establish `hG2 : ∀ d, dif L (0, 1) (dif L (0, 1) G) (c, d) = h d - mean L h d`. Introduce `d`. Rewrite using `[hpt, hG1]`. Simplify using `only [hG1]`.

Simplify using `only [hG2] at hS ⊢`. Establish `hTs` using `(hS.hasSum.comp Finset.tendsto_Icc_neg)`. Establish `hh0 : Tendsto h cofinite (𝓝 0)` using `by simpa using hg.sub (mean_tendsto hg)`. Establish `k1` using `symS_mul_mean_tendsto hA hsum hg`. Establish `k2` using `symS_mul_mean_tendsto hA hsum hh0`.

Use `(hTs.add k1).add k2` as an intermediate fact. Rewrite `this` using `[add_zero, add_zero]`. Use `(tendsto_congr fun R => ?_).1 this` and prove the remaining obligations. Simplify using `only [Function.comp, symS, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Simplify using `only [hh]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rowlim : ∀ (L : ℕ) (A g : ℤ → ℂ) (G : ℤ × ℤ → ℂ) (c : ℤ), 0 < L → (∃ C : ℝ, ∀ d, ‖A d‖ ≤ C) → (∀ d, ∑ r ∈ Finset.range L, A (d - r) = 0) → (∀ d, G (c, d) = g d) → Tendsto g cofinite (𝓝 0) → (Summable fun d : ℤ => A d * dif L (0, 1) (dif L (0, 1) G) (c, d)) → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, A d * g d) atTop (𝓝 (∑' d : ℤ, A d * dif L (0, 1) (dif L (0, 1) G) (c, d))) := by
  intro L A g G c _ ⟨C, hA⟩ hsum hG hg hS
  have hpt : ∀ (F : ℤ × ℤ → ℂ) (d : ℤ), dif L (0, 1) F (c, d) = F (c, d) - mean L (fun e => F (c, e)) d := by
    intro F d
    have e : ∀ r : ℕ, (c, d) + (r : ℤ) • ((0 : ℤ), (1 : ℤ)) = (c, d + r) := by
      intro r; ext <;> simp
    simp only [dif, mean, e]
  set h : ℤ → ℂ := fun d => g d - mean L g d with hh
  have hG1 : ∀ d, dif L (0, 1) G (c, d) = h d := by
    intro d; rw [hpt]; simp only [hh, hG]
  have hG2 : ∀ d, dif L (0, 1) (dif L (0, 1) G) (c, d) = h d - mean L h d := by
    intro d; rw [hpt, hG1]; simp only [hG1]
  simp only [hG2] at hS ⊢
  have hTs := (hS.hasSum.comp Finset.tendsto_Icc_neg)
  have hh0 : Tendsto h cofinite (𝓝 0) := by simpa using hg.sub (mean_tendsto hg)
  have k1 := symS_mul_mean_tendsto hA hsum hg
  have k2 := symS_mul_mean_tendsto hA hsum hh0
  have := (hTs.add k1).add k2
  rw [add_zero, add_zero] at this
  refine (tendsto_congr fun R => ?_).1 this
  simp only [Function.comp, symS, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [hh]; ring

end GlobalTheory.RowLim
