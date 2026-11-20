import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice

noncomputable section

namespace PI.Dv.GLP

open Formalism.HermitianLatticesTheory NumberField

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)

/- English proof (translation)
Unfold `fcoord vecAt`. Rewrite using `[← Matrix.mulVec_smul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem fcoord_smul' (c : K) (x : V) : fcoord b X v (c • x) = v.embedding c • fcoord b X v x := by
  unfold fcoord vecAt
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

/- English proof (translation)
Unfold `fcoord vecAt`. Rewrite using `[← Matrix.mulVec_add]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
private theorem fcoord_add_projection_lattices (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  unfold fcoord vecAt
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp

/- English proof (translation)
Unfold `majAt`. Rewrite using `[fcoord_add_projection_lattices]`. Simplify using `[add_mul, Finset.sum_add_distrib]`.
-/
theorem majAt_add_left' (x x' y : V) : majAt b X v (x + x') y = majAt b X v x y + majAt b X v x' y := by
  unfold majAt
  rw [fcoord_add_projection_lattices]
  simp [add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `majAt`. Rewrite using `[fcoord_add_projection_lattices]`. Simplify using `[mul_add, Finset.sum_add_distrib]`.
-/
theorem majAt_add_right' (x y y' : V) : majAt b X v x (y + y') = majAt b X v x y + majAt b X v x y' := by
  unfold majAt
  rw [fcoord_add_projection_lattices]
  simp [mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `majAt`. Rewrite using `[fcoord_smul', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, star_mul']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem majAt_smul_left' (c : K) (x y : V) :
    majAt b X v (c • x) y = star (v.embedding c) * majAt b X v x y := by
  unfold majAt
  rw [fcoord_smul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

/- English proof (translation)
Unfold `majAt`. Rewrite using `[fcoord_smul', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem majAt_smul_right' (c : K) (x y : V) :
    majAt b X v x (c • y) = v.embedding c * majAt b X v x y := by
  unfold majAt
  rw [fcoord_smul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `majAt`. Rewrite using `[star_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul', star_star, mul_comm]`.
-/
theorem majAt_swap' (x y : V) : majAt b X v y x = star (majAt b X v x y) := by
  unfold majAt
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul', star_star, mul_comm]

/- English proof (translation)
Unfold `majAt normAt cnorm`. Rewrite using `[Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`.
-/
theorem majAt_self' (x : V) : majAt b X v x x = ((normAt b X v x ^ 2 : ℝ) : ℂ) := by
  unfold majAt normAt cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

/- English proof (translation)
Conclude with `map_sum (AddMonoidHom.mk' (fun x => majAt b X v x y) fun x x' => majAt_add_left' b X v x x' y) f s`.
-/
theorem majAt_sum_left' {α : Type} (s : Finset α) (f : α → V) (y : V) :
    majAt b X v (∑ i ∈ s, f i) y = ∑ i ∈ s, majAt b X v (f i) y := by
  exact map_sum (AddMonoidHom.mk' (fun x => majAt b X v x y) fun x x' => majAt_add_left' b X v x x' y) f s

/- English proof (translation)
Conclude with `map_sum (AddMonoidHom.mk' (fun y => majAt b X v x y) fun y y' => majAt_add_right' b X v x y y') f s`.
-/
theorem majAt_sum_right' {α : Type} (s : Finset α) (f : α → V) (x : V) :
    majAt b X v x (∑ i ∈ s, f i) = ∑ i ∈ s, majAt b X v x (f i) := by
  exact map_sum (AddMonoidHom.mk' (fun y => majAt b X v x y) fun y y' => majAt_add_right' b X v x y y') f s

/- English proof (translation)
Simplify using `only [majAt_add_left', majAt_add_right', majAt_smul_left', majAt_smul_right']`. Rewrite using `[majAt_swap' b X v u w]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem majAt_expand' (c : K) (u w : V) :
    majAt b X v (u + c • w) (u + c • w) = majAt b X v u u + v.embedding c * majAt b X v u w +
      star (v.embedding c) * star (majAt b X v u w) +
      star (v.embedding c) * v.embedding c * majAt b X v w w := by
  simp only [majAt_add_left', majAt_add_right', majAt_smul_left', majAt_smul_right']
  rw [majAt_swap' b X v u w]
  ring

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use `(InfinitePlace.not_isReal_iff_isComplex.mpr (NumberField.IsTotallyComplex.isComplex v)) ?_` and prove the remaining obligations. Rewrite using `[InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]`. Use extensionality with `c`.

Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `Complex.conj_eq_iff_im.mpr (h c)`.
-/
theorem exists_nonreal [NumberField.IsTotallyComplex K] : ∃ c : K, (v.embedding c).im ≠ 0 := by
  by_contra h
  push_neg at h
  refine (InfinitePlace.not_isReal_iff_isComplex.mpr (NumberField.IsTotallyComplex.isComplex v)) ?_
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext c
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.mpr (h c)

/- English proof (translation)
Establish `hs : ∀ z, majAt b X v (g z) (g z) = majAt b X v z z` using `fun z => by`. Rewrite using `[majAt_self', majAt_self', hg]`. Establish `key : ∀ c : K, v.embedding c * majAt b X v (g x) (g y) + star (v.embedding c) * star (majAt b X v (g x) (g y)) = v.embedding c * majAt b X v x y + star (v.embedding c) * star (majAt b X v x y)`. Introduce `c`. Establish `h1` using `majAt_expand' b X v c (g x) (g y)`.

Establish `h2` using `majAt_expand' b X v c x y`. Establish `e1 : g x + c • g y = g (x + c • y)` using `by simp`. Rewrite `h1` using `[e1, hs (x + c • y), h2, hs x, hs y]`. Take the linear combination `-h1`. Take `⟨c0, hc0⟩` from `exists_nonreal (v := v)`.

Establish `k1` using `key 1`. Establish `k2` using `key c0`. Simplify using `only [map_one, star_one, one_mul] at k1`. Generalize the expression as in `majAt b X v (g x) (g y) = a at k1 k2 ⊢`. Generalize the expression as in `majAt b X v x y = a0 at k1 k2 ⊢`.

Generalize the expression as in `v.embedding c0 = z at k2 hc0`. Establish `r1` using `congrArg Complex.re k1`. Simplify using `only [Complex.add_re, Complex.star_def, Complex.conj_re] at r1`. Establish `h1 : a.re = a0.re` using `by linarith`. Establish `r2` using `congrArg Complex.re k2`.

Simplify using `only [Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im] at r2`. Establish `e2 : z.re * a.re = z.re * a0.re` using `by rw [h1]`. Establish `h3 : z.im * (a.im - a0.im) = 0` using `by linarith`. Use `Complex.ext h1 ?_` and prove the remaining obligations. Break down `mul_eq_zero.mp h3 with h | h` into its components or cases.

Conclude with `absurd h hc0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem majAt_inv' [NumberField.IsTotallyComplex K] (g : V →ₗ[K] V)
    (hg : ∀ x, normAt b X v (g x) = normAt b X v x) (x y : V) :
    majAt b X v (g x) (g y) = majAt b X v x y := by
  have hs : ∀ z, majAt b X v (g z) (g z) = majAt b X v z z := fun z => by
    rw [majAt_self', majAt_self', hg]
  have key : ∀ c : K, v.embedding c * majAt b X v (g x) (g y) +
      star (v.embedding c) * star (majAt b X v (g x) (g y)) =
      v.embedding c * majAt b X v x y + star (v.embedding c) * star (majAt b X v x y) := by
    intro c
    have h1 := majAt_expand' b X v c (g x) (g y)
    have h2 := majAt_expand' b X v c x y
    have e1 : g x + c • g y = g (x + c • y) := by simp
    rw [e1, hs (x + c • y), h2, hs x, hs y] at h1
    linear_combination -h1
  obtain ⟨c0, hc0⟩ := exists_nonreal (v := v)
  have k1 := key 1
  have k2 := key c0
  simp only [map_one, star_one, one_mul] at k1
  generalize majAt b X v (g x) (g y) = a at k1 k2 ⊢
  generalize majAt b X v x y = a0 at k1 k2 ⊢
  generalize v.embedding c0 = z at k2 hc0
  have r1 := congrArg Complex.re k1
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re] at r1
  have h1 : a.re = a0.re := by linarith
  have r2 := congrArg Complex.re k2
  simp only [Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im] at r2
  have e2 : z.re * a.re = z.re * a0.re := by rw [h1]
  have h3 : z.im * (a.im - a0.im) = 0 := by linarith
  refine Complex.ext h1 ?_
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h hc0
  · linarith

/- English proof (translation)
Establish `hρ' : ∀ g, majAt b X v (ρ g x) y = majAt b X v x (ρ g⁻¹ y)` using `fun g => by`. Establish `e : ρ g (ρ g⁻¹ y) = y` using `by show (ρ g * ρ g⁻¹) y = y`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression. Establish `h` using `majAt_inv' b X v (ρ g) (hρ g) x (ρ g⁻¹ y)`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply]`. Rewrite using `[majAt_sum_left', majAt_sum_right']`. Simplify using `only [majAt_smul_left', majAt_smul_right', ha, hρ']`. Conclude with `Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)`.
-/
theorem majAt_selfadj' [NumberField.IsTotallyComplex K] {G : Type} [Group G] [Fintype G]
    (ρ : Representation K G V) (hρ : ∀ g x, normAt b X v (ρ g x) = normAt b X v x)
    (a : G → K) (ha : ∀ g, star (v.embedding (a g)) = v.embedding (a g⁻¹)) (x y : V) :
    majAt b X v ((∑ g, a g • ρ g) x) y = majAt b X v x ((∑ g, a g • ρ g) y) := by
  have hρ' : ∀ g, majAt b X v (ρ g x) y = majAt b X v x (ρ g⁻¹ y) := fun g => by
    have e : ρ g (ρ g⁻¹ y) = y := by
      show (ρ g * ρ g⁻¹) y = y
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    have h := majAt_inv' b X v (ρ g) (hρ g) x (ρ g⁻¹ y)
    rwa [e] at h
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [majAt_sum_left', majAt_sum_right']
  simp only [majAt_smul_left', majAt_smul_right', ha, hρ']
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)

end PI.Dv.GLP
