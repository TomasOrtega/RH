import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.I

open scoped ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Unfold `dDot`. Simplify using `only [d_mul n z f g hf hg, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]`. Apply the tactic sequence `congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem evl_dDot_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ)
    (hf : Ck n z 1 f) (hg : Ck n z 1 g) (x : M) (ξ : Fin n → ℂ) :
    dDot n z (fun y => f y * g y) x ξ = dDot n z f x ξ * g x + f x * dDot n z g x ξ := by
  unfold dDot
  simp only [d_mul n z f g hf hg, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Unfold `dDot`. Simplify using `only [d_const_mul n z c f hf, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem evl_dDot_const_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℂ)
    (f : M → ℂ) (hf : Ck n z 1 f) (x : M) (ξ : Fin n → ℂ) :
    dDot n z (fun y => c * f y) x ξ = c * dDot n z f x ξ := by
  unfold dDot
  simp only [d_const_mul n z c f hf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `hf1 : Ck n z 1 (fun y => (f y : ℂ))` using `Ck.mono n z 1 2 (by norm_num) _ hf`. Establish `hg1 : Ck n z 1 (fun y => (g y : ℂ))` using `Ck.mono n z 1 2 (by norm_num) _ hg`. Establish `h1 : ∀ k, db n z k (fun y => ((f y * g y : ℝ) : ℂ)) = fun y => db n z k (fun y => (f y : ℂ)) y * (g y : ℂ) + (f y : ℂ) * db n z k (fun y => (g y : ℂ)) y`. Introduce `k`. Use function extensionality and compare the values at `y`.

Use `db_mul n z _ _ hf1 hg1 k y` as an intermediate fact. Simplify `this` using `only [Complex.ofReal_mul]`. Establish `h2 : ∀ j k, d n z j (db n z k (fun y => ((f y * g y : ℝ) : ℂ))) x = d n z j (db n z k (fun y => (f y : ℂ))) x * (g x : ℂ) + conj (d n z k (fun y => (f y : ℂ)) x) * d n z j (fun y => (g y : ℂ)) x + d n z j (fun y => (f y : ℂ)) x * conj (d n z k (fun y => (g y : ℂ)) x) + (f x : ℂ) …`. Introduce `j k`. Establish `hdbf : Ck n z 1 (db n z k (fun y => (f y : ℂ)))` using `Ck.db n z 1 k _ hf`.

Establish `hdbg : Ck n z 1 (db n z k (fun y => (g y : ℂ)))` using `Ck.db n z 1 k _ hg`. Establish `hp1` using `Ck.mul n z 1 _ _ hdbf hg1`. Establish `hp2` using `Ck.mul n z 1 _ _ hf1 hdbg`. Rewrite using `[h1 k, d_add n z _ _ hp1 hp2 j x, d_mul n z _ _ hdbf hg1 j x, d_mul n z _ _ hf1 hdbg j x, db_ofReal n z f k x, db_ofReal n z g k x]`. Expand and normalize the polynomial expressions, which then agree.

Establish `c1 : conj (dDot n z (fun y => (f y : ℂ)) x ξ) * dDot n z (fun y => (g y : ℂ)) x ξ = ∑ j, ∑ k, conj (d n z k (fun y => (f y : ℂ)) x) * d n z j (fun y => (g y : ℂ)) x * ξ j * conj (ξ k)`. Unfold `dDot`. Rewrite using `[map_sum, Finset.sum_mul_sum, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `c2 : dDot n z (fun y => (f y : ℂ)) x ξ * conj (dDot n z (fun y => (g y : ℂ)) x ξ) = ∑ j, ∑ k, d n z j (fun y => (f y : ℂ)) x * conj (d n z k (fun y => (g y : ℂ)) x) * ξ j * conj (ξ k)`. Unfold `dDot`. Rewrite using `[map_sum, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[c1, c2]`. Unfold `Levi`. Simplify using `only [h2, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evl_levi_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℝ)
    (hf : CkR n z 2 f) (hg : CkR n z 2 g) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => f y * g y) x ξ =
      Levi n z f x ξ * (g x : ℂ) + (f x : ℂ) * Levi n z g x ξ +
        conj (dDot n z (fun y => (f y : ℂ)) x ξ) * dDot n z (fun y => (g y : ℂ)) x ξ +
        dDot n z (fun y => (f y : ℂ)) x ξ * conj (dDot n z (fun y => (g y : ℂ)) x ξ) := by
  have hf1 : Ck n z 1 (fun y => (f y : ℂ)) := Ck.mono n z 1 2 (by norm_num) _ hf
  have hg1 : Ck n z 1 (fun y => (g y : ℂ)) := Ck.mono n z 1 2 (by norm_num) _ hg
  have h1 : ∀ k, db n z k (fun y => ((f y * g y : ℝ) : ℂ)) =
      fun y => db n z k (fun y => (f y : ℂ)) y * (g y : ℂ) +
        (f y : ℂ) * db n z k (fun y => (g y : ℂ)) y := by
    intro k; funext y
    have := db_mul n z _ _ hf1 hg1 k y
    simpa only [Complex.ofReal_mul] using this
  have h2 : ∀ j k, d n z j (db n z k (fun y => ((f y * g y : ℝ) : ℂ))) x =
      d n z j (db n z k (fun y => (f y : ℂ))) x * (g x : ℂ)
      + conj (d n z k (fun y => (f y : ℂ)) x) * d n z j (fun y => (g y : ℂ)) x
      + d n z j (fun y => (f y : ℂ)) x * conj (d n z k (fun y => (g y : ℂ)) x)
      + (f x : ℂ) * d n z j (db n z k (fun y => (g y : ℂ))) x := by
    intro j k
    have hdbf : Ck n z 1 (db n z k (fun y => (f y : ℂ))) := Ck.db n z 1 k _ hf
    have hdbg : Ck n z 1 (db n z k (fun y => (g y : ℂ))) := Ck.db n z 1 k _ hg
    have hp1 := Ck.mul n z 1 _ _ hdbf hg1
    have hp2 := Ck.mul n z 1 _ _ hf1 hdbg
    rw [h1 k, d_add n z _ _ hp1 hp2 j x, d_mul n z _ _ hdbf hg1 j x, d_mul n z _ _ hf1 hdbg j x,
      db_ofReal n z f k x, db_ofReal n z g k x]
    ring
  have c1 : conj (dDot n z (fun y => (f y : ℂ)) x ξ) * dDot n z (fun y => (g y : ℂ)) x ξ =
      ∑ j, ∑ k, conj (d n z k (fun y => (f y : ℂ)) x) * d n z j (fun y => (g y : ℂ)) x *
        ξ j * conj (ξ k) := by
    unfold dDot
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul]; ring
  have c2 : dDot n z (fun y => (f y : ℂ)) x ξ * conj (dDot n z (fun y => (g y : ℂ)) x ξ) =
      ∑ j, ∑ k, d n z j (fun y => (f y : ℂ)) x * conj (d n z k (fun y => (g y : ℂ)) x) *
        ξ j * conj (ξ k) := by
    unfold dDot
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul]; ring
  rw [c1, c2]
  unfold Levi
  simp only [h2, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Establish `h : ∀ k, db n z k (fun _ => ((0 : ℝ) : ℂ)) = fun _ => (0 : ℂ)`. Introduce `k`. Use function extensionality and compare the values at `y`. Conclude with `db_const n z _ k y`. Unfold `Levi`.

Simplify using `only [h, d_const, zero_mul, Finset.sum_const_zero]`.
-/
theorem evl_levi_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (x : M)
    (ξ : Fin n → ℂ) : Levi n z (fun _ => (0 : ℝ)) x ξ = 0 := by
  have h : ∀ k, db n z k (fun _ => ((0 : ℝ) : ℂ)) = fun _ => (0 : ℂ) := by
    intro k; funext y; exact db_const n z _ k y
  unfold Levi
  simp only [h, d_const, zero_mul, Finset.sum_const_zero]

/- English proof (translation)
Unfold `dDot`. Simplify using `only [d_const, zero_mul, Finset.sum_const_zero]`.
-/
theorem evl_dDot_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (x : M)
    (ξ : Fin n → ℂ) : dDot n z (fun _ => (0 : ℂ)) x ξ = 0 := by
  unfold dDot
  simp only [d_const, zero_mul, Finset.sum_const_zero]

/- English proof (translation)
Unfold `dDot`. Simplify using `only [d_add n z f g hf hg, add_mul, Finset.sum_add_distrib]`.
-/
theorem evl_dDot_add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ)
    (hf : Ck n z 1 f) (hg : Ck n z 1 g) (x : M) (ξ : Fin n → ℂ) :
    dDot n z (fun y => f y + g y) x ξ = dDot n z f x ξ + dDot n z g x ξ := by
  unfold dDot
  simp only [d_add n z f g hf hg, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Establish `hs : Smooth n z g` using `Holo.smooth n z g hg`. Establish `h1 : Ck n z 1 g` using `Smooth.ck n z 1 g hs`. Establish `hsq : (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ)) = fun y => g y * conj (g y)`. Use function extensionality and compare the values at `y`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Rewrite using `[hsq, evl_dDot_mul n z _ _ h1 (Ck.conj n z 1 g h1)]`. Establish `h0 : dDot n z (fun y => conj (g y)) x ξ = 0`. Unfold `dDot`. Simplify using `only [d_conj, Holo.db_eq_zero n z g hg, map_zero, zero_mul, Finset.sum_const_zero]`. Rewrite using `[h0]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem evl_dDot_normSq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ)
    (hg : Holo n z g) (x : M) (ξ : Fin n → ℂ) :
    dDot n z (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ)) x ξ = conj (g x) * dDot n z g x ξ := by
  have hs : Smooth n z g := Holo.smooth n z g hg
  have h1 : Ck n z 1 g := Smooth.ck n z 1 g hs
  have hsq : (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ)) = fun y => g y * conj (g y) := by
    funext y; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hsq, evl_dDot_mul n z _ _ h1 (Ck.conj n z 1 g h1)]
  have h0 : dDot n z (fun y => conj (g y)) x ξ = 0 := by
    unfold dDot
    simp only [d_conj, Holo.db_eq_zero n z g hg, map_zero, zero_mul, Finset.sum_const_zero]
  rw [h0]; ring

/- English proof (translation)
The claim follows from `smoothR_sum n z s (fun i y => ‖g i y‖ ^ 2) fun i _ => Smooth.normSq n z _ (Holo.smooth n z _ (hg i))`.
-/
theorem evl_smoothR_sumSq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (g : ι → M → ℂ) (hg : ∀ i, Holo n z (g i)) :
    SmoothR n z (fun y => ∑ i ∈ s, ‖g i y‖ ^ 2) :=
  smoothR_sum n z s (fun i y => ‖g i y‖ ^ 2) fun i _ => Smooth.normSq n z _ (Holo.smooth n z _ (hg i))

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using evl_levi_zero n z x ξ`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`. Rewrite using `[levi_add n z (fun y => ‖g a y‖ ^ 2) (fun y => ∑ i ∈ s, ‖g i y‖ ^ 2) (SmoothR.ckR n z 2 _ (Smooth.normSq n z _ (Holo.smooth n z _ (hg a)))) (SmoothR.ckR n z 2 _ (evl_smoothR_sumSq n z s g hg)) x ξ, levi_normSq n z (g a) (hg a) x ξ, ih]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evl_levi_sumSq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (g : ι → M → ℂ) (hg : ∀ i, Holo n z (g i)) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => ∑ i ∈ s, ‖g i y‖ ^ 2) x ξ =
      ((∑ i ∈ s, ‖dDot n z (g i) x ξ‖ ^ 2 : ℝ) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evl_levi_zero n z x ξ
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [levi_add n z (fun y => ‖g a y‖ ^ 2) (fun y => ∑ i ∈ s, ‖g i y‖ ^ 2)
      (SmoothR.ckR n z 2 _ (Smooth.normSq n z _ (Holo.smooth n z _ (hg a))))
      (SmoothR.ckR n z 2 _ (evl_smoothR_sumSq n z s g hg)) x ξ,
      levi_normSq n z (g a) (hg a) x ξ, ih]
    push_cast; ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using evl_dDot_zero n z x ξ`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha, Complex.ofReal_add]`. Rewrite using `[evl_dDot_add n z _ _ (SmoothR.ckR n z 1 _ (Smooth.normSq n z _ (Holo.smooth n z _ (hg a)))) (SmoothR.ckR n z 1 _ (evl_smoothR_sumSq n z s g hg)) x ξ, evl_dDot_normSq n z (g a) (hg a) x ξ, ih]`.
-/
theorem evl_dDot_sumSq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (g : ι → M → ℂ) (hg : ∀ i, Holo n z (g i)) (x : M) (ξ : Fin n → ℂ) :
    dDot n z (fun y => ((∑ i ∈ s, ‖g i y‖ ^ 2 : ℝ) : ℂ)) x ξ =
      ∑ i ∈ s, conj (g i x) * dDot n z (g i) x ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evl_dDot_zero n z x ξ
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha, Complex.ofReal_add]
    rw [evl_dDot_add n z _ _ (SmoothR.ckR n z 1 _ (Smooth.normSq n z _ (Holo.smooth n z _ (hg a))))
      (SmoothR.ckR n z 1 _ (evl_smoothR_sumSq n z s g hg)) x ξ,
      evl_dDot_normSq n z (g a) (hg a) x ξ, ih]

/- English proof (translation)
Establish `h` using `(hasDerivAt_neg t).exp`. Rewrite using `[h.deriv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deriv_exp_neg (t : ℝ) : deriv (fun t => Real.exp (-t)) t = -Real.exp (-t) := by
  have h := (hasDerivAt_neg t).exp
  rw [h.deriv]; ring

/- English proof (translation)
Establish `h : HasDerivAt (fun t => -Real.exp (-t)) (-(Real.exp (-t) * -1)) t` using `(hasDerivAt_neg t).exp.neg`. Rewrite using `[h.deriv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deriv_neg_exp_neg (t : ℝ) : deriv (fun t => -Real.exp (-t)) t = Real.exp (-t) := by
  have h : HasDerivAt (fun t => -Real.exp (-t)) (-(Real.exp (-t) * -1)) t :=
    (hasDerivAt_neg t).exp.neg
  rw [h.deriv]; ring

/- English proof (translation)
The claim follows from `Real.contDiff_exp.comp contDiff_neg`.
-/
theorem contDiff_exp_neg : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (-t)) :=
  Real.contDiff_exp.comp contDiff_neg

/- English proof (translation)
The claim follows from `(Real.contDiff_exp.comp contDiff_neg).neg`.
-/
theorem contDiff_neg_exp_neg : ContDiff ℝ ∞ (fun t : ℝ => -Real.exp (-t)) :=
  (Real.contDiff_exp.comp contDiff_neg).neg

/- English proof (translation)
Establish `h : ∀ j, d n z j (fun y => ((Real.exp (-ph y) : ℝ) : ℂ)) x = -((Real.exp (-ph x) : ℝ) : ℂ) * d n z j (fun y => (ph y : ℂ)) x`. Introduce `j`. Use `d_comp_real n z (fun t => Real.exp (-t)) contDiff_exp_neg ph (SmoothR.ckR n z 1 ph hph) j x` as an intermediate fact. Rewrite `this` using `[deriv_exp_neg]`. Simplify using `using this`.

Unfold `dDot`. Simplify using `only [h, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem evl_dDot_expNeg {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ)
    (hph : SmoothR n z ph) (x : M) (ξ : Fin n → ℂ) :
    dDot n z (fun y => ((Real.exp (-ph y) : ℝ) : ℂ)) x ξ =
      -((Real.exp (-ph x) : ℝ) : ℂ) * dDot n z (fun y => (ph y : ℂ)) x ξ := by
  have h : ∀ j, d n z j (fun y => ((Real.exp (-ph y) : ℝ) : ℂ)) x =
      -((Real.exp (-ph x) : ℝ) : ℂ) * d n z j (fun y => (ph y : ℂ)) x := by
    intro j
    have := d_comp_real n z (fun t => Real.exp (-t)) contDiff_exp_neg ph (SmoothR.ckR n z 1 ph hph) j x
    rw [deriv_exp_neg] at this
    simpa using this
  unfold dDot
  simp only [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `hdb : ∀ k, db n z k (fun y => ((Real.exp (-ph y) : ℝ) : ℂ)) = fun y => ((-Real.exp (-ph y) : ℝ) : ℂ) * db n z k (fun y => (ph y : ℂ)) y`. Introduce `k`. Use function extensionality and compare the values at `y`. Use `db_comp_real n z (fun t => Real.exp (-t)) contDiff_exp_neg ph (SmoothR.ckR n z 1 ph hph) k y` as an intermediate fact. Rewrite `this` using `[deriv_exp_neg]`.

Simplify using `using this`. Establish `hf1 : Ck n z 1 (fun y => ((-Real.exp (-ph y) : ℝ) : ℂ))` using `SmoothR.ckR n z 1 _ (SmoothR.comp n z _ contDiff_neg_exp_neg ph hph)`. Establish `hd2 : ∀ j, d n z j (fun y => ((-Real.exp (-ph y) : ℝ) : ℂ)) x = ((Real.exp (-ph x) : ℝ) : ℂ) * d n z j (fun y => (ph y : ℂ)) x`. Introduce `j`. Use `d_comp_real n z (fun t => -Real.exp (-t)) contDiff_neg_exp_neg ph (SmoothR.ckR n z 1 ph hph) j x` as an intermediate fact.

Rewrite `this` using `[deriv_neg_exp_neg]`. Simplify using `using this`. Establish `h2 : ∀ j k, d n z j (db n z k (fun y => ((Real.exp (-ph y) : ℝ) : ℂ))) x = ((Real.exp (-ph x) : ℝ) : ℂ) * (d n z j (fun y => (ph y : ℂ)) x * conj (d n z k (fun y => (ph y : ℂ)) x) - d n z j (db n z k (fun y => (ph y : ℂ))) x)`. Introduce `j k`. Establish `hdbk : Ck n z 1 (db n z k (fun y => (ph y : ℂ)))` using `Ck.db n z 1 k _ (SmoothR.ckR n z 2 ph hph)`.

Rewrite using `[hdb k, d_mul n z _ _ hf1 hdbk j x, hd2 j, db_ofReal n z ph k x]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `c : dDot n z (fun y => (ph y : ℂ)) x ξ * conj (dDot n z (fun y => (ph y : ℂ)) x ξ) = ∑ j, ∑ k, d n z j (fun y => (ph y : ℂ)) x * conj (d n z k (fun y => (ph y : ℂ)) x) * ξ j * conj (ξ k)`. Unfold `dDot`.

Rewrite using `[map_sum, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[c]`.

Unfold `Levi`. Simplify using `only [h2, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evl_levi_expNeg {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ)
    (hph : SmoothR n z ph) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => Real.exp (-ph y)) x ξ =
      ((Real.exp (-ph x) : ℝ) : ℂ) * (dDot n z (fun y => (ph y : ℂ)) x ξ *
        conj (dDot n z (fun y => (ph y : ℂ)) x ξ) - Levi n z ph x ξ) := by
  have hdb : ∀ k, db n z k (fun y => ((Real.exp (-ph y) : ℝ) : ℂ)) =
      fun y => ((-Real.exp (-ph y) : ℝ) : ℂ) * db n z k (fun y => (ph y : ℂ)) y := by
    intro k; funext y
    have := db_comp_real n z (fun t => Real.exp (-t)) contDiff_exp_neg ph (SmoothR.ckR n z 1 ph hph) k y
    rw [deriv_exp_neg] at this
    simpa using this
  have hf1 : Ck n z 1 (fun y => ((-Real.exp (-ph y) : ℝ) : ℂ)) :=
    SmoothR.ckR n z 1 _ (SmoothR.comp n z _ contDiff_neg_exp_neg ph hph)
  have hd2 : ∀ j, d n z j (fun y => ((-Real.exp (-ph y) : ℝ) : ℂ)) x =
      ((Real.exp (-ph x) : ℝ) : ℂ) * d n z j (fun y => (ph y : ℂ)) x := by
    intro j
    have := d_comp_real n z (fun t => -Real.exp (-t)) contDiff_neg_exp_neg ph (SmoothR.ckR n z 1 ph hph) j x
    rw [deriv_neg_exp_neg] at this
    simpa using this
  have h2 : ∀ j k, d n z j (db n z k (fun y => ((Real.exp (-ph y) : ℝ) : ℂ))) x =
      ((Real.exp (-ph x) : ℝ) : ℂ) * (d n z j (fun y => (ph y : ℂ)) x *
        conj (d n z k (fun y => (ph y : ℂ)) x) - d n z j (db n z k (fun y => (ph y : ℂ))) x) := by
    intro j k
    have hdbk : Ck n z 1 (db n z k (fun y => (ph y : ℂ))) :=
      Ck.db n z 1 k _ (SmoothR.ckR n z 2 ph hph)
    rw [hdb k, d_mul n z _ _ hf1 hdbk j x, hd2 j, db_ofReal n z ph k x]
    push_cast; ring
  have c : dDot n z (fun y => (ph y : ℂ)) x ξ * conj (dDot n z (fun y => (ph y : ℂ)) x ξ) =
      ∑ j, ∑ k, d n z j (fun y => (ph y : ℂ)) x * conj (d n z k (fun y => (ph y : ℂ)) x) *
        ξ j * conj (ξ k) := by
    unfold dDot
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul]; ring
  rw [c]
  unfold Levi
  simp only [h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `h : c * (S * ee) * (c * (Q * ee + S * (ee * (b1 ^ 2 + b2 ^ 2 - l)) - 2 * ee * (p1 * b1 + p2 * b2)) + c * (S * ee) * l) - c ^ 2 * ee ^ 2 * ((p1 - S * b1) ^ 2 + (p2 - S * b2) ^ 2) = (c * ee) ^ 2 * (S * Q - (p1 ^ 2 + p2 ^ 2))` using `by ring`. Establish `: 0 ≤ (c * ee) ^ 2 * (S * Q - (p1 ^ 2 + p2 ^ 2))` using `mul_nonneg (sq_nonneg _) (sub_nonneg.2 hCS)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX : 0 ≤ Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2)`.

Break down `hS.eq_or_lt with h0 | hpos` into its components or cases. Substitute `h0` using the available equality. Establish `h1 : p1 = 0` using `by nlinarith [sq_nonneg p1, sq_nonneg p2]`. Establish `h2 : p2 = 0` using `by nlinarith [sq_nonneg p1, sq_nonneg p2]`. Substitute `h1` using the available equality.

Substitute `h2` using the available equality. Use the polynomial consequences of the given equalities and inequalities. Establish `hm : S * (Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2)) = (S * Q - (p1 ^ 2 + p2 ^ 2)) + ((p1 - S * b1) ^ 2 + (p2 - S * b2) ^ 2)` using `by ring`. Establish `h3 : 0 ≤ S * (Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2))`. Rewrite using `[hm]`.

Use polynomial arithmetic with `[sq_nonneg (p1 - S * b1), sq_nonneg (p2 - S * b2)]`. Conclude with `nonneg_of_mul_nonneg_right (by linarith [h3, mul_comm S (Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2))]) hpos`. Establish `h : c * (Q * ee + S * (ee * (b1 ^ 2 + b2 ^ 2 - l)) - 2 * ee * (p1 * b1 + p2 * b2)) + c * (S * ee) * l = (c * ee) * (Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2))`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]; exact mul_nonneg (by positivity) hX`.
-/
theorem evl_alg (c ee S Q p1 p2 b1 b2 l : ℝ) (hc : 0 < c) (hee : 0 < ee) (hS : 0 ≤ S)
    (hQ : 0 ≤ Q) (hCS : p1 ^ 2 + p2 ^ 2 ≤ S * Q) :
    c ^ 2 * ee ^ 2 * ((p1 - S * b1) ^ 2 + (p2 - S * b2) ^ 2) ≤
        c * (S * ee) * (c * (Q * ee + S * (ee * (b1 ^ 2 + b2 ^ 2 - l)) -
          2 * ee * (p1 * b1 + p2 * b2)) + c * (S * ee) * l) ∧
      0 ≤ c * (Q * ee + S * (ee * (b1 ^ 2 + b2 ^ 2 - l)) - 2 * ee * (p1 * b1 + p2 * b2)) +
        c * (S * ee) * l := by
  constructor
  · have h : c * (S * ee) * (c * (Q * ee + S * (ee * (b1 ^ 2 + b2 ^ 2 - l)) -
          2 * ee * (p1 * b1 + p2 * b2)) + c * (S * ee) * l) -
        c ^ 2 * ee ^ 2 * ((p1 - S * b1) ^ 2 + (p2 - S * b2) ^ 2) =
        (c * ee) ^ 2 * (S * Q - (p1 ^ 2 + p2 ^ 2)) := by ring
    have : 0 ≤ (c * ee) ^ 2 * (S * Q - (p1 ^ 2 + p2 ^ 2)) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.2 hCS)
    linarith
  · have hX : 0 ≤ Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2) := by
      rcases hS.eq_or_lt with h0 | hpos
      · subst h0
        have h1 : p1 = 0 := by nlinarith [sq_nonneg p1, sq_nonneg p2]
        have h2 : p2 = 0 := by nlinarith [sq_nonneg p1, sq_nonneg p2]
        subst h1; subst h2; nlinarith
      · have hm : S * (Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2)) =
            (S * Q - (p1 ^ 2 + p2 ^ 2)) + ((p1 - S * b1) ^ 2 + (p2 - S * b2) ^ 2) := by ring
        have h3 : 0 ≤ S * (Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2)) := by
          rw [hm]; nlinarith [sq_nonneg (p1 - S * b1), sq_nonneg (p2 - S * b2)]
        exact nonneg_of_mul_nonneg_right (by linarith [h3, mul_comm S (Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2))]) hpos
    have h : c * (Q * ee + S * (ee * (b1 ^ 2 + b2 ^ 2 - l)) - 2 * ee * (p1 * b1 + p2 * b2)) +
        c * (S * ee) * l = (c * ee) * (Q + S * (b1 ^ 2 + b2 ^ 2) - 2 * (p1 * b1 + p2 * b2)) := by
      ring
    rw [h]; exact mul_nonneg (by positivity) hX

/- English proof (translation)
Establish `h1 : ‖∑ i ∈ s, conj (u i) * a i‖ ≤ ∑ i ∈ s, ‖u i‖ * ‖a i‖`. Use `(norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_conj]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem evl_cs {ι : Type*} (s : Finset ι) (u a : ι → ℂ) :
    ‖∑ i ∈ s, conj (u i) * a i‖ ^ 2 ≤ (∑ i ∈ s, ‖u i‖ ^ 2) * ∑ i ∈ s, ‖a i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, conj (u i) * a i‖ ≤ ∑ i ∈ s, ‖u i‖ * ‖a i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_mul, Complex.norm_conj]
  calc ‖∑ i ∈ s, conj (u i) * a i‖ ^ 2 ≤ (∑ i ∈ s, ‖u i‖ * ‖a i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq s _ _

end

end ReciprocityTheory.L2DbarEstimates.I
