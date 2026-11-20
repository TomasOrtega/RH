import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open Matrix
open scoped ComplexOrder

namespace GramSchmidtFlag

variable {N : ℕ}

/- English proof (translation)
Unfold `gramOf`. Use `isHermitian_conjTranspose_mul_mul g ?_` and prove the remaining obligations. Conclude with `isHermitian_diagonal_of_self_adjoint _ (funext fun i => Complex.conj_ofReal _)`.
-/
theorem gramOf_isHermitian (d : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) :
    (gramOf d g).IsHermitian := by
  unfold gramOf
  refine isHermitian_conjTranspose_mul_mul g ?_
  exact isHermitian_diagonal_of_self_adjoint _ (funext fun i => Complex.conj_ofReal _)

/- English proof (translation)
Simplify using `[gramOf, conjTranspose_mul, Matrix.mul_assoc]`.
-/
theorem gramOf_mul (d : Fin N → ℝ) (g c : Matrix (Fin N) (Fin N) ℂ) :
    gramOf d (g * c) = cᴴ * gramOf d g * c := by
  simp [gramOf, conjTranspose_mul, Matrix.mul_assoc]

/- English proof (translation)
Unfold `gramOf`. Rewrite using `[star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]`. Conclude with `dotProduct_mulVec _ _ _`.
-/
theorem quad_gramOf (d : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) (y : Fin N → ℂ) :
    star y ⬝ᵥ (gramOf d g *ᵥ y) =
      star (g *ᵥ y) ⬝ᵥ (diagonal (fun i => (d i : ℂ)) *ᵥ (g *ᵥ y)) := by
  unfold gramOf
  rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  exact dotProduct_mulVec _ _ _

/- English proof (translation)
Simplify using `only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `[Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_diag_re (d : Fin N → ℝ) (z : Fin N → ℂ) :
    (star z ⬝ᵥ (diagonal (fun i => (d i : ℂ)) *ᵥ z)).re = ∑ a, d a * Complex.normSq (z a) := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Complex.normSq_apply]
  ring

/- English proof (translation)
Establish `: star (Pi.single k (1 : ℂ) : Fin N → ℂ) = Pi.single k 1`. Apply the tactic sequence `ext a; by_cases h : a = k <;> simp [Pi.single_apply, h]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem single_quad (B : Matrix (Fin N) (Fin N) ℂ) (k : Fin N) :
    star (Pi.single k (1 : ℂ) : Fin N → ℂ) ⬝ᵥ (B *ᵥ Pi.single k 1) = B k k := by
  have : star (Pi.single k (1 : ℂ) : Fin N → ℂ) = Pi.single k 1 := by
    ext a; by_cases h : a = k <;> simp [Pi.single_apply, h]
  rw [this]
  simp

/- English proof (translation)
Rewrite using `[← Finset.sum_subtype (Finset.univ.filter p) (by simp) f]`. Use `(Finset.sum_filter_of_ne fun a _ ha => ?_).symm` and prove the remaining obligations. Assume the negation of the conclusion as `hp`. Conclude with `ha (h a hp)`.
-/
theorem sum_eq_sum_subtype (p : Fin N → Prop) [DecidablePred p] (f : Fin N → ℂ)
    (h : ∀ a, ¬ p a → f a = 0) : ∑ a, f a = ∑ a : {a // p a}, f a := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp) f]
  refine (Finset.sum_filter_of_ne fun a _ ha => ?_).symm
  by_contra hp
  exact ha (h a hp)

def elem (k : Fin N) (w : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) + (if a = k then w b else 0)

/- English proof (translation)
Simplify using `[Matrix.mul_apply, elem, mul_add, Finset.sum_add_distrib]`.
-/
theorem mul_elem_apply (k : Fin N) (w : Fin N → ℂ) (B : Matrix (Fin N) (Fin N) ℂ) (i m : Fin N) :
    (B * elem k w) i m = B i m + B i k * w m := by
  simp [Matrix.mul_apply, elem, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, conjTranspose_apply, elem, Matrix.of_apply, star_add, add_mul, Finset.sum_add_distrib]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]`.

Simplify using the standard rewrite rules.
-/
theorem elem_conj_mul_apply (k : Fin N) (w : Fin N → ℂ) (B : Matrix (Fin N) (Fin N) ℂ)
    (i m : Fin N) : ((elem k w)ᴴ * B) i m = B i m + star (w i) * B k m := by
  simp only [Matrix.mul_apply, conjTranspose_apply, elem, Matrix.of_apply, star_add, add_mul,
    Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
    simp
  · rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    simp

/- English proof (translation)
Rewrite using `[mul_elem_apply, elem_conj_mul_apply, elem_conj_mul_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem elem_conj_apply (A : Matrix (Fin N) (Fin N) ℂ) (k : Fin N) (w : Fin N → ℂ) (i m : Fin N) :
    ((elem k w)ᴴ * A * elem k w) i m =
      A i m + A i k * w m + star (w i) * A k m + star (w i) * A k k * w m := by
  rw [mul_elem_apply, elem_conj_mul_apply, elem_conj_mul_apply]
  ring

/- English proof (translation)
Take `⟨r, hrdef⟩ : ∃ r : ℝ, r = (A k k).re` from `⟨_, rfl⟩`. Rewrite `hr` using `[← hrdef]`. Establish `hAkk : A k k = (r : ℂ)` using `by rw [hrdef]; exact (hA.coe_re_apply_self k).symm`. Establish `hr0 : r ≠ 0`. Introduce `h`.

Simplify using `[h] at hr`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht0, htt⟩ : ∃ t : ℝ, t ≠ 0 ∧ t * t * (d k * r) = 1 := by`. Establish `h` using `Real.mul_self_sqrt hr.le`. Establish `h0 : Real.sqrt (d k * r) ≠ 0` using `(Real.sqrt_pos.2 hr).ne'`. Use `⟨(Real.sqrt (d k * r))⁻¹, inv_ne_zero h0, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `ht2 : t * t * r = d k`. Combine the equalities or inequalities in the displayed calculation. Set `w : Fin N → ℂ` to `fun m => if m = k then (t : ℂ) - 1 else if k < m then -(A k m) / (r : ℂ) else 0`. Establish `hwk : w k = (t : ℂ) - 1` using `by simp [w]`.

Establish `hwlt : ∀ m, m < k → w m = 0`. Introduce `m hm`. Simplify using `[w, hm.ne, not_lt.2 hm.le]`. Establish `hwgt : ∀ m, k < m → w m = -(A k m) / (r : ℂ)`. Introduce `m hm`.

Simplify using `[w, hm.ne', hm]`. Establish `htri : (elem k w).BlockTriangular id`. Introduce `a b hab`. Establish `hab' : b < a` using `hab`. Establish `hne : a ≠ b` using `hab'.ne'`.

Distinguish the cases in `hak : a = k`. Substitute `hak` using the available equality. Simplify using `[elem, hne, hwlt b hab']`. Simplify using `[elem, hne, hak]`. Use `⟨elem k w, htri, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[det_of_upperTriangular htri, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]`. Introduce `a _`. Distinguish the cases in `hak : a = k`. Substitute `hak` using the available equality. Simplify using `[elem, hwk, ht0]`.

Simplify using `[elem, hak]`. Introduce `i m hi`. Rewrite using `[elem_conj_apply]`. Break down `hi.lt_or_eq with hik | rfl` into its components or cases. Rewrite using `[hwlt i hik, hk i k hik, if_neg hik.ne, hk i m hik]`.

Simplify using the standard rewrite rules. Establish `hstar : star (w i) = (t : ℂ) - 1`. Rewrite using `[hwk]`. Simplify using the standard rewrite rules. Rewrite using `[hstar, hAkk]`.

Break down `lt_trichotomy m i with hm | rfl | hm` into its components or cases. Establish `h1 : A i m = 0`. Use `hA.apply m i` as an intermediate fact. Rewrite `this` using `[hk m i hm, if_neg hm.ne]`. Conclude with `star_eq_zero.1 this`.

Rewrite using `[h1, hwlt m hm, if_neg hm.ne']`. Simplify using the standard rewrite rules. Rewrite using `[hwk, if_pos rfl, hAkk]`. Establish `: ((t * t * r : ℝ) : ℂ) = (d m : ℂ)` using `by rw [ht2]`. Move the coercions through the operations in `at this`.

Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hwgt m hm, if_neg hm.ne]`. Establish `hrc : (r : ℂ) ≠ 0` using `by exact_mod_cast hr0`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem step (d : Fin N → ℝ) (hd : ∀ i, d i * d i = 1) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : A.IsHermitian) (k : Fin N)
    (hk : ∀ i m, i < k → A i m = if i = m then (d i : ℂ) else 0)
    (hr : 0 < d k * (A k k).re) :
    ∃ E : Matrix (Fin N) (Fin N) ℂ, E.BlockTriangular id ∧ IsUnit E.det ∧
      ∀ i m, i ≤ k → (Eᴴ * A * E) i m = if i = m then (d i : ℂ) else 0 := by
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = (A k k).re := ⟨_, rfl⟩
  rw [← hrdef] at hr
  have hAkk : A k k = (r : ℂ) := by rw [hrdef]; exact (hA.coe_re_apply_self k).symm
  have hr0 : r ≠ 0 := by
    intro h; simp [h] at hr
  obtain ⟨t, ht0, htt⟩ : ∃ t : ℝ, t ≠ 0 ∧ t * t * (d k * r) = 1 := by
    have h := Real.mul_self_sqrt hr.le
    have h0 : Real.sqrt (d k * r) ≠ 0 := (Real.sqrt_pos.2 hr).ne'
    refine ⟨(Real.sqrt (d k * r))⁻¹, inv_ne_zero h0, ?_⟩
    calc _ = (Real.sqrt (d k * r))⁻¹ * (Real.sqrt (d k * r))⁻¹ *
          (Real.sqrt (d k * r) * Real.sqrt (d k * r)) := by rw [h]
      _ = 1 := by field_simp
  have ht2 : t * t * r = d k := by
    calc t * t * r = (t * t * (d k * r)) * d k * 1 - (t * t * r) * (d k * d k - 1) := by ring
      _ = d k := by rw [htt, hd k]; ring
  let w : Fin N → ℂ := fun m =>
    if m = k then (t : ℂ) - 1 else if k < m then -(A k m) / (r : ℂ) else 0
  have hwk : w k = (t : ℂ) - 1 := by simp [w]
  have hwlt : ∀ m, m < k → w m = 0 := by
    intro m hm
    simp [w, hm.ne, not_lt.2 hm.le]
  have hwgt : ∀ m, k < m → w m = -(A k m) / (r : ℂ) := by
    intro m hm
    simp [w, hm.ne', hm]
  have htri : (elem k w).BlockTriangular id := by
    intro a b hab
    have hab' : b < a := hab
    have hne : a ≠ b := hab'.ne'
    by_cases hak : a = k
    · subst hak
      simp [elem, hne, hwlt b hab']
    · simp [elem, hne, hak]
  refine ⟨elem k w, htri, ?_, ?_⟩
  · rw [det_of_upperTriangular htri, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro a _
    by_cases hak : a = k
    · subst hak
      simp [elem, hwk, ht0]
    · simp [elem, hak]
  · intro i m hi
    rw [elem_conj_apply]
    rcases hi.lt_or_eq with hik | rfl
    · rw [hwlt i hik, hk i k hik, if_neg hik.ne, hk i m hik]
      simp
    · have hstar : star (w i) = (t : ℂ) - 1 := by
        rw [hwk]; simp
      rw [hstar, hAkk]
      rcases lt_trichotomy m i with hm | rfl | hm
      · have h1 : A i m = 0 := by
          have := hA.apply m i
          rw [hk m i hm, if_neg hm.ne] at this
          exact star_eq_zero.1 this
        rw [h1, hwlt m hm, if_neg hm.ne']
        simp
      · rw [hwk, if_pos rfl, hAkk]
        have : ((t * t * r : ℝ) : ℂ) = (d m : ℂ) := by rw [ht2]
        push_cast at this
        rw [← this]
        ring
      · rw [hwgt m hm, if_neg hm.ne]
        have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
        field_simp
        ring

/- English proof (translation)
Set `x : {a : Fin N // (a : ℕ) < n} → ℂ` to `fun a => y a`. Establish `hx : x ≠ 0`. Introduce `h`. Apply `hy` to reduce the goal to its premises. Use extensionality with `a`.

Distinguish the cases in `ha : (a : ℕ) < n`. Conclude with `congrFun h ⟨a, ha⟩`. Conclude with `hs a (not_lt.1 ha)`. Establish `h1` using `hneg.dotProduct_mulVec_pos hx`. Establish `h3 : ∀ a : {a : Fin N // (a : ℕ) < n}, (gramHead d n g *ᵥ x) a = (gramOf d g *ᵥ y) a`.

Introduce `a`. Simplify using `only [mulVec, dotProduct]`. Rewrite using `[sum_eq_sum_subtype (fun b : Fin N => (b : ℕ) < n) (fun b => gramOf d g a b * y b) (fun b hb => by simp [hs b (not_lt.1 hb)])]`. Both sides reduce to the same expression. Establish `h2 : star x ⬝ᵥ (gramHead d n g *ᵥ x) = star y ⬝ᵥ (gramOf d g *ᵥ y)` using `by conv_rhs => rw [dotProduct]`.

Rewrite using `[sum_eq_sum_subtype (fun b : Fin N => (b : ℕ) < n) (fun b => (star y) b * (gramOf d g *ᵥ y) b) (fun b hb => by simp [hs b (not_lt.1 hb)])]`. Rewrite using `[dotProduct]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[h3]`. Both sides reduce to the same expression.

Rewrite `h1` using `[neg_mulVec, dotProduct_neg, h2]`. Use `(Complex.lt_def.1 h1).1` as an intermediate fact. Simplify using `using this`.
-/
theorem neg_quad (d : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) (n : ℕ)
    (hneg : (-gramHead d n g).PosDef) (y : Fin N → ℂ) (hy : y ≠ 0)
    (hs : ∀ a : Fin N, n ≤ (a : ℕ) → y a = 0) :
    (star y ⬝ᵥ (gramOf d g *ᵥ y)).re < 0 := by
  let x : {a : Fin N // (a : ℕ) < n} → ℂ := fun a => y a
  have hx : x ≠ 0 := by
    intro h
    apply hy
    ext a
    by_cases ha : (a : ℕ) < n
    · exact congrFun h ⟨a, ha⟩
    · exact hs a (not_lt.1 ha)
  have h1 := hneg.dotProduct_mulVec_pos hx
  have h3 : ∀ a : {a : Fin N // (a : ℕ) < n},
      (gramHead d n g *ᵥ x) a = (gramOf d g *ᵥ y) a := by
    intro a
    simp only [mulVec, dotProduct]
    rw [sum_eq_sum_subtype (fun b : Fin N => (b : ℕ) < n) (fun b => gramOf d g a b * y b)
      (fun b hb => by simp [hs b (not_lt.1 hb)])]
    rfl
  have h2 : star x ⬝ᵥ (gramHead d n g *ᵥ x) = star y ⬝ᵥ (gramOf d g *ᵥ y) := by
    conv_rhs => rw [dotProduct]
    rw [sum_eq_sum_subtype (fun b : Fin N => (b : ℕ) < n)
      (fun b => (star y) b * (gramOf d g *ᵥ y) b)
      (fun b hb => by simp [hs b (not_lt.1 hb)])]
    rw [dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [h3]
    rfl
  rw [neg_mulVec, dotProduct_neg, h2] at h1
  have := (Complex.lt_def.1 h1).1
  simpa using this

/- English proof (translation)
Establish `hy : c *ᵥ (Pi.single k 1 : Fin N → ℂ) ≠ 0`. Introduce `h`. Establish `h1 : c⁻¹ *ᵥ (c *ᵥ (Pi.single k 1 : Fin N → ℂ)) = Pi.single k 1`. Rewrite using `[mulVec_mulVec, nonsing_inv_mul c hcu, one_mulVec]`. Rewrite `h1` using `[h, mulVec_zero]`.

Use `congrFun h1 k` as an intermediate fact. Simplify using `at this`. Establish `hs : ∀ a : Fin N, n ≤ (a : ℕ) → (c *ᵥ (Pi.single k 1 : Fin N → ℂ)) a = 0`. Introduce `a ha`. Establish `hka : k < a` using `Fin.lt_def.2 (by omega)`.

Use `hc (i := a) (j := k) hka` as an intermediate fact. Simplify using `using this`. Establish `h` using `neg_quad d g n hneg _ hy hs`. Establish `e1` using `single_quad (gramOf d (g * c)) k`. Rewrite `e1` using `[quad_gramOf]`.

Establish `e2` using `quad_gramOf d g (c *ᵥ (Pi.single k 1 : Fin N → ℂ))`. Establish `e3 : g *ᵥ (c *ᵥ (Pi.single k 1 : Fin N → ℂ)) = (g * c) *ᵥ Pi.single k 1` using `mulVec_mulVec _ _ _`. Rewrite `e2` using `[e3, e1]`. Rewrite `h` using `[e2]`. Then use the resulting hypothesis.
-/
theorem pivot_neg (d : Fin N → ℝ) (g c : Matrix (Fin N) (Fin N) ℂ) (n : ℕ)
    (hneg : (-gramHead d n g).PosDef) (hc : c.BlockTriangular id) (hcu : IsUnit c.det)
    (k : Fin N) (hk : (k : ℕ) < n) : (gramOf d (g * c) k k).re < 0 := by
  have hy : c *ᵥ (Pi.single k 1 : Fin N → ℂ) ≠ 0 := by
    intro h
    have h1 : c⁻¹ *ᵥ (c *ᵥ (Pi.single k 1 : Fin N → ℂ)) = Pi.single k 1 := by
      rw [mulVec_mulVec, nonsing_inv_mul c hcu, one_mulVec]
    rw [h, mulVec_zero] at h1
    have := congrFun h1 k
    simp at this
  have hs : ∀ a : Fin N, n ≤ (a : ℕ) → (c *ᵥ (Pi.single k 1 : Fin N → ℂ)) a = 0 := by
    intro a ha
    have hka : k < a := Fin.lt_def.2 (by omega)
    have := hc (i := a) (j := k) hka
    simpa using this
  have h := neg_quad d g n hneg _ hy hs
  have e1 := single_quad (gramOf d (g * c)) k
  rw [quad_gramOf] at e1
  have e2 := quad_gramOf d g (c *ᵥ (Pi.single k 1 : Fin N → ℂ))
  have e3 : g *ᵥ (c *ᵥ (Pi.single k 1 : Fin N → ℂ)) = (g * c) *ᵥ Pi.single k 1 :=
    mulVec_mulVec _ _ _
  rw [e3, e1] at e2
  rwa [e2] at h

/- English proof (translation)
Simplify using `[Complex.normSq_apply, Complex.mul_re, Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem star_mul_real_re (r : ℝ) (z : ℂ) : (star z * ((r : ℂ) * z)).re = r * Complex.normSq z := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/- English proof (translation)
Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Establish `hdneg : ∀ a : Fin N, (a : ℕ) < N - j → sigForm N j a = -1` using `fun a ha => by`. Simplify using `[sigForm, ha]`. Establish `hdpos : ∀ a : Fin N, N - j ≤ (a : ℕ) → sigForm N j a = 1` using `fun a ha => by`.

Simplify using `[sigForm, not_lt.2 ha]`. Establish `hAH` using `gramOf_isHermitian (sigForm N j) h`. Set `M : Matrix {a : Fin N // (a : ℕ) < N - j} {a : Fin N // (a : ℕ) < N - j ∨ a = k} ℂ` to `h.submatrix Subtype.val Subtype.val`. Establish `hcard : Fintype.card {a : Fin N // (a : ℕ) < N - j} < Fintype.card {a : Fin N // (a : ℕ) < N - j ∨ a = k}`. Use `Fintype.card_lt_of_injective_of_notMem (fun a => (⟨a.1, Or.inl a.2⟩ : {a : Fin N // (a : ℕ) < N - j ∨ a = k})) ?_ (b := ⟨k, Or.inr rfl⟩) ?_` and prove the remaining obligations.

Introduce `a b hab`. Conclude with `Subtype.ext (congrArg (fun s => s.1) hab)`. Introduce and unpack `⟨a, ha⟩`. Establish `: (a.1 : Fin N) = k` using `congrArg (fun s => s.1) ha`. Establish `h2` using `a.2`.

Rewrite `h2` using `[this]`. Use linear arithmetic over natural numbers and integers. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := M.mulVecLin) (by simpa using hcard))`. Establish `hMx : M *ᵥ x = 0` using `by simpa using hx`. Set `y : Fin N → ℂ` to `fun a => if ha : (a : ℕ) < N - j ∨ a = k then x ⟨a, ha⟩ else 0`.

Establish `hyx : ∀ s : {a : Fin N // (a : ℕ) < N - j ∨ a = k}, y s = x s`. Introduce `s`. Simplify using `only [y, dif_pos s.2]`. Establish `hyS : ∀ a : Fin N, ¬ ((a : ℕ) < N - j ∨ a = k) → y a = 0`. Introduce `a ha`.

Simplify using `only [y, dif_neg ha]`. Establish `hy0 : y ≠ 0`. Introduce `h0`. Apply `hx0` to reduce the goal to its premises. Use extensionality with `s`.

Rewrite using `[← hyx s, h0]`. Both sides reduce to the same expression. Establish `hz : ∀ a : Fin N, (a : ℕ) < N - j → (h *ᵥ y) a = 0`. Introduce `a ha`. Establish `h1` using `congrFun hMx ⟨a, ha⟩`.

Simplify using `only [mulVec, dotProduct]`. Rewrite using `[sum_eq_sum_subtype (fun b : Fin N => (b : ℕ) < N - j ∨ b = k) (fun b => h a b * y b) (fun b hb => by simp [hyS b hb])]`. Simplify using `only [mulVec, dotProduct] at h1`. Rewrite using `[← show (0 : {a : Fin N // (a : ℕ) < N - j} → ℂ) ⟨a, ha⟩ = 0 from rfl, ← h1]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[hyx s]`. Both sides reduce to the same expression. Establish `hz0 : h *ᵥ y ≠ 0`. Introduce `h0`. Apply `hy0` to reduce the goal to its premises.

Establish `h1 : h⁻¹ *ᵥ (h *ᵥ y) = y`. Rewrite using `[mulVec_mulVec, nonsing_inv_mul h hu, one_mulVec]`. Rewrite using `[← h1, h0, mulVec_zero]`. Establish `hpos : 0 < (star y ⬝ᵥ (gramOf (sigForm N j) h *ᵥ y)).re`. Rewrite using `[quad_gramOf, quad_diag_re]`.

Take `⟨a, ha⟩` from `Function.ne_iff.1 hz0`. Establish `han : N - j ≤ (a : ℕ)`. Assume the negation of the conclusion as `hh`. Conclude with `ha (hz a (not_le.1 hh))`. Use `Finset.sum_pos' (fun b _ => ?_) ⟨a, Finset.mem_univ _, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hb : (b : ℕ) < N - j`. Simplify using `[hz b hb]`. Rewrite using `[hdpos b (not_lt.1 hb), one_mul]`. Conclude with `Complex.normSq_nonneg _`. Rewrite using `[hdpos a han, one_mul]`.

Conclude with `Complex.normSq_pos.2 ha`. Establish `hnonpos : (star y ⬝ᵥ (gramOf (sigForm N j) h *ᵥ y)).re ≤ 0`. Simplify using `only [dotProduct, Complex.re_sum]`. Use `Finset.sum_nonpos fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `ha : (a : ℕ) < N - j`.

Establish `h1 : (gramOf (sigForm N j) h *ᵥ y) a = ((-1 : ℝ) : ℂ) * y a`. Simplify using `only [mulVec, dotProduct, hA a _ ha, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hdneg a ha]`. Rewrite using `[h1, Pi.star_apply, star_mul_real_re]`. Use `Complex.normSq_nonneg (y a)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Distinguish the cases in `hak : a = k`. Rewrite using `[hak]`. Establish `h1 : (gramOf (sigForm N j) h *ᵥ y) k = gramOf (sigForm N j) h k k * y k`. Simplify using `only [mulVec, dotProduct]`. Use `Finset.sum_eq_single k (fun b _ hb => ?_) (by simp)` and prove the remaining obligations.

Distinguish the cases in `hbn : (b : ℕ) < N - j`. Establish `h2` using `hAH.apply k b`. Rewrite `h2` using `[hA b k hbn, if_neg hb]`. Rewrite using `[← h2]`. Simplify using the standard rewrite rules.

Rewrite using `[hyS b (by tauto)]`. Simplify using the standard rewrite rules. Establish `hre : gramOf (sigForm N j) h k k = (((gramOf (sigForm N j) h k k).re : ℝ) : ℂ)` using `(hAH.coe_re_apply_self k).symm`. Rewrite using `[h1, hre, Pi.star_apply, star_mul_real_re]`. Conclude with `mul_nonpos_of_nonpos_of_nonneg hle (Complex.normSq_nonneg _)`.

Establish `hya : y a = 0` using `hyS a (by tauto)`. Simplify using `[Pi.star_apply, hya]`. Conclude with `absurd hpos (not_lt.2 hnonpos)`.
-/
theorem pivot_pos (j : ℕ) (h : Matrix (Fin N) (Fin N) ℂ) (hu : IsUnit h.det) (k : Fin N)
    (hnk : N - j ≤ (k : ℕ))
    (hA : ∀ i m : Fin N, (i : ℕ) < N - j →
      gramOf (sigForm N j) h i m = if i = m then ((sigForm N j i : ℝ) : ℂ) else 0) :
    0 < (gramOf (sigForm N j) h k k).re := by
  by_contra hle
  push_neg at hle
  have hdneg : ∀ a : Fin N, (a : ℕ) < N - j → sigForm N j a = -1 := fun a ha => by
    simp [sigForm, ha]
  have hdpos : ∀ a : Fin N, N - j ≤ (a : ℕ) → sigForm N j a = 1 := fun a ha => by
    simp [sigForm, not_lt.2 ha]
  have hAH := gramOf_isHermitian (sigForm N j) h
  let M : Matrix {a : Fin N // (a : ℕ) < N - j} {a : Fin N // (a : ℕ) < N - j ∨ a = k} ℂ :=
    h.submatrix Subtype.val Subtype.val
  have hcard : Fintype.card {a : Fin N // (a : ℕ) < N - j} <
      Fintype.card {a : Fin N // (a : ℕ) < N - j ∨ a = k} := by
    refine Fintype.card_lt_of_injective_of_notMem
      (fun a => (⟨a.1, Or.inl a.2⟩ : {a : Fin N // (a : ℕ) < N - j ∨ a = k})) ?_
      (b := ⟨k, Or.inr rfl⟩) ?_
    · intro a b hab
      exact Subtype.ext (congrArg (fun s => s.1) hab)
    · rintro ⟨a, ha⟩
      have : (a.1 : Fin N) = k := congrArg (fun s => s.1) ha
      have h2 := a.2
      rw [this] at h2
      omega
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1
    (LinearMap.ker_ne_bot_of_finrank_lt (f := M.mulVecLin) (by simpa using hcard))
  have hMx : M *ᵥ x = 0 := by simpa using hx
  let y : Fin N → ℂ := fun a => if ha : (a : ℕ) < N - j ∨ a = k then x ⟨a, ha⟩ else 0
  have hyx : ∀ s : {a : Fin N // (a : ℕ) < N - j ∨ a = k}, y s = x s := by
    intro s
    simp only [y, dif_pos s.2]
  have hyS : ∀ a : Fin N, ¬ ((a : ℕ) < N - j ∨ a = k) → y a = 0 := by
    intro a ha
    simp only [y, dif_neg ha]
  have hy0 : y ≠ 0 := by
    intro h0
    apply hx0
    ext s
    rw [← hyx s, h0]
    rfl
  have hz : ∀ a : Fin N, (a : ℕ) < N - j → (h *ᵥ y) a = 0 := by
    intro a ha
    have h1 := congrFun hMx ⟨a, ha⟩
    simp only [mulVec, dotProduct]
    rw [sum_eq_sum_subtype (fun b : Fin N => (b : ℕ) < N - j ∨ b = k) (fun b => h a b * y b)
      (fun b hb => by simp [hyS b hb])]
    simp only [mulVec, dotProduct] at h1
    rw [← show (0 : {a : Fin N // (a : ℕ) < N - j} → ℂ) ⟨a, ha⟩ = 0 from rfl, ← h1]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hyx s]
    rfl
  have hz0 : h *ᵥ y ≠ 0 := by
    intro h0
    apply hy0
    have h1 : h⁻¹ *ᵥ (h *ᵥ y) = y := by
      rw [mulVec_mulVec, nonsing_inv_mul h hu, one_mulVec]
    rw [← h1, h0, mulVec_zero]
  have hpos : 0 < (star y ⬝ᵥ (gramOf (sigForm N j) h *ᵥ y)).re := by
    rw [quad_gramOf, quad_diag_re]
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hz0
    have han : N - j ≤ (a : ℕ) := by
      by_contra hh
      exact ha (hz a (not_le.1 hh))
    refine Finset.sum_pos' (fun b _ => ?_) ⟨a, Finset.mem_univ _, ?_⟩
    · by_cases hb : (b : ℕ) < N - j
      · simp [hz b hb]
      · rw [hdpos b (not_lt.1 hb), one_mul]
        exact Complex.normSq_nonneg _
    · rw [hdpos a han, one_mul]
      exact Complex.normSq_pos.2 ha
  have hnonpos : (star y ⬝ᵥ (gramOf (sigForm N j) h *ᵥ y)).re ≤ 0 := by
    simp only [dotProduct, Complex.re_sum]
    refine Finset.sum_nonpos fun a _ => ?_
    by_cases ha : (a : ℕ) < N - j
    · have h1 : (gramOf (sigForm N j) h *ᵥ y) a = ((-1 : ℝ) : ℂ) * y a := by
        simp only [mulVec, dotProduct, hA a _ ha, ite_mul, zero_mul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true, hdneg a ha]
      rw [h1, Pi.star_apply, star_mul_real_re]
      have := Complex.normSq_nonneg (y a)
      linarith
    · by_cases hak : a = k
      · rw [hak]
        have h1 : (gramOf (sigForm N j) h *ᵥ y) k = gramOf (sigForm N j) h k k * y k := by
          simp only [mulVec, dotProduct]
          refine Finset.sum_eq_single k (fun b _ hb => ?_) (by simp)
          by_cases hbn : (b : ℕ) < N - j
          · have h2 := hAH.apply k b
            rw [hA b k hbn, if_neg hb] at h2
            rw [← h2]
            simp
          · rw [hyS b (by tauto)]
            simp
        have hre : gramOf (sigForm N j) h k k = (((gramOf (sigForm N j) h k k).re : ℝ) : ℂ) :=
          (hAH.coe_re_apply_self k).symm
        rw [h1, hre, Pi.star_apply, star_mul_real_re]
        exact mul_nonpos_of_nonpos_of_nonneg hle (Complex.normSq_nonneg _)
      · have hya : y a = 0 := hyS a (by tauto)
        simp [Pi.star_apply, hya]
  exact absurd hpos (not_lt.2 hnonpos)

/- English proof (translation)
Unfold `sigForm`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem sigForm_mul_self (N j : ℕ) (i : Fin N) : sigForm N j i * sigForm N j i = 1 := by
  unfold sigForm
  split_ifs <;> norm_num

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_`. Use `⟨1, fun a b hab => ?_, by simp, fun i m hi => absurd hi (by omega)⟩` and prove the remaining obligations.

Conclude with `one_apply_ne (show b < a from hab).ne'`. Consider the case `succ k ih`. Introduce `hk`. Take `⟨c, hc, hcu, hA⟩` from `ih (by omega)`. Establish `hhu : IsUnit (g * c).det`.

Rewrite using `[det_mul]`. Conclude with `hg.1.mul hcu`. Establish `hpiv : 0 < sigForm N j ⟨k, by omega⟩ * (gramOf (sigForm N j) (g * c) ⟨k, by omega⟩ ⟨k, by omega⟩).re`. Distinguish the cases in `hkn : k < N - j`. Establish `h1` using `pivot_neg (sigForm N j) g c (N - j) hg.2 hc hcu ⟨k, by omega⟩ hkn`.

Establish `h2 : sigForm N j ⟨k, by omega⟩ = -1` using `by simp [sigForm, hkn]`. Rewrite using `[h2]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `pivot_pos j (g * c) hhu ⟨k, by omega⟩ (not_lt.1 hkn) (fun i m hi => hA i m (by omega))`. Establish `h2 : sigForm N j ⟨k, by omega⟩ = 1` using `by simp [sigForm, hkn]`.

Rewrite using `[h2]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨E, hE, hEu, hEA⟩` from `step (sigForm N j) (sigForm_mul_self N j) (gramOf (sigForm N j) (g * c)) (gramOf_isHermitian _ _) ⟨k, by omega⟩ (fun i m hi => hA i m hi) hpiv`. Use `⟨c * E, hc.mul hE, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[det_mul]`.

Conclude with `hcu.mul hEu`. Introduce `i m hi`. Rewrite using `[← Matrix.mul_assoc, gramOf_mul]`. Conclude with `hEA i m (Fin.le_def.2 (by simp; omega))`.
-/
theorem exists_col_ops (N j : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) (hg : InFlagDomain N j g) :
    ∀ k, k ≤ N → ∃ c : Matrix (Fin N) (Fin N) ℂ, c.BlockTriangular id ∧ IsUnit c.det ∧
      ∀ i m : Fin N, (i : ℕ) < k →
        gramOf (sigForm N j) (g * c) i m = if i = m then ((sigForm N j i : ℝ) : ℂ) else 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨1, fun a b hab => ?_, by simp, fun i m hi => absurd hi (by omega)⟩
    exact one_apply_ne (show b < a from hab).ne'
  | succ k ih =>
    intro hk
    obtain ⟨c, hc, hcu, hA⟩ := ih (by omega)
    have hhu : IsUnit (g * c).det := by
      rw [det_mul]
      exact hg.1.mul hcu
    have hpiv : 0 < sigForm N j ⟨k, by omega⟩ *
        (gramOf (sigForm N j) (g * c) ⟨k, by omega⟩ ⟨k, by omega⟩).re := by
      by_cases hkn : k < N - j
      · have h1 := pivot_neg (sigForm N j) g c (N - j) hg.2 hc hcu ⟨k, by omega⟩ hkn
        have h2 : sigForm N j ⟨k, by omega⟩ = -1 := by simp [sigForm, hkn]
        rw [h2]
        linarith
      · have h1 := pivot_pos j (g * c) hhu ⟨k, by omega⟩ (not_lt.1 hkn)
          (fun i m hi => hA i m (by omega))
        have h2 : sigForm N j ⟨k, by omega⟩ = 1 := by simp [sigForm, hkn]
        rw [h2]
        linarith
    obtain ⟨E, hE, hEu, hEA⟩ := step (sigForm N j) (sigForm_mul_self N j)
      (gramOf (sigForm N j) (g * c)) (gramOf_isHermitian _ _) ⟨k, by omega⟩
      (fun i m hi => hA i m hi) hpiv
    refine ⟨c * E, hc.mul hE, ?_, ?_⟩
    · rw [det_mul]
      exact hcu.mul hEu
    · intro i m hi
      rw [← Matrix.mul_assoc, gramOf_mul]
      exact hEA i m (Fin.le_def.2 (by simp; omega))

end GramSchmidtFlag

/- English proof (translation)
Introduce `N j _ g hg`. Take `⟨c, hc, hcu, hA⟩` from `GramSchmidtFlag.exists_col_ops N j g hg N le_rfl`. Establish `hvu : IsUnit (g * c).det`. Rewrite using `[det_mul]`. Conclude with `hg.1.mul hcu`.

Establish `hv : gramOf (sigForm N j) (g * c) = diagonal (fun i => ((sigForm N j i : ℝ) : ℂ))`. Use extensionality with `i m`. Rewrite using `[hA i m i.2, diagonal_apply]`. Use `⟨(g * c)⁻¹, c⁻¹, ?_, ?_, isUnit_nonsing_inv_det c hcu, ?_⟩` and prove the remaining obligations. Establish `h1` using `GramSchmidtFlag.gramOf_mul (sigForm N j) (g * c) (g * c)⁻¹`.

Rewrite `h1` using `[mul_nonsing_inv _ hvu, hv]`. Establish `h2 : gramOf (sigForm N j) (1 : Matrix (Fin N) (Fin N) ℂ) = diagonal (fun i => ((sigForm N j i : ℝ) : ℂ))`. Simplify using `[gramOf]`. Rewrite `h1` using `[h2]`. Conclude with `h1.symm`.

Use `haveI := invertibleOfIsUnitDet c hcu`. Conclude with `blockTriangular_inv_of_blockTriangular hc`. Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul g hg.1, Matrix.mul_one]`.
-/
theorem exists_unitary_translate_flag :
    ∀ (N j : ℕ), j ≤ N → ∀ g : Matrix (Fin N) (Fin N) ℂ, InFlagDomain N j g →
      ∃ u b : Matrix (Fin N) (Fin N) ℂ,
        gramOf (sigForm N j) u = diagonal (fun i => ((sigForm N j i : ℝ) : ℂ)) ∧
        b.BlockTriangular id ∧ IsUnit b.det ∧ u * g = b := by
  intro N j _ g hg
  obtain ⟨c, hc, hcu, hA⟩ := GramSchmidtFlag.exists_col_ops N j g hg N le_rfl
  have hvu : IsUnit (g * c).det := by
    rw [det_mul]
    exact hg.1.mul hcu
  have hv : gramOf (sigForm N j) (g * c) = diagonal (fun i => ((sigForm N j i : ℝ) : ℂ)) := by
    ext i m
    rw [hA i m i.2, diagonal_apply]
  refine ⟨(g * c)⁻¹, c⁻¹, ?_, ?_, isUnit_nonsing_inv_det c hcu, ?_⟩
  · have h1 := GramSchmidtFlag.gramOf_mul (sigForm N j) (g * c) (g * c)⁻¹
    rw [mul_nonsing_inv _ hvu, hv] at h1
    have h2 : gramOf (sigForm N j) (1 : Matrix (Fin N) (Fin N) ℂ) =
        diagonal (fun i => ((sigForm N j i : ℝ) : ℂ)) := by
      simp [gramOf]
    rw [h2] at h1
    exact h1.symm
  · haveI := invertibleOfIsUnitDet c hcu
    exact blockTriangular_inv_of_blockTriangular hc
  · rw [Matrix.mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul g hg.1, Matrix.mul_one]

end GlobalTheory.CompanionTheory.Ar.PB
