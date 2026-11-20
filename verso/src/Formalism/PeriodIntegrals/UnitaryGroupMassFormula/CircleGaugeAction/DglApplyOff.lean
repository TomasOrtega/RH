import Mathlib
import Formalism.PeriodIntegrals.ExistsGaugeMeasureForEachRank

noncomputable section

open Matrix

namespace PI.ExistsGaugeMeasureForEachRank.W

variable {r : ℕ}

def cI (r : ℕ) : Fin (2 * r + 0 + 1) := ⟨r, by omega⟩

def dgl (r : ℕ) (u : ℂ) : Mat 0 r := diagonal (fun i => if i = cI r then u else 1)

/- English proof (translation)
Unfold `dgl`. Rewrite using `[Matrix.diagonal_apply]`.
-/
lemma dgl_apply (u : ℂ) (i j : Fin (2 * r + 0 + 1)) :
    dgl r u i j = if i = j then (if i = cI r then u else 1) else 0 := by
  unfold dgl
  rw [Matrix.diagonal_apply]

/- English proof (translation)
Rewrite using `[dgl_apply, Matrix.one_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `hi : i ≠ cI r` using `fun hi => h ⟨hi, hi⟩`. Simplify using `[hi]`.

Simplify using `[hij]`.
-/
lemma dgl_apply_off (u : ℂ) (i j : Fin (2 * r + 0 + 1)) (h : ¬ (i = cI r ∧ j = cI r)) :
    dgl r u i j = (1 : Mat 0 r) i j := by
  rw [dgl_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    have hi : i ≠ cI r := fun hi => h ⟨hi, hi⟩
    simp [hi]
  · simp [hij]

/- English proof (translation)
Rewrite using `[Fin.ext_iff, Fin.ext_iff, Fin.val_rev]`. Simplify using `only [cI]`. Use `p.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma rev_eq_c_iff (p : Fin (2 * r + 0 + 1)) : Fin.rev p = cI r ↔ p = cI r := by
  rw [Fin.ext_iff, Fin.ext_iff, Fin.val_rev]
  simp only [cI]
  have := p.isLt
  omega

/- English proof (translation)
Establish `hp` using `p.isLt`. Establish `hq` using `q.isLt`. Simplify using `only [Hpk, Fin.ext_iff, Fin.val_rev, cI]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
lemma Hpk_apply (p q : Fin (2 * r + 0 + 1)) :
    Hpk 0 r p q = if q = Fin.rev p then (if p = cI r then -1 else 1) else 0 := by
  have hp := p.isLt
  have hq := q.isLt
  simp only [Hpk, Fin.ext_iff, Fin.val_rev, cI]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Use `⟨?_, fun a => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `show (dgl r u)ᴴ * Hpk 0 r * dgl r u = Hpk 0 r`. Use extensionality with `p q`. Simplify using `only [dgl, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply]`. Rewrite using `[Hpk_apply]`.

Distinguish the cases in `hq : q = Fin.rev p`. Substitute `hq` using the available equality. Distinguish the cases in `hp : p = cI r`. Substitute `hp` using the available equality. Establish `hc : Fin.rev (cI r) = cI r` using `(rev_eq_c_iff _).2 rfl`.

Simplify using `only [hc, if_true]`. Use `show star u * -1 * u = -1`. Rewrite using `[show star u = (starRingEnd ℂ) u from rfl]`. Take the linear combination `-hu`. Establish `hc : Fin.rev p ≠ cI r` using `fun h => hp ((rev_eq_c_iff p).1 h)`.

Simplify using `[hp, hc]`. Simplify using `[hq]`. Establish `hne : eI 0 r a ≠ cI r`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `[eI, cI] at this`. Use linear arithmetic over natural numbers and integers. Simplify using `only [bvec, dgl, Matrix.diagonal_mulVec_single, if_neg hne, one_mul]`. Establish `hne : esI 0 r a ≠ cI r`. Introduce `h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[esI, cI] at this`. Use linear arithmetic over natural numbers and integers. Simplify using `only [bvec, dgl, Matrix.diagonal_mulVec_single, if_neg hne, one_mul]`.
-/
lemma dgl_mem {u : ℂ} (hu : (starRingEnd ℂ) u * u = 1) : dgl r u ∈ UWb 0 r := by
  refine ⟨?_, fun a => ⟨?_, ?_⟩⟩
  · show (dgl r u)ᴴ * Hpk 0 r * dgl r u = Hpk 0 r
    ext p q
    simp only [dgl, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply]
    rw [Hpk_apply]
    by_cases hq : q = Fin.rev p
    · subst hq
      by_cases hp : p = cI r
      · subst hp
        have hc : Fin.rev (cI r) = cI r := (rev_eq_c_iff _).2 rfl
        simp only [hc, if_true]
        show star u * -1 * u = -1
        rw [show star u = (starRingEnd ℂ) u from rfl]
        linear_combination -hu
      · have hc : Fin.rev p ≠ cI r := fun h => hp ((rev_eq_c_iff p).1 h)
        simp [hp, hc]
    · simp [hq]
  · have hne : eI 0 r a ≠ cI r := by
      intro h
      have := congrArg Fin.val h
      simp [eI, cI] at this
      omega
    simp only [bvec, dgl, Matrix.diagonal_mulVec_single, if_neg hne, one_mul]
  · have hne : esI 0 r a ≠ cI r := by
      intro h
      have := congrArg Fin.val h
      simp [esI, cI] at this
      omega
    simp only [bvec, dgl, Matrix.diagonal_mulVec_single, if_neg hne, one_mul]

/- English proof (translation)
Establish `hjl` using `j.isLt`. Establish `hcol : g *ᵥ bvec j = bvec j`. Break down `lt_or_gt_of_ne (show j.val ≠ r from fun h => hj (Fin.ext h)) with h | h` into its components or cases. Use `(hg.2 ⟨j.val, h⟩).1` as an intermediate fact. Establish `e : eI 0 r ⟨j.val, h⟩ = j` using `Fin.ext rfl`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Use `(hg.2 ⟨2 * r - j.val, by omega⟩).2` as an intermediate fact. Establish `e : esI 0 r ⟨2 * r - j.val, by omega⟩ = j` using `Fin.ext (by simp [esI]; omega)`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Use `congrFun hcol i` as an intermediate fact.

Rewrite `this` using `[bvec, Matrix.mulVec_single_one, Pi.single_apply]`. Simplify `this` using `[Matrix.col]`.
-/
lemma col_fix {g : Mat 0 r} (hg : g ∈ UWb 0 r) (j : Fin (2 * r + 0 + 1)) (hj : j ≠ cI r)
    (i : Fin (2 * r + 0 + 1)) : g i j = if i = j then 1 else 0 := by
  have hjl := j.isLt
  have hcol : g *ᵥ bvec j = bvec j := by
    rcases lt_or_gt_of_ne (show j.val ≠ r from fun h => hj (Fin.ext h)) with h | h
    · have := (hg.2 ⟨j.val, h⟩).1
      have e : eI 0 r ⟨j.val, h⟩ = j := Fin.ext rfl
      rwa [e] at this
    · have := (hg.2 ⟨2 * r - j.val, by omega⟩).2
      have e : esI 0 r ⟨2 * r - j.val, by omega⟩ = j := Fin.ext (by simp [esI]; omega)
      rwa [e] at this
  have := congrFun hcol i
  rw [bvec, Matrix.mulVec_single_one, Pi.single_apply] at this
  simpa [Matrix.col] using this

/- English proof (translation)
Simplify using `[Matrix.mul_apply, col_fix hg p hp]`.
-/
lemma conjT_mul_H {g : Mat 0 r} (hg : g ∈ UWb 0 r) (p : Fin (2 * r + 0 + 1)) (hp : p ≠ cI r)
    (k : Fin (2 * r + 0 + 1)) : (gᴴ * Hpk 0 r) p k = Hpk 0 r p k := by
  simp [Matrix.mul_apply, col_fix hg p hp]

/- English proof (translation)
Establish `hp : Fin.rev q ≠ cI r` using `fun h => hq ((rev_eq_c_iff q).1 h)`. Establish `hU : gᴴ * Hpk 0 r * g = Hpk 0 r` using `hg.1`. Establish `h1` using `congrFun (congrFun hU (Fin.rev q)) (cI r)`. Rewrite `h1` using `[Matrix.mul_apply]`. Simplify using `only [conjT_mul_H hg _ hp] at h1`.

Simplify using `[Hpk_apply, Fin.rev_rev, hp, Ne.symm hq] at h1`. Conclude with `h1`.
-/
lemma col_c {g : Mat 0 r} (hg : g ∈ UWb 0 r) (q : Fin (2 * r + 0 + 1)) (hq : q ≠ cI r) :
    g q (cI r) = 0 := by
  have hp : Fin.rev q ≠ cI r := fun h => hq ((rev_eq_c_iff q).1 h)
  have hU : gᴴ * Hpk 0 r * g = Hpk 0 r := hg.1
  have h1 := congrFun (congrFun hU (Fin.rev q)) (cI r)
  rw [Matrix.mul_apply] at h1
  simp only [conjT_mul_H hg _ hp] at h1
  simp [Hpk_apply, Fin.rev_rev, hp, Ne.symm hq] at h1
  exact h1

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[dgl_apply]`. Distinguish the cases in `hj : j = cI r`. Substitute `hj` using the available equality. Distinguish the cases in `hi : i = cI r`.

Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[col_c hg i hi]`. Simplify using `[hi]`. Rewrite using `[col_fix hg j hj i]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[hj]`. Simplify using `[hij]`.
-/
lemma eq_dgl {g : Mat 0 r} (hg : g ∈ UWb 0 r) : g = dgl r (g (cI r) (cI r)) := by
  ext i j
  rw [dgl_apply]
  by_cases hj : j = cI r
  · subst hj
    by_cases hi : i = cI r
    · subst hi
      simp
    · rw [col_c hg i hi]
      simp [hi]
  · rw [col_fix hg j hj i]
    by_cases hij : i = j
    · subst hij
      simp [hj]
    · simp [hij]

/- English proof (translation)
Establish `hU : (dgl r u)ᴴ * Hpk 0 r * dgl r u = Hpk 0 r` using `h.1`. Establish `h1` using `congrFun (congrFun hU (cI r)) (cI r)`. Establish `hc : Fin.rev (cI r) = cI r` using `(rev_eq_c_iff (cI r)).2 rfl`. Simplify using `only [dgl, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply, if_true] at h1`. Rewrite `h1` using `[Hpk_apply]`.

Simplify using `only [hc, if_true] at h1`. Use `show (starRingEnd ℂ) u * u = 1`. Rewrite using `[show (starRingEnd ℂ) u = star u from rfl]`. Take the linear combination `-h1`.
-/
lemma dgl_norm {u : ℂ} (h : dgl r u ∈ UWb 0 r) : (starRingEnd ℂ) u * u = 1 := by
  have hU : (dgl r u)ᴴ * Hpk 0 r * dgl r u = Hpk 0 r := h.1
  have h1 := congrFun (congrFun hU (cI r)) (cI r)
  have hc : Fin.rev (cI r) = cI r := (rev_eq_c_iff (cI r)).2 rfl
  simp only [dgl, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Pi.star_apply, if_true] at h1
  rw [Hpk_apply] at h1
  simp only [hc, if_true] at h1
  show (starRingEnd ℂ) u * u = 1
  rw [show (starRingEnd ℂ) u = star u from rfl]
  linear_combination -h1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `e` using `eq_dgl hg`. Conclude with `⟨g (cI r) (cI r), dgl_norm (e ▸ hg), e⟩`. Introduce and unpack `⟨u, hu, rfl⟩`.

Conclude with `dgl_mem hu`.
-/
theorem mem_UWb_iff (g : Mat 0 r) :
    g ∈ UWb 0 r ↔ ∃ u : ℂ, (starRingEnd ℂ) u * u = 1 ∧ g = dgl r u := by
  constructor
  · intro hg
    have e := eq_dgl hg
    exact ⟨g (cI r) (cI r), dgl_norm (e ▸ hg), e⟩
  · rintro ⟨u, hu, rfl⟩
    exact dgl_mem hu

/- English proof (translation)
Rewrite using `[Complex.conj_mul']`. Use `norm_cast`. Conclude with `pow_eq_one_iff_of_nonneg (norm_nonneg u) two_ne_zero`.
-/
lemma conj_mul_iff (u : ℂ) : (starRingEnd ℂ) u * u = 1 ↔ ‖u‖ = 1 := by
  rw [Complex.conj_mul']
  norm_cast
  exact pow_eq_one_iff_of_nonneg (norm_nonneg u) two_ne_zero

/- English proof (translation)
Simplify using `only [dgl, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma dgl_mul (u v : ℂ) : dgl r u * dgl r v = dgl r (u * v) := by
  simp only [dgl, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

end PI.ExistsGaugeMeasureForEachRank.W
