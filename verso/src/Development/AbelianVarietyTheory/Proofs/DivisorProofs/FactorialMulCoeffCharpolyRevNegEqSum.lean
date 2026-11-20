import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs

open Polynomial Matrix

namespace GlobalTheory.GoodTop

/- English proof (translation)
Establish `hc : Fintype.card (Fin n) = Fintype.card s` using `by simp [hs]`. Establish `h1 : ∑ e : Fin n ≃ s, (M.submatrix (Subtype.val ∘ e) (Subtype.val ∘ e)).det = (n.factorial : A) * (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det`. Establish `: ∀ e : Fin n ≃ s, (M.submatrix (Subtype.val ∘ e) (Subtype.val ∘ e)).det = (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det`. Introduce `e`. Rewrite using `[← Matrix.submatrix_submatrix, Matrix.det_submatrix_equiv_self]`.

Simplify using `only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[Fintype.card_equiv (Fintype.equivOfCardEq hc), Fintype.card_fin]`. Rewrite using `[← h1]`. Use `symm`. Use `Finset.sum_bij (fun e _ => Subtype.val ∘ e) ?_ ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations.

Introduce `e _`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use extensionality with `x`. Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, rfl⟩`. Conclude with `(e a).2`. Introduce `hx`. Conclude with `⟨e.symm ⟨x, hx⟩, by simp⟩`. Introduce `e _ e' _ h`.

Use extensionality with `i`. Conclude with `congrFun h i`. Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp`. Set `f : Fin n → s` to `fun i => ⟨p i, hp ▸ Finset.mem_image_of_mem p (Finset.mem_univ i)⟩`.

Establish `hf : Function.Surjective f`. Introduce and unpack `⟨x, hx⟩`. Rewrite `hx` using `[← hp]`. Take `⟨a, -, rfl⟩` from `Finset.mem_image.mp hx`. Conclude with `⟨a, rfl⟩`.

Establish `hb : Function.Bijective f` using `(Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf, hc⟩`. Conclude with `⟨Equiv.ofBijective f hb, Finset.mem_univ _, rfl⟩`.
-/
theorem sum_det_submatrix_image_eq {A : Type} [CommRing A] {r : Type} [Fintype r] [DecidableEq r]
    (M : Matrix r r A) (n : ℕ) (s : Finset r) (hs : s.card = n) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n → r => Finset.univ.image p = s),
      (M.submatrix p p).det =
    (n.factorial : A) * (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
  classical
  have hc : Fintype.card (Fin n) = Fintype.card s := by simp [hs]
  have h1 : ∑ e : Fin n ≃ s, (M.submatrix (Subtype.val ∘ e) (Subtype.val ∘ e)).det =
      (n.factorial : A) * (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
    have : ∀ e : Fin n ≃ s, (M.submatrix (Subtype.val ∘ e) (Subtype.val ∘ e)).det =
        (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
      intro e
      rw [← Matrix.submatrix_submatrix, Matrix.det_submatrix_equiv_self]
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.card_equiv (Fintype.equivOfCardEq hc), Fintype.card_fin]
  rw [← h1]
  symm
  refine Finset.sum_bij (fun e _ => Subtype.val ∘ e) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro e _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨a, rfl⟩
      exact (e a).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  · intro e _ e' _ h
    ext i
    exact congrFun h i
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    let f : Fin n → s := fun i => ⟨p i, hp ▸ Finset.mem_image_of_mem p (Finset.mem_univ i)⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      rw [← hp] at hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨a, rfl⟩
    have hb : Function.Bijective f :=
      (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf, hc⟩
    exact ⟨Equiv.ofBijective f hb, Finset.mem_univ _, rfl⟩

/- English proof (translation)
Establish `hrev : (-M).charpolyRev = det (1 + (X : A[X]) • M.map C)`. Simplify using `only [charpolyRev, sub_eq_add_neg]`. Use `congr 2`. Rewrite using `[Matrix.map_neg C (map_neg C) M, smul_neg, neg_neg]`. Establish `hdet : ∀ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ((Equiv.Perm.sign π : ℤ) : A) * ∏ i, M (p i) (p (π i)) = (M.submatrix p p).det`.

Introduce `p`. Rewrite using `[← Matrix.det_transpose, Matrix.det_apply']`. Both sides reduce to the same expression. Rewrite using `[hrev, coeff_det_one_add_X_smul_eq_sum_minors, Finset.mul_sum]`. Simplify using `only [hdet]`.

Rewrite using `[← Finset.sum_filter_of_ne (s := Finset.univ) (p := fun p : Fin n → r => Finset.univ.image p ∈ (Finset.univ : Finset r).powersetCard n)]`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset r).powersetCard n) (g := fun p : Fin n → r => Finset.univ.image p) (fun p hp => (Finset.mem_filter.mp hp).2)]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Rewrite using `[← sum_det_submatrix_image_eq M n s (Finset.mem_powersetCard.mp hs).2]`. Use `Finset.sum_congr ?_ fun _ _ => rfl` and prove the remaining obligations.

Use extensionality with `p`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `⟨fun h => ⟨h ▸ hs, h⟩, fun h => h.2⟩`. Introduce `p _ hp`. Establish `hinj : Function.Injective p`.

Introduce `i j hij`. Assume the negation of the conclusion as `hne`. Conclude with `hp (Matrix.det_zero_of_row_eq hne (by ext k; simp [hij]))`. Rewrite using `[Finset.mem_powersetCard, Finset.card_image_of_injective _ hinj]`. Simplify using the standard rewrite rules.
-/
theorem factorial_mul_coeff_charpolyRev_neg {A : Type} [CommRing A] {r : Type} [Fintype r]
    [DecidableEq r] (M : Matrix r r A) (n : ℕ) :
    (n.factorial : A) * (Matrix.charpolyRev (-M)).coeff n =
      ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : A) * ∏ i, M (p i) (p (π i)) := by
  classical
  have hrev : (-M).charpolyRev = det (1 + (X : A[X]) • M.map C) := by
    simp only [charpolyRev, sub_eq_add_neg]
    congr 2
    rw [Matrix.map_neg C (map_neg C) M, smul_neg, neg_neg]
  have hdet : ∀ p : Fin n → r, ∑ π : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign π : ℤ) : A) * ∏ i, M (p i) (p (π i)) = (M.submatrix p p).det := by
    intro p
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  rw [hrev, coeff_det_one_add_X_smul_eq_sum_minors, Finset.mul_sum]
  simp only [hdet]
  rw [← Finset.sum_filter_of_ne (s := Finset.univ)
    (p := fun p : Fin n → r => Finset.univ.image p ∈ (Finset.univ : Finset r).powersetCard n)]
  · rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset r).powersetCard n)
      (g := fun p : Fin n → r => Finset.univ.image p) (fun p hp => (Finset.mem_filter.mp hp).2)]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [← sum_det_submatrix_image_eq M n s (Finset.mem_powersetCard.mp hs).2]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h ▸ hs, h⟩, fun h => h.2⟩
  · intro p _ hp
    have hinj : Function.Injective p := by
      intro i j hij
      by_contra hne
      exact hp (Matrix.det_zero_of_row_eq hne (by ext k; simp [hij]))
    rw [Finset.mem_powersetCard, Finset.card_image_of_injective _ hinj]
    simp

end GlobalTheory.GoodTop
