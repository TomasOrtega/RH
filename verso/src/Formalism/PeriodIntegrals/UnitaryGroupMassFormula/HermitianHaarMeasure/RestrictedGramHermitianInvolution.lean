import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Development
import Formalism.FormalDegreeBessel.FinalG

open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rel_posL_val (k r : ℕ) (i : Fin (r + 1)) (l : Fin (mdim k r i)) :
    (posL k r i l).val = l.val + i.val := rfl

/- English proof (translation)
Introduce `a b h`. Apply `Fin.ext` to reduce the goal to its premises. Establish `h'` using `congrArg Fin.val h`. Rewrite `h'` using `[rel_posL_val, rel_posL_val]`. Use linear arithmetic over natural numbers and integers.
-/
theorem rel_posL_injective (k r : ℕ) (i : Fin (r + 1)) : Function.Injective (posL k r i) := by
  intro a b h
  apply Fin.ext
  have h' := congrArg Fin.val h
  rw [rel_posL_val, rel_posL_val] at h'
  omega

/- English proof (translation)
Rewrite using `[rel_posL_val]`. Establish `hl : l.val < 2 * (r - i.val) + k + 1` using `l.isLt`. Establish `hi` using `i.isLt`. Use linear arithmetic over natural numbers and integers.
-/
theorem rel_posL_bound (k r : ℕ) (i : Fin (r + 1)) (l : Fin (mdim k r i)) :
    i.val ≤ (posL k r i l).val ∧ (posL k r i l).val + i.val ≤ 2 * r + k := by
  rw [rel_posL_val]
  have hl : l.val < 2 * (r - i.val) + k + 1 := l.isLt
  have hi := i.isLt
  omega

/- English proof (translation)
Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem rel_hpk_off_left (k r : ℕ) (p q : Fin (2 * r + k + 1)) (j : ℕ)
    (hp : j ≤ p.val ∧ p.val + j ≤ 2 * r + k) (hq : q.val < j ∨ 2 * r + k < q.val + j) :
    Hpk k r q p = 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem rel_hpk_off_right (k r : ℕ) (p q : Fin (2 * r + k + 1)) (j : ℕ)
    (hp : j ≤ p.val ∧ p.val + j ≤ 2 * r + k) (hq : q.val < j ∨ 2 * r + k < q.val + j) :
    Hpk k r p q = 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Rewrite using `[← Finset.sum_image (s := Finset.univ) (g := posL k r i) (fun x _ y _ h => rel_posL_injective k r i h)]`. Use `(Finset.sum_subset (Finset.subset_univ _) ?_).symm` and prove the remaining obligations. Introduce `a _ ha`. Apply `hF` to reduce the goal to its premises. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Apply `ha` to reduce the goal to its premises. Establish `hi` using `i.isLt`. Use `Finset.mem_image.2 ⟨⟨a.val - i.val, ?_⟩, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use `show a.val - i.val < 2 * (r - i.val) + k + 1`.

Use linear arithmetic over natural numbers and integers. Apply `Fin.ext show a.val - i.val + i.val = a.val` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.
-/
theorem rel_sum_posL (k r : ℕ) (i : Fin (r + 1)) (F : Fin (2 * r + k + 1) → ℂ)
    (hF : ∀ a : Fin (2 * r + k + 1), (a.val < i.val ∨ 2 * r + k < a.val + i.val) → F a = 0) :
    ∑ a, F a = ∑ l : Fin (mdim k r i), F (posL k r i l) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := posL k r i)
    (fun x _ y _ h => rel_posL_injective k r i h)]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro a _ ha
  apply hF
  by_contra hc
  push_neg at hc
  apply ha
  have hi := i.isLt
  refine Finset.mem_image.2 ⟨⟨a.val - i.val, ?_⟩, Finset.mem_univ _, ?_⟩
  · show a.val - i.val < 2 * (r - i.val) + k + 1
    omega
  · apply Fin.ext
    show a.val - i.val + i.val = a.val
    omega

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hU]`.
-/
theorem rel_herm_unitary {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) (hU : gᴴ * H * g = H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hU]

/- English proof (translation)
Unfold `herm bvec`. Simplify using `[dotProduct, Matrix.mulVec, Pi.single_apply]`.
-/
theorem rel_herm_bvec {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (p : Fin n) (y : Fin n → ℂ) :
    herm H (bvec p) y = ∑ a, star (y a) * H a p := by
  unfold herm bvec
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

/- English proof (translation)
Introduce `k r z i _ g hg c`. Establish `hU : gᴴ * Hpk k r * g = Hpk k r` using `hg.1`. Take `⟨_, hI, -⟩` from `hpkFacts k r`. Establish `hleft : (Hpk k r * gᴴ * Hpk k r) * g = 1`. Rewrite using `[Matrix.mul_assoc (Hpk k r * gᴴ), Matrix.mul_assoc (Hpk k r), ← Matrix.mul_assoc gᴴ, hU, hI]`.

Establish `hdet : IsUnit g.det` using `Matrix.isUnit_det_of_left_inverse hleft`. Establish `hf : fvec k r z i = g *ᵥ (g⁻¹ *ᵥ fvec k r z i)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]`. Establish `key : herm (Hpk k r) (g *ᵥ bvec (posL k r i c)) (fvec k r z i) = herm (Hpk k r) (bvec (posL k r i c)) (g⁻¹ *ᵥ fvec k r z i)` using `by conv_lhs => rw [hf]`. Conclude with `rel_herm_unitary _ _ hU _ _`.

Establish `hsum` using `rel_sum_posL k r i (fun a => star ((g⁻¹ *ᵥ fvec k r z i) a) * Hpk k r a (posL k r i c)) (by`. Introduce `a ha`. Use `show star ((g⁻¹ *ᵥ fvec k r z i) a) * Hpk k r a (posL k r i c) = 0`. Rewrite using `[rel_hpk_off_left k r (posL k r i c) a i.val (rel_posL_bound k r i c) ha, mul_zero])`. Use `show herm (Hpk k r) (g *ᵥ bvec (posL k r i c)) (fvec k r z i) = ∑ l, Hm k r i l c * star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l))`.

Rewrite using `[key, rel_herm_bvec]`. Use `hsum.trans (Finset.sum_congr rfl fun l _ => ?_)` and prove the remaining obligations. Use `show star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l)) * Hpk k r (posL k r i l) (posL k r i c) = Hm k r i l c * star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l))`. Rewrite using `[mul_comm]`. Both sides reduce to the same expression.
-/
theorem conjugate_y_relation : YbRel := by
  intro k r z i _ g hg c
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
  obtain ⟨_, hI, -⟩ := hpkFacts k r
  have hleft : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc (Hpk k r * gᴴ), Matrix.mul_assoc (Hpk k r), ← Matrix.mul_assoc gᴴ, hU, hI]
  have hdet : IsUnit g.det := Matrix.isUnit_det_of_left_inverse hleft
  have hf : fvec k r z i = g *ᵥ (g⁻¹ *ᵥ fvec k r z i) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have key : herm (Hpk k r) (g *ᵥ bvec (posL k r i c)) (fvec k r z i) =
      herm (Hpk k r) (bvec (posL k r i c)) (g⁻¹ *ᵥ fvec k r z i) := by
    conv_lhs => rw [hf]
    exact rel_herm_unitary _ _ hU _ _
  have hsum := rel_sum_posL k r i
    (fun a => star ((g⁻¹ *ᵥ fvec k r z i) a) * Hpk k r a (posL k r i c)) (by
      intro a ha
      show star ((g⁻¹ *ᵥ fvec k r z i) a) * Hpk k r a (posL k r i c) = 0
      rw [rel_hpk_off_left k r (posL k r i c) a i.val (rel_posL_bound k r i c) ha, mul_zero])
  show herm (Hpk k r) (g *ᵥ bvec (posL k r i c)) (fvec k r z i) =
    ∑ l, Hm k r i l c * star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l))
  rw [key, rel_herm_bvec]
  refine hsum.trans (Finset.sum_congr rfl fun l _ => ?_)
  show star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l)) * Hpk k r (posL k r i l) (posL k r i c) =
    Hm k r i l c * star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l))
  rw [mul_comm]
  rfl

/- English proof (translation)
Introduce `k r z' i _ c`. Establish `hsum` using `rel_sum_posL k r i (fun a => star (fvec k r z' i a) * Hpk k r a (posL k r i c)) (by`. Introduce `a ha`. Use `show star (fvec k r z' i a) * Hpk k r a (posL k r i c) = 0`. Rewrite using `[rel_hpk_off_left k r (posL k r i c) a i.val (rel_posL_bound k r i c) ha, mul_zero])`.

Use `show herm (Hpk k r) (bvec (posL k r i c)) (fvec k r z' i) = ∑ l, Hm k r i l c * star (fvec k r z' i (posL k r i l))`. Rewrite using `[rel_herm_bvec]`. Use `hsum.trans (Finset.sum_congr rfl fun l _ => ?_)` and prove the remaining obligations. Use `show star (fvec k r z' i (posL k r i l)) * Hpk k r (posL k r i l) (posL k r i c) = Hm k r i l c * star (fvec k r z' i (posL k r i l))`. Rewrite using `[mul_comm]`.

Both sides reduce to the same expression.
-/
theorem conjugate_x_relation : XbRel := by
  intro k r z' i _ c
  have hsum := rel_sum_posL k r i
    (fun a => star (fvec k r z' i a) * Hpk k r a (posL k r i c)) (by
      intro a ha
      show star (fvec k r z' i a) * Hpk k r a (posL k r i c) = 0
      rw [rel_hpk_off_left k r (posL k r i c) a i.val (rel_posL_bound k r i c) ha, mul_zero])
  show herm (Hpk k r) (bvec (posL k r i c)) (fvec k r z' i) =
    ∑ l, Hm k r i l c * star (fvec k r z' i (posL k r i l))
  rw [rel_herm_bvec]
  refine hsum.trans (Finset.sum_congr rfl fun l _ => ?_)
  show star (fvec k r z' i (posL k r i l)) * Hpk k r (posL k r i l) (posL k r i c) =
    Hm k r i l c * star (fvec k r z' i (posL k r i l))
  rw [mul_comm]
  rfl

/- English proof (translation)
Introduce `k r i`. Take `⟨hH, hI, -⟩` from `hpkFacts k r`. Prove the components needed by the constructor for the conclusion. Use extensionality with `a b show star (Hpk k r (posL k r i b) (posL k r i a)) = Hpk k r (posL k r i a) (posL k r i b)`. Rewrite using `[← Matrix.conjTranspose_apply (Hpk k r), hH]`.

Use extensionality with `a b`. Establish `h1 : (Hm k r i * Hm k r i) a b = (Hpk k r * Hpk k r) (posL k r i a) (posL k r i b)`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`. Use `symm`. Use `rel_sum_posL k r i (fun q => Hpk k r (posL k r i a) q * Hpk k r q (posL k r i b)) ?_` and prove the remaining obligations.

Introduce `q hq`. Use `show Hpk k r (posL k r i a) q * Hpk k r q (posL k r i b) = 0`. Rewrite using `[rel_hpk_off_right k r (posL k r i a) q i.val (rel_posL_bound k r i a) hq, zero_mul]`. Rewrite using `[h1, hI, Matrix.one_apply, Matrix.one_apply]`. Distinguish the cases in `h : a = b`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg (fun e => h (rel_posL_injective k r i e))]`.
-/
theorem restricted_gram_hermitian_involution : HmFacts := by
  intro k r i
  obtain ⟨hH, hI, -⟩ := hpkFacts k r
  constructor
  · ext a b
    show star (Hpk k r (posL k r i b) (posL k r i a)) = Hpk k r (posL k r i a) (posL k r i b)
    rw [← Matrix.conjTranspose_apply (Hpk k r), hH]
  · ext a b
    have h1 : (Hm k r i * Hm k r i) a b = (Hpk k r * Hpk k r) (posL k r i a) (posL k r i b) := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      symm
      refine rel_sum_posL k r i
        (fun q => Hpk k r (posL k r i a) q * Hpk k r q (posL k r i b)) ?_
      intro q hq
      show Hpk k r (posL k r i a) q * Hpk k r q (posL k r i b) = 0
      rw [rel_hpk_off_right k r (posL k r i a) q i.val (rel_posL_bound k r i a) hq, zero_mul]
    rw [h1, hI, Matrix.one_apply, Matrix.one_apply]
    by_cases h : a = b
    · subst h
      simp
    · rw [if_neg h, if_neg (fun e => h (rel_posL_injective k r i e))]

end PI.QnHermHaar
