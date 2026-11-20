import Mathlib
import Formalism.BranchSandwichDivisors.StatementW
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockbLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetMinor
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylNonDom

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL

noncomputable section

namespace Formalism.BranchingDeterminantCap

section XiA

variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `sum_mem fun τ _ => mul_mem ?_ (prod_mem fun i _ => h _ _)` and prove the remaining obligations. Use `first`. Consider the case `exact intCast_mem _ _`. Consider the case `exact Subalgebra.intCast_mem _ _`.

Consider the case `(rw [← map_intCast (algebraMap ℂ (MvPolynomial σ ℂ))]; exact Subalgebra.algebraMap_mem _ _)`.
-/
lemma xn_det_supported {σ m : Type*} [Fintype m] [DecidableEq m] (s : Set σ)
    (A : Matrix m m (MvPolynomial σ ℂ)) (h : ∀ i j, A i j ∈ supported ℂ s) :
    A.det ∈ supported ℂ s := by
  rw [Matrix.det_apply']
  refine sum_mem fun τ _ => mul_mem ?_ (prod_mem fun i _ => h _ _)
  first
  | exact intCast_mem _ _
  | exact Subalgebra.intCast_mem _ _
  | (rw [← map_intCast (algebraMap ℂ (MvPolynomial σ ℂ))]; exact Subalgebra.algebraMap_mem _ _)

/- English proof (translation)
Rewrite `hf` using `[MvPolynomial.mem_supported]`. Use `first`. Consider the case `exact MvPolynomial.pderiv_eq_zero_of_notMem_vars fun hv' => hv (hf hv')`. Consider the case `exact MvPolynomial.pderiv_eq_zero_of_not_mem_vars fun hv' => hv (hf hv')`.
-/
lemma xn_pderiv_supported {σ : Type*} (s : Set σ) (v : σ) (hv : v ∉ s) (f : MvPolynomial σ ℂ)
    (hf : f ∈ supported ℂ s) : pderiv v f = 0 := by
  rw [MvPolynomial.mem_supported] at hf
  first
  | exact MvPolynomial.pderiv_eq_zero_of_notMem_vars fun hv' => hv (hf hv')
  | exact MvPolynomial.pderiv_eq_zero_of_not_mem_vars fun hv' => hv (hf hv')

/- English proof (translation)
Unfold `Function.Injective at h`. Use `push_neg at h`. Take `⟨i, j, hij, hne⟩` from `h`. Unfold `initMinor`. Conclude with `Matrix.det_zero_of_row_eq hne (funext fun q => by simp [hij])`.
-/
lemma xn_minor_zero {s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) (h : ¬ Function.Injective I) :
    initMinor ℂ I hs = 0 := by
  unfold Function.Injective at h
  push_neg at h
  obtain ⟨i, j, hij, hne⟩ := h
  unfold initMinor
  exact Matrix.det_zero_of_row_eq hne (funext fun q => by simp [hij])

def xnCof (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ) (j : Fin (p + 1)) :
    MvPolynomial (Fin r × Fin n) ℂ :=
  (-1) ^ (p + j.val) * (Matrix.of fun i k : Fin p =>
    (X (ι (a i), Fin.castLE hp (j.succAbove k)) : MvPolynomial (Fin r × Fin n) ℂ)).det

/- English proof (translation)
Unfold `initMinor xnCof`. Rewrite using `[Matrix.det_succ_row _ (Fin.last p)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Fin.snoc_last, Fin.val_last, Fin.succAbove_last, Fin.snoc_castSucc]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma xn_lap (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ) (b : κ) :
    initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp =
      ∑ j, X (ι b, Fin.castLE hp j) * xnCof ι hp a j := by
  unfold initMinor xnCof
  rw [Matrix.det_succ_row _ (Fin.last p)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Fin.snoc_last, Fin.val_last,
    Fin.succAbove_last, Fin.snoc_castSucc]
  ring

/- English proof (translation)
Unfold `xnCof initMinor`. Rewrite using `[Fin.val_last, (Even.neg_one_pow ⟨p, rfl⟩ : ((-1 : MvPolynomial (Fin r × Fin n) ℂ)) ^ (p + p) = 1), one_mul]`. Use `congr 1`. Use `Matrix.ext fun i k => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply, Function.comp_apply, Fin.succAbove_last]`.

Both sides reduce to the same expression.
-/
lemma xn_cof_last (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ) :
    xnCof ι hp a (Fin.last p) = initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) := by
  unfold xnCof initMinor
  rw [Fin.val_last, (Even.neg_one_pow ⟨p, rfl⟩ : ((-1 : MvPolynomial (Fin r × Fin n) ℂ)) ^ (p + p) = 1),
    one_mul]
  congr 1
  refine Matrix.ext fun i k => ?_
  simp only [Matrix.of_apply, Function.comp_apply, Fin.succAbove_last]
  rfl

/- English proof (translation)
Unfold `xnCof`. Use `mul_mem (pow_mem (neg_mem (one_mem _)) _) (xn_det_supported _ _ fun i k => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.of_apply]`. Use `first`. Consider the case `exact (MvPolynomial.X_mem_supported (R := ℂ)).2 ⟨i, rfl⟩`.

Consider the case `exact MvPolynomial.X_mem_supported.mpr ⟨i, rfl⟩`.
-/
lemma xn_cof_supported (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ) (j : Fin (p + 1)) :
    xnCof ι hp a j ∈ supported ℂ {v : Fin r × Fin n | ∃ i, v.1 = ι (a i)} := by
  unfold xnCof
  refine mul_mem (pow_mem (neg_mem (one_mem _)) _) (xn_det_supported _ _ fun i k => ?_)
  rw [Matrix.of_apply]
  first
  | exact (MvPolynomial.X_mem_supported (R := ℂ)).2 ⟨i, rfl⟩
  | exact MvPolynomial.X_mem_supported.mpr ⟨i, rfl⟩

/- English proof (translation)
Use `split_ifs with hb`. Take `⟨i, -, hi⟩` from `Finset.mem_image.1 hb`. Establish `hni : ¬ Function.Injective (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ))`. Introduce `hinj`. Establish `h2` using `@hinj (Fin.castSucc i) (Fin.last p) (by simp [hi])`.

Conclude with `(Fin.castSucc_lt_last i).ne h2`. Rewrite using `[xn_minor_zero _ hp hni, map_zero]`. Establish `hns : ((ι b, (⟨p, hp⟩ : Fin n)) : Fin r × Fin n) ∉ {v : Fin r × Fin n | ∃ i, v.1 = ι (a i)}`. Introduce and unpack `⟨i, hi⟩`. Conclude with `hb (Finset.mem_image.2 ⟨i, Finset.mem_univ _, (hι hi).symm⟩)`.

Rewrite using `[xn_lap ι hp a b, map_sum, Finset.sum_eq_single (Fin.last p), ← xn_cof_last ι hp a]`. Rewrite using `[Derivation.leibniz, xn_pderiv_supported _ _ hns _ (xn_cof_supported ι hp a _), smul_zero, zero_add, MvPolynomial.pderiv_X, smul_eq_mul]`. Simplify using `[Pi.single_apply, Fin.ext_iff]`. Introduce `j _ hj`. Establish `hjv : (j : ℕ) ≠ p` using `fun h => hj (Fin.ext (by simpa using h))`.

Rewrite using `[Derivation.leibniz, xn_pderiv_supported _ _ hns _ (xn_cof_supported ι hp a _), smul_zero, zero_add, MvPolynomial.pderiv_X, smul_eq_mul]`. Simplify using `[Pi.single_apply, Fin.ext_iff, hjv]`. Simplify using the standard rewrite rules.
-/
lemma xn_part1 (ι : κ → Fin r) (hι : Function.Injective ι) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ)
    (b : κ) :
    pderiv (ι b, (⟨p, hp⟩ : Fin n)) (initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp) =
      if b ∈ Finset.univ.image a then 0 else initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) := by
  split_ifs with hb
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hb
    have hni : ¬ Function.Injective (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) := by
      intro hinj
      have h2 := @hinj (Fin.castSucc i) (Fin.last p) (by simp [hi])
      exact (Fin.castSucc_lt_last i).ne h2
    rw [xn_minor_zero _ hp hni, map_zero]
  · have hns : ((ι b, (⟨p, hp⟩ : Fin n)) : Fin r × Fin n) ∉
        {v : Fin r × Fin n | ∃ i, v.1 = ι (a i)} := by
      rintro ⟨i, hi⟩
      exact hb (Finset.mem_image.2 ⟨i, Finset.mem_univ _, (hι hi).symm⟩)
    rw [xn_lap ι hp a b, map_sum, Finset.sum_eq_single (Fin.last p), ← xn_cof_last ι hp a]
    · rw [Derivation.leibniz, xn_pderiv_supported _ _ hns _ (xn_cof_supported ι hp a _), smul_zero,
        zero_add, MvPolynomial.pderiv_X, smul_eq_mul]
      simp [Pi.single_apply, Fin.ext_iff]
    · intro j _ hj
      have hjv : (j : ℕ) ≠ p := fun h => hj (Fin.ext (by simpa using h))
      rw [Derivation.leibniz, xn_pderiv_supported _ _ hns _ (xn_cof_supported ι hp a _), smul_zero,
        zero_add, MvPolynomial.pderiv_X, smul_eq_mul]
      simp [Pi.single_apply, Fin.ext_iff, hjv]
    · simp

/- English proof (translation)
Establish `hl : Fin.castLE hp (Fin.last p) = (⟨p, hp⟩ : Fin n)` using `Fin.ext (by simp)`. Simplify using `only [xn_lap ι hp a, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm, Finset.sum_eq_single (Fin.last p)]`. Simplify using `only [hl]`. Repeatedly rewrite using `[mul_right_comm _ (xnCof ι hp a (Fin.last p)) _]`.

Rewrite using `[← Finset.sum_mul, h1, xn_cof_last]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j _ hj`. Establish `hjv : (Fin.castLE hp j).val < p`. Establish `h3 : (j : ℕ) ≠ p` using `fun h => hj (Fin.ext (by simpa using h))`.

Establish `h4` using `j.isLt`. Simplify using `only [Fin.coe_castLE]`. Use linear arithmetic over natural numbers and integers. Repeatedly rewrite using `[mul_right_comm _ (xnCof ι hp a j) _]`. Rewrite using `[← Finset.sum_mul, h0 (Fin.castLE hp j) hjv, zero_mul]`.

Simplify using the standard rewrite rules.
-/
lemma xn_part2 (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ)
    (f : MvPolynomial (Fin r × Fin n) ℂ) (m : ℂ)
    (h0 : ∀ t : Fin n, t.val < p → ∑ b : κ, X (ι b, t) * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f = 0)
    (h1 : ∑ b : κ, X (ι b, (⟨p, hp⟩ : Fin n)) * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f = C m * f) :
    ∑ b : κ, initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp *
        pderiv (ι b, (⟨p, hp⟩ : Fin n)) f =
      C m * (initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) * f) := by
  have hl : Fin.castLE hp (Fin.last p) = (⟨p, hp⟩ : Fin n) := Fin.ext (by simp)
  simp only [xn_lap ι hp a, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_eq_single (Fin.last p)]
  · simp only [hl]
    simp_rw [mul_right_comm _ (xnCof ι hp a (Fin.last p)) _]
    rw [← Finset.sum_mul, h1, xn_cof_last]
    ring
  · intro j _ hj
    have hjv : (Fin.castLE hp j).val < p := by
      have h3 : (j : ℕ) ≠ p := fun h => hj (Fin.ext (by simpa using h))
      have h4 := j.isLt
      simp only [Fin.coe_castLE]
      omega
    simp_rw [mul_right_comm _ (xnCof ι hp a j) _]
    rw [← Finset.sum_mul, h0 (Fin.castLE hp j) hjv, zero_mul]
  · simp

/- English proof (translation)
Establish `hsplit : ∀ b : κ, pderiv (ι b, (⟨p, hp⟩ : Fin n)) (initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp * f) = initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f + f * (if b ∈ Finset.univ.image a then 0 else initMinor ℂ (ι ∘ a) (Nat.le_of_s …`. Introduce `b`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul, xn_part1 ι hι hp a b]`. Simplify using `only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]`. Rewrite using `[xn_part2 ι hp a f m h0 h1]`.

Distinguish the cases in `ha : Function.Injective a`. Establish `hsum : ∑ b : κ, (if b ∈ Finset.univ.image a then (0 : MvPolynomial (Fin r × Fin n) ℂ) else initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp)) = ((Fintype.card κ : MvPolynomial (Fin r × Fin n) ℂ) - p) * initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp)`. Apply the tactic sequence `rw [Finset.sum_congr rfl fun b _ => (show (if b ∈ Finset.univ.image a then (0 : MvPolynomial (Fin r × Fin n) ℂ) else initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp)) = initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) - (if b ∈ Finset.univ.image a then initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le …`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Finset.card_image_of_injective _ ha]`. Simplify using `only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum, map_add, map_sub, map_natCast, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `hz : initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) = 0` using `xn_minor_zero _ _ fun h => ha h.of_comp`. Simplify using `[hz]`.
-/
lemma xn_key (ι : κ → Fin r) (hι : Function.Injective ι) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ)
    (f : MvPolynomial (Fin r × Fin n) ℂ) (m : ℂ)
    (h0 : ∀ t : Fin n, t.val < p → ∑ b : κ, X (ι b, t) * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f = 0)
    (h1 : ∑ b : κ, X (ι b, (⟨p, hp⟩ : Fin n)) * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f = C m * f) :
    ∑ b : κ, pderiv (ι b, (⟨p, hp⟩ : Fin n))
        (initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp * f) =
      C ((Fintype.card κ : ℂ) - p + m) * (initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) * f) := by
  have hsplit : ∀ b : κ, pderiv (ι b, (⟨p, hp⟩ : Fin n))
      (initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp * f) =
      initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f +
      f * (if b ∈ Finset.univ.image a then 0 else initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp)) := by
    intro b
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, xn_part1 ι hι hp a b]
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [xn_part2 ι hp a f m h0 h1]
  by_cases ha : Function.Injective a
  · have hsum : ∑ b : κ, (if b ∈ Finset.univ.image a then (0 : MvPolynomial (Fin r × Fin n) ℂ)
        else initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp)) =
        ((Fintype.card κ : MvPolynomial (Fin r × Fin n) ℂ) - p) *
          initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) := by
      rw [Finset.sum_congr rfl fun b _ => (show (if b ∈ Finset.univ.image a then
          (0 : MvPolynomial (Fin r × Fin n) ℂ) else initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp)) =
          initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) - (if b ∈ Finset.univ.image a then
          initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) else 0) by split_ifs <;> simp)]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, Finset.card_image_of_injective _ ha]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hsum, map_add, map_sub, map_natCast, map_natCast]
    ring
  · have hz : initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) = 0 :=
      xn_minor_zero _ _ fun h => ha h.of_comp
    simp [hz]

end XiA

section XiB

variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]

def xnMono (ι : κ → Fin r) {p : ℕ} (hp : p ≤ n) (a : Fin p → κ) : MvPolynomial (Fin r × Fin n) ℂ :=
  ∏ q : Fin p, X (ι (a q), Fin.castLE hp q)

def xnC (M : ℕ) (m : ℕ → ℕ) (p : ℕ) : ℝ := ∏ q ∈ Finset.range p, ((M : ℝ) - q + m q)

def xnSg {p : ℕ} (π : Equiv.Perm (Fin p)) : ℂ := ((Equiv.Perm.sign π : ℤ) : ℂ)

/- English proof (translation)
Unfold `xnSg`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]`.
-/
lemma xnSg_mul_self {p : ℕ} (π : Equiv.Perm (Fin p)) : xnSg π * xnSg π = 1 := by
  unfold xnSg
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]

/- English proof (translation)
Unfold `xnSg`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]`.
-/
lemma xnSg_star {p : ℕ} (π : Equiv.Perm (Fin p)) : star (xnSg π) = xnSg π := by
  unfold xnSg
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]

/- English proof (translation)
Unfold `initMinor xnMono xnSg`. Rewrite using `[Matrix.det_apply']`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_intCast]`. Both sides reduce to the same expression.
-/
lemma xn_minor_sum (ι : κ → Fin r) {p : ℕ} (hp : p ≤ n) (a : Fin p → κ) :
    initMinor ℂ (ι ∘ a) hp = ∑ π : Equiv.Perm (Fin p), C (xnSg π) * xnMono ι hp (a ∘ π) := by
  unfold initMinor xnMono xnSg
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_intCast]
  rfl

/- English proof (translation)
Unfold `initMinor xnSg`. Use `first`. Consider the case `(rw [map_intCast, ← Matrix.det_permute]; rfl)`. Consider the case `(rw [map_intCast]`. Conclude with `Matrix.det_permute π (Matrix.of fun x y : Fin p => (X ((ι ∘ a) x, Fin.castLE hp y) : MvPolynomial (Fin r × Fin n) ℂ)))`.
-/
lemma xn_minor_perm (ι : κ → Fin r) {p : ℕ} (hp : p ≤ n) (a : Fin p → κ) (π : Equiv.Perm (Fin p)) :
    initMinor ℂ (ι ∘ (a ∘ π)) hp = C (xnSg π) * initMinor ℂ (ι ∘ a) hp := by
  unfold initMinor xnSg
  first
  | (rw [map_intCast, ← Matrix.det_permute]; rfl)
  | (rw [map_intCast]
     exact Matrix.det_permute π (Matrix.of fun x y : Fin p =>
       (X ((ι ∘ a) x, Fin.castLE hp y) : MvPolynomial (Fin r × Fin n) ℂ)))

/- English proof (translation)
Use `set T := insert v m.support with hTdef`. Establish `hT : ∀ u : (Fin r × Fin n) →₀ ℕ, u.support ⊆ T → ∏ k ∈ u.support, (u k).factorial = (u v).factorial * ∏ k ∈ T.erase v, (u k).factorial`. Introduce `u hu`. Rewrite using `[Finset.mul_prod_erase T (fun k => (u k).factorial) (Finset.mem_insert_self v _)]`. Use `Finset.prod_subset hu fun k _ hk => ?_` and prove the remaining obligations.

Establish `h0 : u k = 0` using `by simpa using hk`. Rewrite using `[h0, Nat.factorial_zero]`. Establish `hsub : (Finsupp.single v 1 + m).support ⊆ T`. Introduce `k hk`. Assume the negation of the conclusion as `hc`.

Establish `hkv : k ≠ v`. Introduce and unpack `rfl`. Conclude with `hc (Finset.mem_insert_self _ _)`. Establish `hkm : m k = 0`. Assume the negation of the conclusion as `hm`.

Conclude with `hc (Finset.mem_insert_of_mem (Finsupp.mem_support_iff.2 hm))`. Establish `h5 : (Finsupp.single v 1 + m : (Fin r × Fin n) →₀ ℕ) k = 0` using `by simp [Finsupp.single_apply, Ne.symm hkv, hkm]`. Conclude with `(Finsupp.mem_support_iff.1 hk) h5`. Rewrite using `[hT _ hsub, hT m (Finset.subset_insert _ _)]`. Establish `hrest : ∏ k ∈ T.erase v, ((Finsupp.single v 1 + m : (Fin r × Fin n) →₀ ℕ) k).factorial = ∏ k ∈ T.erase v, (m k).factorial`.

Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hkv : k ≠ v` using `Finset.ne_of_mem_erase hk`. Simplify using `[Finsupp.single_apply, Ne.symm hkv]`. Rewrite using `[hrest]`. Simplify using `only [Finsupp.add_apply, Finsupp.single_eq_same]`.

Rewrite using `[add_comm 1, Nat.factorial_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma prod_factorial_single_add_eq_mul' (v : Fin r × Fin n) (m : (Fin r × Fin n) →₀ ℕ) :
    (∏ k ∈ (Finsupp.single v 1 + m).support,
      ((Finsupp.single v 1 + m : (Fin r × Fin n) →₀ ℕ) k).factorial) =
      (m v + 1) * ∏ k ∈ m.support, (m k).factorial := by
  set T := insert v m.support with hTdef
  have hT : ∀ u : (Fin r × Fin n) →₀ ℕ, u.support ⊆ T →
      ∏ k ∈ u.support, (u k).factorial = (u v).factorial * ∏ k ∈ T.erase v, (u k).factorial := by
    intro u hu
    rw [Finset.mul_prod_erase T (fun k => (u k).factorial) (Finset.mem_insert_self v _)]
    refine Finset.prod_subset hu fun k _ hk => ?_
    have h0 : u k = 0 := by simpa using hk
    rw [h0, Nat.factorial_zero]
  have hsub : (Finsupp.single v 1 + m).support ⊆ T := by
    intro k hk
    by_contra hc
    have hkv : k ≠ v := by
      rintro rfl
      exact hc (Finset.mem_insert_self _ _)
    have hkm : m k = 0 := by
      by_contra hm
      exact hc (Finset.mem_insert_of_mem (Finsupp.mem_support_iff.2 hm))
    have h5 : (Finsupp.single v 1 + m : (Fin r × Fin n) →₀ ℕ) k = 0 := by simp [Finsupp.single_apply, Ne.symm hkv, hkm]
    exact (Finsupp.mem_support_iff.1 hk) h5
  rw [hT _ hsub, hT m (Finset.subset_insert _ _)]
  have hrest : ∏ k ∈ T.erase v, ((Finsupp.single v 1 + m : (Fin r × Fin n) →₀ ℕ) k).factorial =
      ∏ k ∈ T.erase v, (m k).factorial := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hkv : k ≠ v := Finset.ne_of_mem_erase hk
    simp [Finsupp.single_apply, Ne.symm hkv]
  rw [hrest]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [add_comm 1, Nat.factorial_succ]
  ring

/- English proof (translation)
Proceed by induction on `H using MvPolynomial.induction_on'`. Use `next u a =>`. Rewrite using `[MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]`. Distinguish the cases in `hu : u = Finsupp.single v 1 + m`. Substitute `hu` using the available equality.

Rewrite using `[add_tsub_cancel_left, if_pos rfl, if_pos rfl]`. Simplify using `only [Finsupp.add_apply, Finsupp.single_eq_same]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hu, mul_zero] split_ifs with h2`.

Establish `h3 : u v = 0`. Assume the negation of the conclusion as `h4`. Apply `hu` to reduce the goal to its premises. Rewrite using `[← h2]`. Use extensionality with `k`.

Simplify using `only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]`. Use `split_ifs with h5`. Substitute `h5` using the available equality. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.

Rewrite using `[h3]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Use `next p q hp hq =>`. Simplify using `only [map_add, MvPolynomial.coeff_add, hp, hq, mul_add]`.
-/
private lemma coeff_pderiv_eq_mul_coeff_single_add (v : Fin r × Fin n) (m : (Fin r × Fin n) →₀ ℕ)
    (H : MvPolynomial (Fin r × Fin n) ℂ) :
    (pderiv v H).coeff m = ((m v + 1 : ℕ) : ℂ) * H.coeff (Finsupp.single v 1 + m) := by
  induction H using MvPolynomial.induction_on'
  next u a =>
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hu : u = Finsupp.single v 1 + m
    · subst hu
      rw [add_tsub_cancel_left, if_pos rfl, if_pos rfl]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      push_cast
      ring
    · rw [if_neg hu, mul_zero]
      split_ifs with h2
      · have h3 : u v = 0 := by
          by_contra h4
          apply hu
          rw [← h2]
          ext k
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          split_ifs with h5
          · subst h5
            omega
          · omega
        rw [h3]
        simp
      · rfl
  next p q hp hq =>
    simp only [map_add, MvPolynomial.coeff_add, hp, hq, mul_add]

/- English proof (translation)
Unfold `fockF`. Rewrite using `[MvPolynomial.support_X_mul, Finset.sum_map]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [addLeftEmbedding_apply, MvPolynomial.coeff_X_mul, coeff_pderiv_eq_mul_coeff_single_add, prod_factorial_single_add_eq_mul', star_mul']`. Use `push_cast`.

Rewrite using `[show star ((m v : ℂ) + 1) = (m v : ℂ) + 1 by simp]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma fockF_X_mul_eq_pderiv (v : Fin r × Fin n) (G H : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF (X v * G) H = fockF G (pderiv v H) := by
  unfold fockF
  rw [MvPolynomial.support_X_mul, Finset.sum_map]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [addLeftEmbedding_apply, MvPolynomial.coeff_X_mul, coeff_pderiv_eq_mul_coeff_single_add, prod_factorial_single_add_eq_mul', star_mul']
  push_cast
  rw [show star ((m v : ℂ) + 1) = (m v : ℂ) + 1 by simp]
  ring

/- English proof (translation)
Unfold `fockF`. Simplify using `only [MvPolynomial.coeff_sum, star_sum, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
private lemma fockF_sum_right' {ι' : Type*} (s : Finset ι') (F : MvPolynomial (Fin r × Fin n) ℂ)
    (G : ι' → MvPolynomial (Fin r × Fin n) ℂ) :
    fockF F (∑ i ∈ s, G i) = ∑ i ∈ s, fockF F (G i) := by
  unfold fockF
  simp only [MvPolynomial.coeff_sum, star_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Unfold `fockF`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_C_mul, star_mul']`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma fockF_C_mul_right (F G : MvPolynomial (Fin r × Fin n) ℂ) (c : ℂ) :
    fockF F (C c * G) = star c * fockF F G := by
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_C_mul, star_mul']
  ring

/- English proof (translation)
Proceed by induction on `p generalizing g with`. Consider the case `zero`. Simplify using `[xnMono, xnC, initMinor]`. Consider the case `succ p ih`. Establish `hp0 : p ≤ n` using `Nat.le_of_succ_le hp`.

Establish `hre : ∀ F : (Fin (p + 1) → κ) → ℂ, ∑ a, F a = ∑ a' : Fin p → κ, ∑ b : κ, F (Fin.snoc a' b : Fin (p + 1) → κ)`. Introduce `F`. Rewrite using `[← Fintype.sum_prod_type']`. Use `symm`. Use `Fintype.sum_bijective (fun x : (Fin p → κ) × κ => (Fin.snoc x.1 x.2 : Fin (p + 1) → κ)) ⟨?_, ?_⟩ _ _ fun x => rfl` and prove the remaining obligations.

Introduce `x y hxy`. Establish `h1` using `congrArg Fin.init hxy`. Establish `h2` using `congrFun hxy (Fin.last p)`. Simplify using `only [Fin.init_snoc, Fin.snoc_last] at h1 h2`. Conclude with `Prod.ext h1 h2`.

Introduce `a`. Conclude with `⟨(Fin.init a, a (Fin.last p)), Fin.snoc_init_self a⟩`. Establish `hmono : ∀ (a' : Fin p → κ) (b : κ), xnMono ι hp (Fin.snoc a' b : Fin (p + 1) → κ) = xnMono ι hp0 a' * X (ι b, (⟨p, hp⟩ : Fin n))`. Introduce `a' b`. Unfold `xnMono`.

Rewrite using `[Fin.prod_univ_castSucc]`. Simplify using `only [Fin.snoc_castSucc, Fin.snoc_last]`. Both sides reduce to the same expression. Establish `hstep : ∀ a' : Fin p → κ, ∑ b : κ, fockF (xnMono ι hp (Fin.snoc a' b : Fin (p + 1) → κ) * g) (initMinor ℂ (ι ∘ (Fin.snoc a' b : Fin (p + 1) → κ)) hp * f) = star ((Fintype.card κ : ℂ) - p + ((m p : ℕ) : ℂ)) * fockF (xnMono ι hp0 a' * g) (initMinor ℂ (ι ∘ a') hp0 * f)`. Introduce `a'`.

Establish `hE : ∀ b : κ, xnMono ι hp (Fin.snoc a' b : Fin (p + 1) → κ) * g = X (ι b, (⟨p, hp⟩ : Fin n)) * (xnMono ι hp0 a' * g)` using `fun b => by rw [hmono]; ring`. Simplify using `only [hE, fockF_X_mul_eq_pderiv]`. Rewrite using `[← fockF_sum_right', xn_key ι hι hp a' f ((m p : ℕ) : ℂ) (fun t ht => hR t ⟨p, hp⟩ ht) (hW ⟨p, hp⟩), fockF_C_mul_right]`. Rewrite using `[hre]`. Simplify using `only [hstep, ← Finset.mul_sum]`.

Rewrite using `[ih]`. Simplify using `only [xnC, Finset.prod_range_succ, star_add, star_sub, star_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma fock_pairing_initial_minor (ι : κ → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : κ, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : κ, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (p : ℕ) (hp : p ≤ n) (g : MvPolynomial (Fin r × Fin n) ℂ) :
    ∑ a : Fin p → κ, fockF (xnMono ι hp a * g) (initMinor ℂ (ι ∘ a) hp * f) =
      ((xnC (Fintype.card κ) m p : ℝ) : ℂ) * fockF g f := by
  induction p generalizing g with
  | zero =>
    simp [xnMono, xnC, initMinor]
  | succ p ih =>
    have hp0 : p ≤ n := Nat.le_of_succ_le hp
    have hre : ∀ F : (Fin (p + 1) → κ) → ℂ,
        ∑ a, F a = ∑ a' : Fin p → κ, ∑ b : κ, F (Fin.snoc a' b : Fin (p + 1) → κ) := by
      intro F
      rw [← Fintype.sum_prod_type']
      symm
      refine Fintype.sum_bijective (fun x : (Fin p → κ) × κ => (Fin.snoc x.1 x.2 : Fin (p + 1) → κ))
        ⟨?_, ?_⟩ _ _ fun x => rfl
      · intro x y hxy
        have h1 := congrArg Fin.init hxy
        have h2 := congrFun hxy (Fin.last p)
        simp only [Fin.init_snoc, Fin.snoc_last] at h1 h2
        exact Prod.ext h1 h2
      · intro a
        exact ⟨(Fin.init a, a (Fin.last p)), Fin.snoc_init_self a⟩
    have hmono : ∀ (a' : Fin p → κ) (b : κ), xnMono ι hp (Fin.snoc a' b : Fin (p + 1) → κ) =
        xnMono ι hp0 a' * X (ι b, (⟨p, hp⟩ : Fin n)) := by
      intro a' b
      unfold xnMono
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rfl
    have hstep : ∀ a' : Fin p → κ, ∑ b : κ, fockF (xnMono ι hp (Fin.snoc a' b : Fin (p + 1) → κ) * g)
        (initMinor ℂ (ι ∘ (Fin.snoc a' b : Fin (p + 1) → κ)) hp * f) =
        star ((Fintype.card κ : ℂ) - p + ((m p : ℕ) : ℂ)) *
          fockF (xnMono ι hp0 a' * g) (initMinor ℂ (ι ∘ a') hp0 * f) := by
      intro a'
      have hE : ∀ b : κ, xnMono ι hp (Fin.snoc a' b : Fin (p + 1) → κ) * g =
          X (ι b, (⟨p, hp⟩ : Fin n)) * (xnMono ι hp0 a' * g) := fun b => by rw [hmono]; ring
      simp only [hE, fockF_X_mul_eq_pderiv]
      rw [← fockF_sum_right', xn_key ι hι hp a' f ((m p : ℕ) : ℂ) (fun t ht => hR t ⟨p, hp⟩ ht) (hW ⟨p, hp⟩),
        fockF_C_mul_right]
    rw [hre]
    simp only [hstep, ← Finset.mul_sum]
    rw [ih]
    simp only [xnC, Finset.prod_range_succ, star_add, star_sub, star_natCast]
    push_cast
    ring

/- English proof (translation)
Unfold `fockF`. Use `Finset.sum_subset hS fun m _ hm => ?_` and prove the remaining obligations. Establish `h0 : F.coeff m = 0` using `by simpa using hm`. Rewrite using `[h0, zero_mul, zero_mul]`.
-/
private lemma fockF_eq_sum_coeff_factorial_of_support_subset (F G : MvPolynomial (Fin r × Fin n) ℂ)
    (S : Finset ((Fin r × Fin n) →₀ ℕ)) (hS : F.support ⊆ S) :
    fockF F G = ∑ m ∈ S, F.coeff m * star (G.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  refine Finset.sum_subset hS fun m _ hm => ?_
  have h0 : F.coeff m = 0 := by simpa using hm
  rw [h0, zero_mul, zero_mul]

/- English proof (translation)
Rewrite using `[fockF_eq_sum_coeff_factorial_of_support_subset (∑ i ∈ s, F i) G _ MvPolynomial.support_sum]`. Rewrite using `[Finset.sum_congr rfl fun i hi => fockF_eq_sum_coeff_factorial_of_support_subset (F i) G (s.biUnion fun i => (F i).support) (Finset.subset_biUnion_of_mem (fun i => (F i).support) hi)]`. Simplify using `only [MvPolynomial.coeff_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
private lemma fockF_sum_left' {ι' : Type*} (s : Finset ι') (F : ι' → MvPolynomial (Fin r × Fin n) ℂ)
    (G : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF (∑ i ∈ s, F i) G = ∑ i ∈ s, fockF (F i) G := by
  rw [fockF_eq_sum_coeff_factorial_of_support_subset (∑ i ∈ s, F i) G _ MvPolynomial.support_sum]
  rw [Finset.sum_congr rfl fun i hi => fockF_eq_sum_coeff_factorial_of_support_subset (F i) G (s.biUnion fun i => (F i).support)
    (Finset.subset_biUnion_of_mem (fun i => (F i).support) hi)]
  simp only [MvPolynomial.coeff_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Rewrite using `[fockF_eq_sum_coeff_factorial_of_support_subset (C c * F) G F.support ?_]`. Unfold `fockF`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_C_mul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `m hm`. Rewrite `hm` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul]`. Conclude with `MvPolynomial.mem_support_iff.2 (right_ne_zero_of_mul hm)`.
-/
private lemma fockF_C_mul_left (F G : MvPolynomial (Fin r × Fin n) ℂ) (c : ℂ) :
    fockF (C c * F) G = c * fockF F G := by
  rw [fockF_eq_sum_coeff_factorial_of_support_subset (C c * F) G F.support ?_]
  · unfold fockF
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_C_mul]
    ring
  · intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
    exact MvPolynomial.mem_support_iff.2 (right_ne_zero_of_mul hm)

/- English proof (translation)
Establish `hT` using `fock_pairing_initial_minor ι hι m f hR hW p hp f`. Establish `hterm : ∀ a : Fin p → κ, fockF (initMinor ℂ (ι ∘ a) hp * f) (initMinor ℂ (ι ∘ a) hp * f) = ∑ π : Equiv.Perm (Fin p), fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ (a ∘ π)) hp * f)`. Introduce `a`. Establish `e` using `xn_minor_sum ι hp a`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_mul, fockF_sum_left']`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, fockF_C_mul_left]`. Use `_ = ∑ π : Equiv.Perm (Fin p), fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ (a ∘ π)) hp * f) := by`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations.

Establish `e2 : initMinor ℂ (ι ∘ a) hp = C (xnSg π) * initMinor ℂ (ι ∘ (a ∘ π)) hp`. Rewrite using `[xn_minor_perm ι hp a π, ← mul_assoc, ← map_mul, xnSg_mul_self, map_one, one_mul]`. Rewrite using `[e2, mul_assoc, fockF_C_mul_right, xnSg_star, ← mul_assoc, xnSg_mul_self, one_mul]`. Establish `hperm : ∀ π : Equiv.Perm (Fin p), ∑ a : Fin p → κ, fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ (a ∘ π)) hp * f) = ∑ a : Fin p → κ, fockF (xnMono ι hp a * f) (initMinor ℂ (ι ∘ a) hp * f)`. Introduce `π`.

Conclude with `Fintype.sum_bijective (fun a : Fin p → κ => a ∘ π) ⟨fun x y h => by`. Use function extensionality and compare the values at `i`. Simplify using `using congrFun h (π.symm i),`. Use `fun b => ⟨b ∘ π.symm, by funext i; simp⟩⟩ _ _ fun a => rfl`. Rewrite using `[Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_comm, Finset.sum_congr rfl fun π _ => hperm π, hT, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]`.
-/
lemma xn_S (ι : κ → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : κ, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : κ, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (p : ℕ) (hp : p ≤ n) :
    ∑ a : Fin p → κ, fockF (initMinor ℂ (ι ∘ a) hp * f) (initMinor ℂ (ι ∘ a) hp * f) =
      (p.factorial : ℂ) * (((xnC (Fintype.card κ) m p : ℝ) : ℂ) * fockF f f) := by
  have hT := fock_pairing_initial_minor ι hι m f hR hW p hp f
  have hterm : ∀ a : Fin p → κ, fockF (initMinor ℂ (ι ∘ a) hp * f) (initMinor ℂ (ι ∘ a) hp * f) =
      ∑ π : Equiv.Perm (Fin p),
        fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ (a ∘ π)) hp * f) := by
    intro a
    have e := xn_minor_sum ι hp a
    calc fockF (initMinor ℂ (ι ∘ a) hp * f) (initMinor ℂ (ι ∘ a) hp * f)
        = fockF ((∑ π : Equiv.Perm (Fin p), C (xnSg π) * xnMono ι hp (a ∘ π)) * f)
            (initMinor ℂ (ι ∘ a) hp * f) := by rw [← e]
      _ = ∑ π : Equiv.Perm (Fin p),
            xnSg π * fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ a) hp * f) := by
          rw [Finset.sum_mul, fockF_sum_left']
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [mul_assoc, fockF_C_mul_left]
      _ = ∑ π : Equiv.Perm (Fin p),
            fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ (a ∘ π)) hp * f) := by
          refine Finset.sum_congr rfl fun π _ => ?_
          have e2 : initMinor ℂ (ι ∘ a) hp = C (xnSg π) * initMinor ℂ (ι ∘ (a ∘ π)) hp := by
            rw [xn_minor_perm ι hp a π, ← mul_assoc, ← map_mul, xnSg_mul_self, map_one, one_mul]
          rw [e2, mul_assoc, fockF_C_mul_right, xnSg_star, ← mul_assoc, xnSg_mul_self, one_mul]
  have hperm : ∀ π : Equiv.Perm (Fin p),
      ∑ a : Fin p → κ, fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ (a ∘ π)) hp * f) =
        ∑ a : Fin p → κ, fockF (xnMono ι hp a * f) (initMinor ℂ (ι ∘ a) hp * f) := by
    intro π
    exact Fintype.sum_bijective (fun a : Fin p → κ => a ∘ π)
      ⟨fun x y h => by
        funext i
        simpa using congrFun h (π.symm i),
       fun b => ⟨b ∘ π.symm, by funext i; simp⟩⟩ _ _ fun a => rfl
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_comm,
    Finset.sum_congr rfl fun π _ => hperm π, hT, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

def xnN {σ : Type*} (f : MvPolynomial σ ℂ) : ℝ := (fockF f f).re

/- English proof (translation)
Establish `key : ∀ (c : ℂ) (N : ℕ), 0 ≤ (c * star c * (N : ℂ)).re`. Introduce `c N`. Establish `hN : (0 : ℝ) ≤ N` using `Nat.cast_nonneg N`. Use `first`. Consider the case `(simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.natCast_re, Complex.natCast_im, Complex.mul_im]`.

Use polynomial arithmetic with `[sq_nonneg c.re, sq_nonneg c.im])`. Consider the case `(rw [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]`. Conclude with `mul_nonneg (Complex.normSq_nonneg _) hN)`. Unfold `xnN fockF`. Rewrite using `[Complex.re_sum]`.

Conclude with `Finset.sum_nonneg fun m _ => key _ _`.
-/
lemma xnN_nonneg {σ : Type*} (f : MvPolynomial σ ℂ) : 0 ≤ xnN f := by
  have key : ∀ (c : ℂ) (N : ℕ), 0 ≤ (c * star c * (N : ℂ)).re := by
    intro c N
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    first
    | (simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.natCast_re, Complex.natCast_im, Complex.mul_im]
       nlinarith [sq_nonneg c.re, sq_nonneg c.im])
    | (rw [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
        Complex.ofReal_re]
       exact mul_nonneg (Complex.normSq_nonneg _) hN)
  unfold xnN fockF
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun m _ => key _ _

/- English proof (translation)
Unfold `xnN fockF`. Establish `hc : xnSg π ≠ 0` using `fun h0 => by simpa [h0] using xnSg_mul_self π`. Rewrite using `[MvPolynomial.C_mul']`. Use `first`. Consider the case `rw [MvPolynomial.support_smul_eq hc]`.

Consider the case `rw [Finsupp.support_smul_eq hc]`. Use `congr 1`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul, star_mul', xnSg_star]`. Rewrite using `[show ∀ a x y N : ℂ, a * x * (a * y) * N = (a * a) * (x * y * N) from fun _ _ _ _ => by ring, xnSg_mul_self, one_mul]`.
-/
lemma xnN_sg {σ : Type*} {p : ℕ} (π : Equiv.Perm (Fin p)) (f : MvPolynomial σ ℂ) :
    xnN (C (xnSg π) * f) = xnN f := by
  unfold xnN fockF
  have hc : xnSg π ≠ 0 := fun h0 => by simpa [h0] using xnSg_mul_self π
  rw [MvPolynomial.C_mul']
  first
  | rw [MvPolynomial.support_smul_eq hc]
  | rw [Finsupp.support_smul_eq hc]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul', xnSg_star]
  rw [show ∀ a x y N : ℂ, a * x * (a * y) * N = (a * a) * (x * y * N) from fun _ _ _ _ => by ring,
    xnSg_mul_self, one_mul]

/- English proof (translation)
Establish `h` using `xn_S ι hι m f hR hW p hp`. Unfold `xnN`. Rewrite using `[← Complex.re_sum, h]`. Use `first`. Consider the case `(rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.re_ofReal_mul])`.

Consider the case `(simp [Complex.mul_re])`. Consider the case `(simp [Complex.mul_re]; ring)`.
-/
lemma xn_SR (ι : κ → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : κ, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : κ, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (p : ℕ) (hp : p ≤ n) :
    ∑ a : Fin p → κ, xnN (initMinor ℂ (ι ∘ a) hp * f) =
      (p.factorial : ℝ) * (xnC (Fintype.card κ) m p * xnN f) := by
  have h := xn_S ι hι m f hR hW p hp
  unfold xnN
  rw [← Complex.re_sum, h]
  first
  | (rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.re_ofReal_mul])
  | (simp [Complex.mul_re])
  | (simp [Complex.mul_re]; ring)

/- English proof (translation)
Rewrite using `[Finset.sum_image (by intro x _ y _ hxy; exact Equiv.ext fun i => hJ (congrFun hxy i))]`. Establish `e : ∀ π : Equiv.Perm (Fin p), xnN (initMinor ℂ (ι ∘ (J ∘ π)) hp * f) = xnN (initMinor ℂ (ι ∘ J) hp * f)`. Introduce `π`. Rewrite using `[xn_minor_perm ι hp J π, mul_assoc, xnN_sg]`. Simplify using `only [e, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]`.
-/
lemma xn_sum_perm (ι : κ → Fin r) (f : MvPolynomial (Fin r × Fin n) ℂ) (p : ℕ) (hp : p ≤ n)
    (J : Fin p → κ) (hJ : Function.Injective J) :
    ∑ a ∈ (Finset.univ : Finset (Equiv.Perm (Fin p))).image (fun π : Equiv.Perm (Fin p) => J ∘ π),
      xnN (initMinor ℂ (ι ∘ a) hp * f) = (p.factorial : ℝ) * xnN (initMinor ℂ (ι ∘ J) hp * f) := by
  rw [Finset.sum_image (by intro x _ y _ hxy; exact Equiv.ext fun i => hJ (congrFun hxy i))]
  have e : ∀ π : Equiv.Perm (Fin p), xnN (initMinor ℂ (ι ∘ (J ∘ π)) hp * f) =
      xnN (initMinor ℂ (ι ∘ J) hp * f) := by
    intro π
    rw [xn_minor_perm ι hp J π, mul_assoc, xnN_sg]
  simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/- English proof (translation)
Establish `h1` using `xn_SR ι hι m f hR hW p hp`. Establish `h2` using `xn_sum_perm ι f p hp J hJ`. Establish `h3 : ∑ a ∈ (Finset.univ : Finset (Equiv.Perm (Fin p))).image (fun π : Equiv.Perm (Fin p) => J ∘ π), xnN (initMinor ℂ (ι ∘ a) hp * f) ≤ ∑ a : Fin p → κ, xnN (initMinor ℂ (ι ∘ a) hp * f)` using `Finset.sum_le_univ_sum_of_nonneg fun a => xnN_nonneg _`. Rewrite `h3` using `[h1, h2]`. Conclude with `le_of_mul_le_mul_left h3 (by exact_mod_cast p.factorial_pos)`.
-/
lemma xn_U (ι : κ → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : κ, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : κ, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (p : ℕ) (hp : p ≤ n) (J : Fin p → κ) (hJ : Function.Injective J) :
    xnN (initMinor ℂ (ι ∘ J) hp * f) ≤ xnC (Fintype.card κ) m p * xnN f := by
  have h1 := xn_SR ι hι m f hR hW p hp
  have h2 := xn_sum_perm ι f p hp J hJ
  have h3 : ∑ a ∈ (Finset.univ : Finset (Equiv.Perm (Fin p))).image (fun π : Equiv.Perm (Fin p) => J ∘ π),
      xnN (initMinor ℂ (ι ∘ a) hp * f) ≤ ∑ a : Fin p → κ, xnN (initMinor ℂ (ι ∘ a) hp * f) :=
    Finset.sum_le_univ_sum_of_nonneg fun a => xnN_nonneg _
  rw [h1, h2] at h3
  exact le_of_mul_le_mul_left h3 (by exact_mod_cast p.factorial_pos)

/- English proof (translation)
Establish `h1` using `xn_SR ι hι m f hR hW p hp`. Rewrite `h1` using `[Fintype.card_fin]`. Establish `h2` using `xn_sum_perm ι f p hp id Function.injective_id`. Establish `h3 : ∑ a ∈ (Finset.univ : Finset (Equiv.Perm (Fin p))).image (fun π : Equiv.Perm (Fin p) => id ∘ π), xnN (initMinor ℂ (ι ∘ a) hp * f) = ∑ a : Fin p → Fin p, xnN (initMinor ℂ (ι ∘ a) hp * f)`. Use `Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_` and prove the remaining obligations.

Establish `hna : ¬ Function.Injective (ι ∘ a)`. Introduce `hinj`. Apply `ha` to reduce the goal to its premises. Use `Finset.mem_image.2 ⟨Equiv.ofBijective a (Finite.injective_iff_bijective.1 hinj.of_comp), Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression.

Rewrite using `[xn_minor_zero _ hp hna, zero_mul]`. Simplify using `[xnN, fockF]`. Rewrite `h1` using `[← h3, h2]`. Establish `hpos : (0 : ℝ) < p.factorial` using `by exact_mod_cast Nat.factorial_pos p`. Conclude with `mul_left_cancel₀ hpos.ne' h1`.
-/
lemma xn_L {p : ℕ} (ι : Fin p → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : Fin p, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : Fin p, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (hp : p ≤ n) :
    xnN (initMinor ℂ ι hp * f) = xnC p m p * xnN f := by
  have h1 := xn_SR ι hι m f hR hW p hp
  rw [Fintype.card_fin] at h1
  have h2 := xn_sum_perm ι f p hp id Function.injective_id
  have h3 : ∑ a ∈ (Finset.univ : Finset (Equiv.Perm (Fin p))).image (fun π : Equiv.Perm (Fin p) => id ∘ π),
      xnN (initMinor ℂ (ι ∘ a) hp * f) = ∑ a : Fin p → Fin p, xnN (initMinor ℂ (ι ∘ a) hp * f) := by
    refine Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_
    have hna : ¬ Function.Injective (ι ∘ a) := by
      intro hinj
      apply ha
      refine Finset.mem_image.2 ⟨Equiv.ofBijective a (Finite.injective_iff_bijective.1 hinj.of_comp),
        Finset.mem_univ _, ?_⟩
      rfl
    rw [xn_minor_zero _ hp hna, zero_mul]
    simp [xnN, fockF]
  rw [← h3, h2] at h1
  have hpos : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
  exact mul_left_cancel₀ hpos.ne' h1

end XiB

section XiC

variable {r n : ℕ}

/- English proof (translation)
Simplify using `only [MvPolynomial.pderiv_X, Pi.single_apply, mul_ite, mul_one, mul_zero]`. Take `⟨v1, v2⟩` from `v`. Distinguish the cases in `h : v2 = s`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`.
-/
lemma xn_E_X (t s : Fin n) (v : Fin r × Fin n) :
    ∑ b : Fin r, (X (b, t) : MvPolynomial (Fin r × Fin n) ℂ) * pderiv (b, s) (X v) =
      if v.2 = s then X (v.1, t) else 0 := by
  simp only [MvPolynomial.pderiv_X, Pi.single_apply, mul_ite, mul_one, mul_zero]
  obtain ⟨v1, v2⟩ := v
  by_cases h : v2 = s
  · subst h
    simp
  · simp [h]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on`. Use `next a =>`. Simplify using `[MvPolynomial.derivation_C]`. Use `next p q hp hq =>`. Simplify using `only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]`.

Use `next p v hp =>`. Establish `e` using `xn_E_X t s v`. Simplify using `only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, ← hp]`. Simplify using `only [ndE, MvPolynomial.mkDerivation_X]`. Rewrite using `[← e, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun b _ => by ring`.
-/
lemma xn_E_eq (t s : Fin n) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    ∑ b : Fin r, X (b, t) * pderiv (b, s) f = ndE ℂ r n t s f := by
  induction f using MvPolynomial.induction_on
  next a =>
    simp [MvPolynomial.derivation_C]
  next p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]
  next p v hp =>
    have e := xn_E_X t s v
    simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, ← hp]
    simp only [ndE, MvPolynomial.mkDerivation_X]
    rw [← e, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [ndEul, ndE, MvPolynomial.mkDerivation_X, colW]`. Take `⟨v1, v2⟩` from `v`. Distinguish the cases in `h : v2 = s`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Pi.single_apply, Ne.symm h]`.
-/
lemma xn_Eul_eq (s : Fin n) : ndEul ℂ r n s = ndE ℂ r n s s := by
  apply MvPolynomial.derivation_ext
  intro v
  simp only [ndEul, ndE, MvPolynomial.mkDerivation_X, colW]
  obtain ⟨v1, v2⟩ := v
  by_cases h : v2 = s
  · subst h
    simp
  · simp [h, Pi.single_apply, Ne.symm h]

/- English proof (translation)
Establish `hinv` using `(mem_dualWeyl_iff.1 hf).2 t s hts`. Use `set ε : MvPolynomial (Option (Fin r × Fin n)) ℂ →ₐ[ℂ] MvPolynomial (Fin r × Fin n) ℂ := aeval fun o => Option.elim o 0 X with hε`. Establish `hεX : ∀ o, ε (X o) = Option.elim o 0 X` using `fun o => by rw [hε, aeval_X]`. Establish `hεc : ∀ g, ε (colAddGen ℂ t s g) = g`. Introduce `g`.

Establish `hc : ε.comp (colAddGen ℂ (r` using `r) t s) = AlgHom.id ℂ _ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply, colAddGen, aeval_X]`. Apply the tactic sequence `split_ifs <;> simp [hεX]`.

Simplify using `using AlgHom.congr_fun hc g`. Establish `hXv : ∀ v : Fin r × Fin n, ε (pderiv none (colAddGen ℂ t s (X v))) = if v.2 = s then X (v.1, t) else 0`. Introduce `v`. Simplify using `only [colAddGen, aeval_X]`. Use `split_ifs`.

Simplify using `[Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, hεX]`. Simplify using `[MvPolynomial.pderiv_X, Pi.single_apply]`. Establish `hE : ∀ v : Fin r × Fin n, ndE ℂ r n t s (X v) = if v.2 = s then X (v.1, t) else 0` using `fun v => by simp only [ndE, MvPolynomial.mkDerivation_X]`. Establish `key : ∀ g, ε (pderiv none (colAddGen ℂ t s g)) = ndE ℂ r n t s g`. Introduce `g`.

Proceed by induction on `g using MvPolynomial.induction_on`. Use `next a => simp [MvPolynomial.derivation_C]`. Use `next p q hp hq => simp only [map_add, hp, hq]`. Use `next p v hp =>`. Rewrite using `[map_mul (colAddGen ℂ (r := r) t s), Derivation.leibniz (pderiv (R := ℂ) none), smul_eq_mul, smul_eq_mul, map_add, map_mul ε, map_mul ε, hp, hεc, hεc, hXv, Derivation.leibniz (ndE ℂ r n t s), smul_eq_mul, smul_eq_mul, hE]`.

Establish `hsupp : rename (some : Fin r × Fin n → Option (Fin r × Fin n)) f ∈ MvPolynomial.supported ℂ (Set.range (some : Fin r × Fin n → Option (Fin r × Fin n)))`. Rewrite using `[MvPolynomial.mem_supported]`. Introduce `o ho`. Take `⟨v, -, rfl⟩` from `Finset.mem_image.1 (MvPolynomial.vars_rename _ _ ho)`. Conclude with `⟨v, rfl⟩`.

Rewrite using `[xn_E_eq, ← key, hinv, xn_pderiv_supported _ none (by simp) _ hsupp, map_zero]`.
-/
lemma xn_hR {μ : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) ℂ} (hf : f ∈ dualWeyl ℂ r n μ)
    (t s : Fin n) (hts : t < s) : ∑ b : Fin r, X (b, t) * pderiv (b, s) f = 0 := by
  have hinv := (mem_dualWeyl_iff.1 hf).2 t s hts
  set ε : MvPolynomial (Option (Fin r × Fin n)) ℂ →ₐ[ℂ] MvPolynomial (Fin r × Fin n) ℂ :=
    aeval fun o => Option.elim o 0 X with hε
  have hεX : ∀ o, ε (X o) = Option.elim o 0 X := fun o => by rw [hε, aeval_X]
  have hεc : ∀ g, ε (colAddGen ℂ t s g) = g := by
    intro g
    have hc : ε.comp (colAddGen ℂ (r := r) t s) = AlgHom.id ℂ _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [AlgHom.comp_apply, AlgHom.id_apply, colAddGen, aeval_X]
      split_ifs <;> simp [hεX]
    simpa using AlgHom.congr_fun hc g
  have hXv : ∀ v : Fin r × Fin n, ε (pderiv none (colAddGen ℂ t s (X v))) =
      if v.2 = s then X (v.1, t) else 0 := by
    intro v
    simp only [colAddGen, aeval_X]
    split_ifs
    · simp [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, hεX]
    · simp [MvPolynomial.pderiv_X, Pi.single_apply]
  have hE : ∀ v : Fin r × Fin n, ndE ℂ r n t s (X v) = if v.2 = s then X (v.1, t) else 0 :=
    fun v => by simp only [ndE, MvPolynomial.mkDerivation_X]
  have key : ∀ g, ε (pderiv none (colAddGen ℂ t s g)) = ndE ℂ r n t s g := by
    intro g
    induction g using MvPolynomial.induction_on
    next a => simp [MvPolynomial.derivation_C]
    next p q hp hq => simp only [map_add, hp, hq]
    next p v hp =>
      rw [map_mul (colAddGen ℂ (r := r) t s), Derivation.leibniz (pderiv (R := ℂ) none), smul_eq_mul,
        smul_eq_mul, map_add, map_mul ε, map_mul ε, hp, hεc, hεc, hXv,
        Derivation.leibniz (ndE ℂ r n t s), smul_eq_mul, smul_eq_mul, hE]
  have hsupp : rename (some : Fin r × Fin n → Option (Fin r × Fin n)) f ∈
      MvPolynomial.supported ℂ (Set.range (some : Fin r × Fin n → Option (Fin r × Fin n))) := by
    rw [MvPolynomial.mem_supported]
    intro o ho
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ ho)
    exact ⟨v, rfl⟩
  rw [xn_E_eq, ← key, hinv, xn_pderiv_supported _ none (by simp) _ hsupp, map_zero]

/- English proof (translation)
Establish `hwh` using `(mem_dualWeyl_iff.1 hf).1`. Rewrite using `[xn_E_eq, ← xn_Eul_eq]`. Establish `hmono : ∀ (d : Fin r × Fin n →₀ ℕ) (c : ℂ), ndEul ℂ r n s (monomial d c) = C (((Finsupp.weight (colW r n) d) s : ℕ) : ℂ) * monomial d c`. Introduce `d c`. Proceed by induction on `d using Finsupp.induction`.

Use `next =>`. Rewrite using `[← MvPolynomial.C_apply, MvPolynomial.derivation_C]`. Simplify using the standard rewrite rules. Use `next v k d hv hk ih =>`. Take `⟨k', rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`.

Rewrite using `[MvPolynomial.monomial_single_add, Derivation.leibniz, ih, Derivation.leibniz_pow]`. Simplify using `only [ndEul, MvPolynomial.mkDerivation_X, map_add, Pi.add_apply, Nat.add_sub_cancel]`. Use `first`. Consider the case `rw [Finsupp.weight_single_index]`. Consider the case `rw [Finsupp.weight_single]`.

Simplify using `only [colW, smul_eq_mul, nsmul_eq_mul, Pi.smul_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_one, map_add, map_mul, map_natCast, map_one]`. Expand and normalize the polynomial expressions, which then agree. Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[map_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Rewrite using `[hmono, hwh (MvPolynomial.mem_support_iff.1 hd)]`.
-/
lemma xn_hW {μ : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) ℂ} (hf : f ∈ dualWeyl ℂ r n μ)
    (s : Fin n) : ∑ b : Fin r, X (b, s) * pderiv (b, s) f = C ((μ s : ℕ) : ℂ) * f := by
  have hwh := (mem_dualWeyl_iff.1 hf).1
  rw [xn_E_eq, ← xn_Eul_eq]
  have hmono : ∀ (d : Fin r × Fin n →₀ ℕ) (c : ℂ), ndEul ℂ r n s (monomial d c) =
      C (((Finsupp.weight (colW r n) d) s : ℕ) : ℂ) * monomial d c := by
    intro d c
    induction d using Finsupp.induction
    next =>
      rw [← MvPolynomial.C_apply, MvPolynomial.derivation_C]
      simp
    next v k d hv hk ih =>
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [MvPolynomial.monomial_single_add, Derivation.leibniz, ih, Derivation.leibniz_pow]
      simp only [ndEul, MvPolynomial.mkDerivation_X, map_add, Pi.add_apply, Nat.add_sub_cancel]
      first
      | rw [Finsupp.weight_single_index]
      | rw [Finsupp.weight_single]
      simp only [colW, smul_eq_mul, nsmul_eq_mul, Pi.smul_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
        map_add, map_mul, map_natCast, map_one]
      ring
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hmono, hwh (MvPolynomial.mem_support_iff.1 hd)]

/- English proof (translation)
Rewrite using `[← Finset.sum_image (s := Finset.univ) (g := Fin.castLE hk) (f := g) (by intro x _ y _ hxy; exact Fin.castLE_injective hk hxy)]`. Use `Finset.sum_subset (Finset.subset_univ _) ?_` and prove the remaining obligations. Introduce `b _ hb`. Apply `hg` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Conclude with `hb (Finset.mem_image.2 ⟨⟨b.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)`.
-/
lemma xn_sum_castLE {A : Type*} [AddCommMonoid A] {k : ℕ} (hk : k ≤ r) (g : Fin r → A)
    (hg : ∀ b : Fin r, k ≤ b.val → g b = 0) :
    ∑ b : Fin k, g (Fin.castLE hk b) = ∑ b : Fin r, g b := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := Fin.castLE hk) (f := g)
    (by intro x _ y _ hxy; exact Fin.castLE_injective hk hxy)]
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro b _ hb
  apply hg
  by_contra hlt
  push_neg at hlt
  exact hb (Finset.mem_image.2 ⟨⟨b.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/- English proof (translation)
Use `xn_sum_castLE hk (fun b => X (b, t) * pderiv (b, s) f) ?_` and prove the remaining obligations. Introduce `b hb`. Use `show X (b, t) * pderiv (b, s) f = 0`. Rewrite using `[xn_pderiv_supported _ (b, s) (by intro h; simp only [Set.mem_setOf_eq] at h; omega) f hs, mul_zero]`.
-/
lemma xn_sum_rows {k : ℕ} (hk : k ≤ r) {f : MvPolynomial (Fin r × Fin n) ℂ}
    (hs : f ∈ supported ℂ {v : Fin r × Fin n | v.1.val < k}) (t s : Fin n) :
    ∑ b : Fin k, X (Fin.castLE hk b, t) * pderiv (Fin.castLE hk b, s) f =
      ∑ b : Fin r, X (b, t) * pderiv (b, s) f := by
  refine xn_sum_castLE hk (fun b => X (b, t) * pderiv (b, s) f) ?_
  intro b hb
  show X (b, t) * pderiv (b, s) f = 0
  rw [xn_pderiv_supported _ (b, s) (by intro h; simp only [Set.mem_setOf_eq] at h; omega) f hs, mul_zero]

end XiC

section XiD

def xnT (μ : ℕ → ℕ) (i j : ℕ) : ℝ :=
  if i < j then ((μ i : ℝ) - μ j + j - i) / ((j : ℝ) - i) else 1

def xnW (N : ℕ) (μ : ℕ → ℕ) : ℝ := ∏ i ∈ Finset.range N, ∏ j ∈ Finset.range N, xnT μ i j

def xnAdd (μ : ℕ → ℕ) (p : ℕ) : ℕ → ℕ := fun j => μ j + if j < p then 1 else 0

/- English proof (translation)
Establish `hlt : ∀ j, j < p → xnT (xnAdd μ p) i j = xnT μ i j`. Introduce `j hj`. Simplify using `only [xnT, xnAdd, if_pos hi, if_pos hj]`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`. Take `⟨d, rfl⟩ : ∃ d, m = p + d` from `⟨m - p, by omega⟩`.

Use `clear hm`. Proceed by induction on `d with`. Consider the case `zero`. Simplify using `only [Nat.add_zero]`. Rewrite using `[Finset.prod_congr rfl fun j hj => hlt j (Finset.mem_range.1 hj)]`.

Consider the case `succ d ih`. Establish `hμ : μ (p + d) = 0` using `h0 _ (by omega)`. Establish `h1 : i < p + d` using `by omega`. Establish `h2 : ¬ (p + d < p)` using `by omega`. Establish `e1 : xnT (xnAdd μ p) i (p + d) = ((μ i : ℝ) + 1 + ((p : ℝ) + d) - i) / (((p : ℝ) + d) - i)`.

Simplify using `only [xnT, xnAdd, if_pos h1, if_pos hi, if_neg h2, hμ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : xnT μ i (p + d) = ((μ i : ℝ) + ((p : ℝ) + d) - i) / (((p : ℝ) + d) - i)`. Simplify using `only [xnT, if_pos h1, hμ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← Nat.add_assoc, Finset.prod_range_succ, Finset.prod_range_succ, e1, e2]`. Move the coercions through the operations in `at ih ⊢`. Take the linear combination `(((μ i : ℝ) + 1 + ((p : ℝ) + d) - i) / (((p : ℝ) + d) - i)) * ih`.
-/
lemma xn_R (μ : ℕ → ℕ) (p i : ℕ) (hi : i < p) (h0 : ∀ j, p ≤ j → μ j = 0) (m : ℕ) (hm : p ≤ m) :
    (∏ j ∈ Finset.range m, xnT (xnAdd μ p) i j) * ((p : ℝ) - i + μ i) =
      (∏ j ∈ Finset.range m, xnT μ i j) * ((m : ℝ) - i + μ i) := by
  have hlt : ∀ j, j < p → xnT (xnAdd μ p) i j = xnT μ i j := by
    intro j hj
    simp only [xnT, xnAdd, if_pos hi, if_pos hj]
    split_ifs <;> push_cast <;> ring
  obtain ⟨d, rfl⟩ : ∃ d, m = p + d := ⟨m - p, by omega⟩
  clear hm
  induction d with
  | zero =>
    simp only [Nat.add_zero]
    rw [Finset.prod_congr rfl fun j hj => hlt j (Finset.mem_range.1 hj)]
  | succ d ih =>
    have hμ : μ (p + d) = 0 := h0 _ (by omega)
    have h1 : i < p + d := by omega
    have h2 : ¬ (p + d < p) := by omega
    have e1 : xnT (xnAdd μ p) i (p + d) =
        ((μ i : ℝ) + 1 + ((p : ℝ) + d) - i) / (((p : ℝ) + d) - i) := by
      simp only [xnT, xnAdd, if_pos h1, if_pos hi, if_neg h2, hμ]
      push_cast
      ring
    have e2 : xnT μ i (p + d) = ((μ i : ℝ) + ((p : ℝ) + d) - i) / (((p : ℝ) + d) - i) := by
      simp only [xnT, if_pos h1, hμ]
      push_cast
      ring
    rw [← Nat.add_assoc, Finset.prod_range_succ, Finset.prod_range_succ, e1, e2]
    push_cast at ih ⊢
    linear_combination (((μ i : ℝ) + 1 + ((p : ℝ) + d) - i) / (((p : ℝ) + d) - i)) * ih

/- English proof (translation)
Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h1 : ¬ i < p` using `by omega`. Distinguish the cases in `hij : i < j`. Establish `h2 : ¬ j < p` using `by omega`. Simplify using `only [xnT, xnAdd, if_pos hij, if_neg h1, if_neg h2, Nat.add_zero]`.

Simplify using `only [xnT, if_neg hij]`.
-/
lemma xn_R' (μ : ℕ → ℕ) (p i : ℕ) (hi : p ≤ i) (m : ℕ) :
    (∏ j ∈ Finset.range m, xnT (xnAdd μ p) i j) = ∏ j ∈ Finset.range m, xnT μ i j := by
  refine Finset.prod_congr rfl fun j _ => ?_
  have h1 : ¬ i < p := by omega
  by_cases hij : i < j
  · have h2 : ¬ j < p := by omega
    simp only [xnT, xnAdd, if_pos hij, if_neg h1, if_neg h2, Nat.add_zero]
  · simp only [xnT, if_neg hij]

/- English proof (translation)
Unfold `xnC`. Rewrite using `[← Finset.prod_filter]`. Use `congr 1`. Use extensionality with `i`. Simplify using `only [Finset.mem_range, Finset.mem_filter]`.

Use linear arithmetic over natural numbers and integers.
-/
lemma xnC_ite (M : ℕ) (m : ℕ → ℕ) (p N : ℕ) (hp : p ≤ N) :
    xnC M m p = ∏ i ∈ Finset.range N, if i < p then ((M : ℝ) - i + m i) else 1 := by
  unfold xnC
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/- English proof (translation)
Rewrite using `[xnC_ite p μ p N hp, xnC_ite N μ p N hp]`. Unfold `xnW`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i < p`.

Simplify using `only [if_pos hi]`. Conclude with `xn_R μ p i hi h0 N hp`. Simplify using `only [if_neg hi, mul_one]`. Conclude with `xn_R' μ p i (by omega) N`.
-/
lemma xn_W_ratio (N : ℕ) (μ : ℕ → ℕ) (p : ℕ) (hp : p ≤ N) (h0 : ∀ j, p ≤ j → μ j = 0) :
    xnW N (xnAdd μ p) * xnC p μ p = xnW N μ * xnC N μ p := by
  rw [xnC_ite p μ p N hp, xnC_ite N μ p N hp]
  unfold xnW
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i < p
  · simp only [if_pos hi]
    exact xn_R μ p i hi h0 N hp
  · simp only [if_neg hi, mul_one]
    exact xn_R' μ p i (by omega) N

/- English proof (translation)
Unfold `xnW xnT`. Use `Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Establish `hij : (i : ℝ) < j` using `by exact_mod_cast h`. Rewrite using `[div_eq_one_iff_eq (by linarith)]`.

Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
lemma xnW_zero (N : ℕ) : xnW N (fun _ => 0) = 1 := by
  unfold xnW xnT
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  split_ifs with h
  · have hij : (i : ℝ) < j := by exact_mod_cast h
    rw [div_eq_one_iff_eq (by linarith)]
    simp
  · rfl

/- English proof (translation)
Unfold `weylProd xnW`. Rewrite using `[Finset.prod_filter, Fintype.prod_prod_type]`. Simplify using `only [Finset.prod_range]`. Use `Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [xnT, Fin.lt_iff_val_lt_val]`.

Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.
-/
lemma xnW_weylProd (n : ℕ) (μ : ℕ → ℕ) :
    weylProd (fun a : Fin (n + 1) => ((μ a.val : ℕ) : ℤ)) = xnW (n + 1) μ := by
  unfold weylProd xnW
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  simp only [Finset.prod_range]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  simp only [xnT, Fin.lt_iff_val_lt_val]
  split_ifs <;> push_cast <;> ring

/- English proof (translation)
Unfold `xnC`. Use `Finset.prod_nonneg fun q hq => ?_` and prove the remaining obligations. Establish `hq' : q < p` using `Finset.mem_range.1 hq`. Establish `h1 : (q : ℝ) ≤ M` using `by exact_mod_cast (by omega : q ≤ M)`. Establish `h2 : (0 : ℝ) ≤ m q` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma xnC_nonneg (M : ℕ) (m : ℕ → ℕ) (p : ℕ) (hp : p ≤ M) : 0 ≤ xnC M m p := by
  unfold xnC
  refine Finset.prod_nonneg fun q hq => ?_
  have hq' : q < p := Finset.mem_range.1 hq
  have h1 : (q : ℝ) ≤ M := by exact_mod_cast (by omega : q ≤ M)
  have h2 : (0 : ℝ) ≤ m q := Nat.cast_nonneg _
  linarith

end XiD

section XiE

variable {r n : ℕ}

structure xnInv (k : ℕ) (μ : ℕ → ℕ) (x h : MvPolynomial (Fin r × Fin n) ℂ) : Prop where
  supp : ∀ q, k ≤ q → μ q = 0
  xm : x ∈ dualWeyl ℂ r n (fun q => μ q.val)
  hm : h ∈ dualWeyl ℂ r n (fun q => μ q.val)
  hs : h ∈ supported ℂ {v : Fin r × Fin n | v.1.val < k}
  le : xnN x ≤ xnW r μ * xnN h

/- English proof (translation)
Substitute `e1` using the available equality. Substitute `e2` using the available equality. Substitute `e3` using the available equality. Conclude with `H`.
-/
lemma xnInv_congr {k : ℕ} {μ μ' : ℕ → ℕ} {x x' h h' : MvPolynomial (Fin r × Fin n) ℂ}
    (H : xnInv k μ x h) (e1 : μ = μ') (e2 : x = x') (e3 : h = h') : xnInv k μ' x' h' := by
  subst e1
  subst e2
  subst e3
  exact H

/- English proof (translation)
Establish `h1 : (1 : MvPolynomial (Fin r × Fin n) ℂ) ∈ dualWeyl ℂ r n (fun q => (fun _ => 0) q.val)` using `one_mem_dualWeyl`. Conclude with `⟨fun q _ => rfl, h1, h1, one_mem _, le_of_eq (by rw [xnW_zero, one_mul])⟩`.
-/
lemma xnInv_zero : xnInv 0 (fun _ => 0) (1 : MvPolynomial (Fin r × Fin n) ℂ) 1 := by
  have h1 : (1 : MvPolynomial (Fin r × Fin n) ℂ) ∈ dualWeyl ℂ r n (fun q => (fun _ => 0) q.val) :=
    one_mem_dualWeyl
  exact ⟨fun q _ => rfl, h1, h1, one_mem _, le_of_eq (by rw [xnW_zero, one_mul])⟩

/- English proof (translation)
Conclude with `{ supp := fun q hq => H.supp q (by omega), xm := H.xm, hm := H.hm, hs := MvPolynomial.supported_mono (fun v hv => by simp only [Set.mem_setOf_eq] at hv ⊢; omega) H.hs, le := H.le }`.
-/
lemma xnInv_mono {k : ℕ} {μ : ℕ → ℕ} {x h : MvPolynomial (Fin r × Fin n) ℂ} (H : xnInv k μ x h) :
    xnInv (k + 1) μ x h := by
  exact { supp := fun q hq => H.supp q (by omega), xm := H.xm, hm := H.hm,
          hs := MvPolynomial.supported_mono
            (fun v hv => by simp only [Set.mem_setOf_eq] at hv ⊢; omega) H.hs,
          le := H.le }

/- English proof (translation)
Establish `hw : initW n k + (fun q : Fin n => μ q.val) = fun q : Fin n => xnAdd μ k q.val`. Use function extensionality and compare the values at `q`. Simplify using `only [initW, xnAdd, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> omega`. Establish `hL0 : lpMinor ℂ k hkr hk = initMinor ℂ (Fin.castLE hkr) hk` using `rfl`.

Establish `hLm : lpMinor ℂ k hkr hk ∈ dualWeyl ℂ r n (initW n k)`. Rewrite using `[hL0]`. Conclude with `initMinor_mem _ _`. Establish `hRx : ∀ t s : Fin n, t < s → ∑ b : Fin r, X ((id : Fin r → Fin r) b, t) * pderiv ((id : Fin r → Fin r) b, s) x = 0` using `fun t s hts => xn_hR H.xm t s hts`. Establish `hWx : ∀ s : Fin n, ∑ b : Fin r, X ((id : Fin r → Fin r) b, s) * pderiv ((id : Fin r → Fin r) b, s) x = C ((μ s.val : ℕ) : ℂ) * x` using `fun s => xn_hW H.xm s`.

Establish `hRh : ∀ t s : Fin n, t < s → ∑ b : Fin k, X (Fin.castLE hkr b, t) * pderiv (Fin.castLE hkr b, s) h = 0` using `fun t s hts => by`. Rewrite using `[xn_sum_rows hkr H.hs]`. Conclude with `xn_hR H.hm t s hts`. Establish `hWh : ∀ s : Fin n, ∑ b : Fin k, X (Fin.castLE hkr b, s) * pderiv (Fin.castLE hkr b, s) h = C ((μ s.val : ℕ) : ℂ) * h` using `fun s => by`. Rewrite using `[xn_sum_rows hkr H.hs]`.

Conclude with `xn_hW H.hm s`. Establish `hU` using `xn_U (id : Fin r → Fin r) Function.injective_id μ x hRx hWx k hk J hJ`. Rewrite `hU` using `[Fintype.card_fin]`. Establish `hLeq` using `xn_L (Fin.castLE hkr) (Fin.castLE_injective hkr) μ h hRh hWh hk`. Rewrite `hLeq` using `[← hL0]`.

Establish `hR` using `xn_W_ratio r μ k hkr H.supp`. Establish `hC` using `xnC_nonneg r μ k hkr`. Use `⟨fun q hq => ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [xnAdd, if_neg (show ¬ q < k by omega), Nat.add_zero]`. Conclude with `H.supp q hq`.

Rewrite using `[← hw]`. Conclude with `dualWeyl_mul (initMinor_mem J hk) H.xm`. Rewrite using `[← hw]`. Conclude with `dualWeyl_mul hLm H.hm`. Use `mul_mem ?_ H.hs` and prove the remaining obligations.

Rewrite using `[hL0]`. Unfold `initMinor`. Use `xn_det_supported _ _ fun i j => ?_` and prove the remaining obligations. Rewrite using `[Matrix.of_apply]`. Use `first`.

Consider the case `exact (MvPolynomial.X_mem_supported (R := ℂ)).2 (show (Fin.castLE hkr i).val < k from i.isLt)`. Consider the case `exact MvPolynomial.X_mem_supported.mpr (show (Fin.castLE hkr i).val < k from i.isLt)`. Rewrite using `[hLeq]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma xnInv_step {k : ℕ} {μ : ℕ → ℕ} {x h : MvPolynomial (Fin r × Fin n) ℂ} (H : xnInv k μ x h)
    (hk : k ≤ n) (hkr : k ≤ r) (J : Fin k → Fin r) (hJ : Function.Injective J) :
    xnInv k (xnAdd μ k) (initMinor ℂ J hk * x) (lpMinor ℂ k hkr hk * h) := by
  have hw : initW n k + (fun q : Fin n => μ q.val) = fun q : Fin n => xnAdd μ k q.val := by
    funext q
    simp only [initW, xnAdd, Pi.add_apply]
    split_ifs <;> omega
  have hL0 : lpMinor ℂ k hkr hk = initMinor ℂ (Fin.castLE hkr) hk := rfl
  have hLm : lpMinor ℂ k hkr hk ∈ dualWeyl ℂ r n (initW n k) := by
    rw [hL0]
    exact initMinor_mem _ _
  have hRx : ∀ t s : Fin n, t < s →
      ∑ b : Fin r, X ((id : Fin r → Fin r) b, t) * pderiv ((id : Fin r → Fin r) b, s) x = 0 :=
    fun t s hts => xn_hR H.xm t s hts
  have hWx : ∀ s : Fin n, ∑ b : Fin r, X ((id : Fin r → Fin r) b, s) *
      pderiv ((id : Fin r → Fin r) b, s) x = C ((μ s.val : ℕ) : ℂ) * x :=
    fun s => xn_hW H.xm s
  have hRh : ∀ t s : Fin n, t < s →
      ∑ b : Fin k, X (Fin.castLE hkr b, t) * pderiv (Fin.castLE hkr b, s) h = 0 :=
    fun t s hts => by
      rw [xn_sum_rows hkr H.hs]
      exact xn_hR H.hm t s hts
  have hWh : ∀ s : Fin n, ∑ b : Fin k, X (Fin.castLE hkr b, s) * pderiv (Fin.castLE hkr b, s) h =
      C ((μ s.val : ℕ) : ℂ) * h :=
    fun s => by
      rw [xn_sum_rows hkr H.hs]
      exact xn_hW H.hm s
  have hU := xn_U (id : Fin r → Fin r) Function.injective_id μ x hRx hWx k hk J hJ
  rw [Fintype.card_fin] at hU
  have hLeq := xn_L (Fin.castLE hkr) (Fin.castLE_injective hkr) μ h hRh hWh hk
  rw [← hL0] at hLeq
  have hR := xn_W_ratio r μ k hkr H.supp
  have hC := xnC_nonneg r μ k hkr
  refine ⟨fun q hq => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [xnAdd, if_neg (show ¬ q < k by omega), Nat.add_zero]
    exact H.supp q hq
  · rw [← hw]
    exact dualWeyl_mul (initMinor_mem J hk) H.xm
  · rw [← hw]
    exact dualWeyl_mul hLm H.hm
  · refine mul_mem ?_ H.hs
    rw [hL0]
    unfold initMinor
    refine xn_det_supported _ _ fun i j => ?_
    rw [Matrix.of_apply]
    first
    | exact (MvPolynomial.X_mem_supported (R := ℂ)).2 (show (Fin.castLE hkr i).val < k from i.isLt)
    | exact MvPolynomial.X_mem_supported.mpr (show (Fin.castLE hkr i).val < k from i.isLt)
  · rw [hLeq]
    calc xnN (initMinor ℂ J hk * x) ≤ xnC r μ k * xnN x := hU
      _ ≤ xnC r μ k * (xnW r μ * xnN h) := mul_le_mul_of_nonneg_left H.le hC
      _ = (xnW r μ * xnC r μ k) * xnN h := by ring
      _ = (xnW r (xnAdd μ k) * xnC k μ k) * xnN h := by rw [hR]
      _ = xnW r (xnAdd μ k) * (xnC k μ k * xnN h) := by ring

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero`. Use `xnInv_congr H ?_ ?_ ?_` and prove the remaining obligations. Apply the tactic sequence `funext q split_ifs <;> simp`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Consider the case `succ e ih`. Establish `H2` using `xnInv_step ih hk hkr J hJ`. Use `xnInv_congr H2 ?_ ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `q`.

Simplify using `only [xnAdd]`. Apply the tactic sequence `split_ifs <;> omega`. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
lemma xnInv_pow {k : ℕ} {μ : ℕ → ℕ} {x h : MvPolynomial (Fin r × Fin n) ℂ} (H : xnInv k μ x h)
    (hk : k ≤ n) (hkr : k ≤ r) (J : Fin k → Fin r) (hJ : Function.Injective J) (e : ℕ) :
    xnInv k (fun q => μ q + if q < k then e else 0) (initMinor ℂ J hk ^ e * x)
      (lpMinor ℂ k hkr hk ^ e * h) := by
  induction e with
  | zero =>
    refine xnInv_congr H ?_ ?_ ?_
    · funext q
      split_ifs <;> simp
    · simp
    · simp
  | succ e ih =>
    have H2 := xnInv_step ih hk hkr J hJ
    refine xnInv_congr H2 ?_ ?_ ?_
    · funext q
      simp only [xnAdd]
      split_ifs <;> omega
    · ring
    · ring

end XiE

section XiF

def xnLam {n : ℕ} (lam : Fin n → ℕ) (q : ℕ) : ℕ := if h : q < n then lam ⟨q, h⟩ else 0

/- English proof (translation)
Introduce `x y h`. Simplify using `only [rowsA, Fin.mk.injEq] at h`. Conclude with `Fin.ext h`.
-/
lemma xn_rowsA_inj {n : ℕ} (i : Fin n) : Function.Injective (rowsA i) := by
  intro x y h
  simp only [rowsA, Fin.mk.injEq] at h
  exact Fin.ext h

/- English proof (translation)
Introduce `x y h`. Establish `hx` using `x.isLt`. Establish `hy` using `y.isLt`. Establish `hi` using `i.isLt`. Simplify using `only [rowsB] at h`.

Apply `Fin.ext` to reduce the goal to its premises. Use `split_ifs at h`. Apply the tactic sequence `all_goals first`. Consider the case `(simpa using h)`. Consider the case `(have h' := congrArg Fin.val h`.

Simplify using `only [Fin.val_last, Fin.val_mk] at h'`. Use the proof step `omega)`. Consider the case `omega`.
-/
lemma xn_rowsB_inj {n : ℕ} (i : Fin n) : Function.Injective (rowsB i) := by
  intro x y h
  have hx := x.isLt
  have hy := y.isLt
  have hi := i.isLt
  simp only [rowsB] at h
  apply Fin.ext
  split_ifs at h
  all_goals first
    | (simpa using h)
    | (have h' := congrArg Fin.val h
       simp only [Fin.val_last, Fin.val_mk] at h'
       omega)
    | omega

/- English proof (translation)
Take `⟨h1, h2⟩` from `hI i`. Establish `hi` using `i.isLt`. Simplify using `only [lamZ, Fin.coe_castSucc, Fin.val_succ] at h1 h2`. Rewrite `h1` using `[dif_pos hi]`. Unfold `nuNext`.

Prove the components needed by the constructor for the conclusion. Use `split_ifs with hh`. Rewrite `h2` using `[dif_pos hh]`. Conclude with `h2` after adjusting the coercions. Conclude with `Nat.zero_le _`.

Conclude with `h1` after adjusting the coercions.
-/
lemma xn_interlace {n : ℕ} (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ)))
    (i : Fin n) : nuNext lam i ≤ sg i ∧ sg i ≤ lam i := by
  obtain ⟨h1, h2⟩ := hI i
  have hi := i.isLt
  simp only [lamZ, Fin.coe_castSucc, Fin.val_succ] at h1 h2
  rw [dif_pos hi] at h1
  unfold nuNext
  constructor
  · split_ifs with hh
    · rw [dif_pos hh] at h2
      exact_mod_cast h2
    · exact Nat.zero_le _
  · exact_mod_cast h1

/- English proof (translation)
Use `antitone_nat_of_succ_le fun q => ?_` and prove the remaining obligations. Unfold `xnLam`. Distinguish the cases in `h1 : q + 1 < n`. Establish `h0 : q < n` using `by omega`. Rewrite using `[dif_pos h1, dif_pos h0]`.

Take `⟨ha, hb⟩` from `xn_interlace lam sg hI ⟨q, h0⟩`. Unfold `nuNext at ha`. Rewrite `ha` using `[dif_pos h1]`. Conclude with `le_trans ha hb`. Rewrite using `[dif_neg h1]`.

Conclude with `Nat.zero_le _`.
-/
lemma xnLam_anti {n : ℕ} (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    Antitone (xnLam lam) := by
  refine antitone_nat_of_succ_le fun q => ?_
  unfold xnLam
  by_cases h1 : q + 1 < n
  · have h0 : q < n := by omega
    rw [dif_pos h1, dif_pos h0]
    obtain ⟨ha, hb⟩ := xn_interlace lam sg hI ⟨q, h0⟩
    unfold nuNext at ha
    rw [dif_pos h1] at ha
    exact le_trans ha hb
  · rw [dif_neg h1]
    exact Nat.zero_le _

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Use `xnInv_congr (xnInv_zero (r := n + 1) (n := n)) ?_ ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Use `xnLam_anti lam sg hI (Nat.zero_le q)` as an intermediate fact.

Use `show 0 = xnLam lam q - xnLam lam 0`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Establish `hkn : k < n` using `by omega`. Establish `H0` using `xnInv_mono (ih (by omega))`. Establish `H1` using `xnInv_pow H0 hk (by omega) (rowsA ⟨k, hkn⟩) (xn_rowsA_inj _) (sg ⟨k, hkn⟩ - nuNext lam ⟨k, hkn⟩)`. Establish `H2` using `xnInv_pow H1 hk (by omega) (rowsB ⟨k, hkn⟩) (xn_rowsB_inj _) (lam ⟨k, hkn⟩ - sg ⟨k, hkn⟩)`. Take `⟨i1, i2⟩` from `xn_interlace lam sg hI ⟨k, hkn⟩`.

Establish `hf : (Finset.univ.filter fun i : Fin n => i.val < k + 1) = insert ⟨k, hkn⟩ (Finset.univ.filter fun i : Fin n => i.val < k)`. Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `constructor <;> intro h <;> omega`. Establish `hnot : (⟨k, hkn⟩ : Fin n) ∉ (Finset.univ.filter fun i : Fin n => i.val < k)` using `by simp`.

Use `xnInv_congr H2 ?_ ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Establish `e1 : xnLam lam k = lam ⟨k, hkn⟩` using `by simp [xnLam, hkn]`. Establish `e2 : xnLam lam (k + 1) = nuNext lam ⟨k, hkn⟩`. Simplify using `only [xnLam, nuNext, Fin.val_mk]`.

Establish `a1` using `xnLam_anti lam sg hI (Nat.le_succ k)`. Distinguish the cases in `hq : q < k + 1`. Establish `a2` using `xnLam_anti lam sg hI (show q ≤ k by omega)`. Simplify using `only [if_pos hq]`. Use linear arithmetic over natural numbers and integers.

Establish `a2` using `xnLam_anti lam sg hI (show k + 1 ≤ q by omega)`. Simplify using `only [if_neg hq]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hf, Finset.prod_insert hnot]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hexp : (lam ⟨k, hkn⟩ - sg ⟨k, hkn⟩) + (sg ⟨k, hkn⟩ - nuNext lam ⟨k, hkn⟩) = lam ⟨k, hkn⟩ - nuNext lam ⟨k, hkn⟩` using `by omega`. Rewrite using `[hf, Finset.prod_insert hnot, ← mul_assoc, ← pow_add, hexp]`.
-/
lemma xn_stage (n : ℕ) (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ)))
    (k : ℕ) (hk : k ≤ n) :
    xnInv (r := n + 1) (n := n) k (fun q => xnLam lam q - xnLam lam k)
      (∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),
        (initMinor ℂ (rowsA i) (by omega : i.val + 1 ≤ n) ^ (sg i - nuNext lam i) *
          initMinor ℂ (rowsB i) (by omega : i.val + 1 ≤ n) ^ (lam i - sg i)))
      (∏ s ∈ Finset.univ.filter (fun s : Fin n => s.val < k),
        (lpMinor ℂ (s.val + 1) (by omega) (by omega)) ^ (lam s - nuNext lam s)) := by
  induction k with
  | zero =>
    refine xnInv_congr (xnInv_zero (r := n + 1) (n := n)) ?_ ?_ ?_
    · funext q
      have := xnLam_anti lam sg hI (Nat.zero_le q)
      show 0 = xnLam lam q - xnLam lam 0
      omega
    · simp
    · simp
  | succ k ih =>
    have hkn : k < n := by omega
    have H0 := xnInv_mono (ih (by omega))
    have H1 := xnInv_pow H0 hk (by omega) (rowsA ⟨k, hkn⟩) (xn_rowsA_inj _)
      (sg ⟨k, hkn⟩ - nuNext lam ⟨k, hkn⟩)
    have H2 := xnInv_pow H1 hk (by omega) (rowsB ⟨k, hkn⟩) (xn_rowsB_inj _)
      (lam ⟨k, hkn⟩ - sg ⟨k, hkn⟩)
    obtain ⟨i1, i2⟩ := xn_interlace lam sg hI ⟨k, hkn⟩
    have hf : (Finset.univ.filter fun i : Fin n => i.val < k + 1) =
        insert ⟨k, hkn⟩ (Finset.univ.filter fun i : Fin n => i.val < k) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff,
        Fin.val_mk]
      constructor <;> intro h <;> omega
    have hnot : (⟨k, hkn⟩ : Fin n) ∉ (Finset.univ.filter fun i : Fin n => i.val < k) := by simp
    refine xnInv_congr H2 ?_ ?_ ?_
    · funext q
      have e1 : xnLam lam k = lam ⟨k, hkn⟩ := by simp [xnLam, hkn]
      have e2 : xnLam lam (k + 1) = nuNext lam ⟨k, hkn⟩ := by
        simp only [xnLam, nuNext, Fin.val_mk]
      have a1 := xnLam_anti lam sg hI (Nat.le_succ k)
      by_cases hq : q < k + 1
      · have a2 := xnLam_anti lam sg hI (show q ≤ k by omega)
        simp only [if_pos hq]
        omega
      · have a2 := xnLam_anti lam sg hI (show k + 1 ≤ q by omega)
        simp only [if_neg hq]
        omega
    · rw [hf, Finset.prod_insert hnot]
      ring
    · have hexp : (lam ⟨k, hkn⟩ - sg ⟨k, hkn⟩) + (sg ⟨k, hkn⟩ - nuNext lam ⟨k, hkn⟩) =
          lam ⟨k, hkn⟩ - nuNext lam ⟨k, hkn⟩ := by omega
      rw [hf, Finset.prod_insert hnot, ← mul_assoc, ← pow_add, hexp]

end XiF

/- English proof (translation)
Unfold `XiNorm`. Introduce `n lam sg hI`. Establish `H` using `xn_stage n lam sg hI n le_rfl`. Establish `hμ : (fun q => xnLam lam q - xnLam lam n) = xnLam lam`. Use function extensionality and compare the values at `q`.

Establish `h0 : xnLam lam n = 0` using `by simp [xnLam]`. Rewrite using `[h0, Nat.sub_zero]`. Establish `hx : (∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < n), (initMinor ℂ (rowsA i) (by omega : i.val + 1 ≤ n) ^ (sg i - nuNext lam i) * initMinor ℂ (rowsB i) (by omega : i.val + 1 ≤ n) ^ (lam i - sg i))) = xiB ℂ lam sg`. Unfold `xiB`. Rewrite using `[Finset.filter_true_of_mem fun i _ => i.isLt]`.

Establish `hh : (∏ s ∈ Finset.univ.filter (fun s : Fin n => s.val < n), (lpMinor ℂ (r` using `n + 1) (n := n) (s.val + 1) (by omega) (by omega)) ^ (lam s - nuNext lam s)) = hw ℂ (Nat.le_succ n) lam := by`. Unfold `hw`. Rewrite using `[Finset.filter_true_of_mem fun i _ => i.isLt]`. Establish `hW : weylProd (lamZ lam) = xnW (n + 1) (xnLam lam)`. Rewrite using `[← xnW_weylProd]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `only [lamZ, xnLam]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `H2` using `H.le`.

Rewrite `H2` using `[hμ, hx, hh]`. Unfold `xnN at H2`. Rewrite using `[hW]`. Conclude with `H2`.
-/
theorem xi_norm_bound : XiNorm := by
  unfold XiNorm
  intro n lam sg hI
  have H := xn_stage n lam sg hI n le_rfl
  have hμ : (fun q => xnLam lam q - xnLam lam n) = xnLam lam := by
    funext q
    have h0 : xnLam lam n = 0 := by simp [xnLam]
    rw [h0, Nat.sub_zero]
  have hx : (∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < n),
      (initMinor ℂ (rowsA i) (by omega : i.val + 1 ≤ n) ^ (sg i - nuNext lam i) *
        initMinor ℂ (rowsB i) (by omega : i.val + 1 ≤ n) ^ (lam i - sg i))) = xiB ℂ lam sg := by
    unfold xiB
    rw [Finset.filter_true_of_mem fun i _ => i.isLt]
  have hh : (∏ s ∈ Finset.univ.filter (fun s : Fin n => s.val < n),
      (lpMinor ℂ (r := n + 1) (n := n) (s.val + 1) (by omega) (by omega)) ^ (lam s - nuNext lam s)) =
      hw ℂ (Nat.le_succ n) lam := by
    unfold hw
    rw [Finset.filter_true_of_mem fun i _ => i.isLt]
  have hW : weylProd (lamZ lam) = xnW (n + 1) (xnLam lam) := by
    rw [← xnW_weylProd]
    congr 1
    funext a
    simp only [lamZ, xnLam]
    split_ifs <;> simp
  have H2 := H.le
  rw [hμ, hx, hh] at H2
  unfold xnN at H2
  rw [hW]
  exact H2

end Formalism.BranchingDeterminantCap
