import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace WeylCellRankOne

variable {L : Type} [Field L] {n : ℕ}

/- English proof (translation)
Establish `hi` using `hy.inv`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (s j)]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (s i)]`. Introduce `b _ hb`. Rewrite using `[hi i b (by intro h; apply hb; rw [h]; simp), zero_mul]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[hy b j hb, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem conj_apply {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y)
    (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    ((y⁻¹ : GL (Fin n) L) * M * (y : Matrix (Fin n) (Fin n) L)) i j =
      ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * M (s i) (s j) *
        (y : Matrix (Fin n) (Fin n) L) (s j) j := by
  have hi := hy.inv
  rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
    · intro b _ hb
      rw [hi i b (by intro h; apply hb; rw [h]; simp), zero_mul]
    · simp
  · intro b _ hb; rw [hy b j hb, mul_zero]
  · simp

/- English proof (translation)
Establish `h` using `conj_apply hy 1 i i`. Rewrite `h` using `[Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq, Matrix.one_apply_eq, mul_one]`. Conclude with `h.symm`.
-/
theorem diag_mul_eq_one {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y) (i : Fin n) :
    ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) *
        (y : Matrix (Fin n) (Fin n) L) (s i) i = 1 := by
  have h := conj_apply hy 1 i i
  rw [Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq,
    Matrix.one_apply_eq, mul_one] at h
  exact h.symm

/- English proof (translation)
Rewrite `hpq`, the goal using `[Fin.lt_def]`. Establish `ha : ∀ x : Fin n, x = a ↔ x.val = a.val` using `fun x => Fin.ext_iff`. Establish `hb : ∀ x : Fin n, x = b ↔ x.val = b.val` using `fun x => Fin.ext_iff`. Simplify using `only [Equiv.swap_apply_def]`. Rewrite `hne` using `[ha, hb]`.

Apply the tactic sequence `split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp only [ha, hb] at * <;> omega`.
-/
theorem swap_lt {a b p q : Fin n} (hab : b.val = a.val + 1) (hpq : p < q) (hne : ¬ (p = a ∧ q = b)) :
    Equiv.swap a b p < Equiv.swap a b q := by
  rw [Fin.lt_def] at hpq ⊢
  have ha : ∀ x : Fin n, x = a ↔ x.val = a.val := fun x => Fin.ext_iff
  have hb : ∀ x : Fin n, x = b ↔ x.val = b.val := fun x => Fin.ext_iff
  simp only [Equiv.swap_apply_def]
  rw [ha, hb] at hne
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp only [ha, hb] at * <;> omega

/- English proof (translation)
Use `set s := Equiv.swap a b with hs`. Establish `hd` using `diag_mul_eq_one hy`. Establish `hne1 : ∀ i, ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) ≠ 0` using `fun i h => by have := hd i; rw [h, zero_mul] at this; exact zero_ne_one this`. Establish `hne2 : ∀ i, (y : Matrix (Fin n) (Fin n) L) (s i) i ≠ 0` using `fun i h => by have := hd i; rw [h, mul_zero] at this; exact zero_ne_one this`. Establish `hconj : ∀ i j, ((y⁻¹ * u * y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * (u : Matrix (Fin n) (Fin n) L) (s i) (s j) * (y : Matrix (Fin n) (Fin n) L) (s j) j`.

Introduce `i j`. Rewrite using `[Units.val_mul, Units.val_mul]`. Conclude with `conj_apply hy _ i j`. Establish `hss : ∀ x, s (s x) = x` using `fun x => Equiv.swap_apply_self a b x`. Establish `hlt : a < b` using `by rw [Fin.lt_def]; omega`.

Rewrite using `[mem_cell, mem_unipB, mem_unipBLower]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hup, hdiag⟩, hlow, -⟩ i j hij`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Rewrite using `[Matrix.one_apply_ne h.ne]`.

Establish `h2` using `hlow (s i) (s j) (swap_lt hab h hij)`. Rewrite `h2` using `[hconj]`. Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases. Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases. Conclude with `absurd h4 (hne1 _)`.

Rewrite `h4` using `[hss, hss]`. Then use the resulting hypothesis. Conclude with `absurd h3 (hne2 _)`. Rewrite using `[Matrix.one_apply_eq]`. Conclude with `hdiag i`. Rewrite using `[Matrix.one_apply_ne h.ne']`.

Conclude with `hup i j h`. Introduce `h`. Establish `hdiag : ∀ i, (u : Matrix (Fin n) (Fin n) L) i i = 1` using `fun i => by`. Rewrite using `[h i i (fun hh => by rw [← hh.1, ← hh.2] at hlt; exact lt_irrefl _ hlt), Matrix.one_apply_eq]`. Use `⟨⟨fun i j hji => ?_, hdiag⟩, fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[h i j (fun hh => by rw [hh.1, hh.2] at hji; exact lt_asymm hji hlt), Matrix.one_apply_ne hji.ne']`. Rewrite using `[hconj, h (s i) (s j), Matrix.one_apply_ne, mul_zero, zero_mul]`. Introduce `he`. Conclude with `hij.ne (s.injective he)`. Introduce and unpack `⟨h1, h2⟩`.

Establish `e1 : i = b` using `by rw [← hss i, h1]; exact Equiv.swap_apply_left a b`. Establish `e2 : j = a` using `by rw [← hss j, h2]; exact Equiv.swap_apply_right a b`. Rewrite `hij` using `[e1, e2]`. Conclude with `lt_asymm hij hlt`. Rewrite using `[hconj, hdiag, mul_one]`.

Conclude with `hd i`.
-/
theorem mem_cell_swap {a b : Fin n} (hab : b.val = a.val + 1) {y : GL (Fin n) L}
    (hy : IsWeylRep (Equiv.swap a b) y) (u : GL (Fin n) L) :
    u ∈ cell y ↔ ∀ i j, ¬ (i = a ∧ j = b) →
      (u : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j := by
  set s := Equiv.swap a b with hs
  have hd := diag_mul_eq_one hy
  have hne1 : ∀ i, ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) ≠ 0 :=
    fun i h => by have := hd i; rw [h, zero_mul] at this; exact zero_ne_one this
  have hne2 : ∀ i, (y : Matrix (Fin n) (Fin n) L) (s i) i ≠ 0 :=
    fun i h => by have := hd i; rw [h, mul_zero] at this; exact zero_ne_one this
  have hconj : ∀ i j, ((y⁻¹ * u * y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * (u : Matrix (Fin n) (Fin n) L) (s i) (s j) *
        (y : Matrix (Fin n) (Fin n) L) (s j) j := by
    intro i j; rw [Units.val_mul, Units.val_mul]; exact conj_apply hy _ i j
  have hss : ∀ x, s (s x) = x := fun x => Equiv.swap_apply_self a b x
  have hlt : a < b := by rw [Fin.lt_def]; omega
  rw [mem_cell, mem_unipB, mem_unipBLower]
  constructor
  · rintro ⟨⟨hup, hdiag⟩, hlow, -⟩ i j hij
    rcases lt_trichotomy i j with h | rfl | h
    · rw [Matrix.one_apply_ne h.ne]
      have h2 := hlow (s i) (s j) (swap_lt hab h hij)
      rw [hconj] at h2
      rcases mul_eq_zero.1 h2 with h3 | h3
      · rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd h4 (hne1 _)
        · rwa [hss, hss] at h4
      · exact absurd h3 (hne2 _)
    · rw [Matrix.one_apply_eq]; exact hdiag i
    · rw [Matrix.one_apply_ne h.ne']; exact hup i j h
  · intro h
    have hdiag : ∀ i, (u : Matrix (Fin n) (Fin n) L) i i = 1 := fun i => by
      rw [h i i (fun hh => by rw [← hh.1, ← hh.2] at hlt; exact lt_irrefl _ hlt), Matrix.one_apply_eq]
    refine ⟨⟨fun i j hji => ?_, hdiag⟩, fun i j hij => ?_, fun i => ?_⟩
    · rw [h i j (fun hh => by rw [hh.1, hh.2] at hji; exact lt_asymm hji hlt), Matrix.one_apply_ne hji.ne']
    · rw [hconj, h (s i) (s j), Matrix.one_apply_ne, mul_zero, zero_mul]
      · intro he; exact hij.ne (s.injective he)
      · rintro ⟨h1, h2⟩
        have e1 : i = b := by rw [← hss i, h1]; exact Equiv.swap_apply_left a b
        have e2 : j = a := by rw [← hss j, h2]; exact Equiv.swap_apply_right a b
        rw [e1, e2] at hij; exact lt_asymm hij hlt
    · rw [hconj, hdiag, mul_one]; exact hd i

end WeylCellRankOne

open WeylCellRankOne in
/- English proof (translation)
Introduce `L _ _ σ n k hk he y hy u`. Establish `hs : simpleU k = Equiv.swap (lo k) (lo k).rev` using `by simp [simpleU, hk]`. Rewrite `hy` using `[hs]`. Establish `hab : ((lo k).rev).val = (lo k).val + 1`. Take `⟨m, rfl⟩` from `he`.

Establish `hk2` using `k.isLt`. Simplify using `only [Fin.val_rev, lo, Fin.coe_castLE]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[cellU, Subgroup.mem_subgroupOf]`. Conclude with `mem_cell_swap hab hy (u : GL (Fin n) L)`.
-/
theorem cellU_rankOne_shape : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n → ∀ (y : GU σ n),
    IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (u : GU σ n),
    u ∈ cellU y ↔ ∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j := by
  intro L _ _ σ n k hk he y hy u
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  rw [hs] at hy
  have hab : ((lo k).rev).val = (lo k).val + 1 := by
    obtain ⟨m, rfl⟩ := he
    have hk2 := k.isLt
    simp only [Fin.val_rev, lo, Fin.coe_castLE]
    omega
  rw [cellU, Subgroup.mem_subgroupOf]
  exact mem_cell_swap hab hy (u : GL (Fin n) L)

end GlobalTheory
