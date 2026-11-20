import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum

open Formalism.L2.Theta

namespace GlobalTheory.SignedHC.GridData

/- English proof (translation)
Take `⟨-, q, hq, rfl⟩` from `h`. Conclude with `⟨(q a, ε a), Finset.mem_image_of_mem _ (Finset.mem_univ a), hq a, rfl⟩`.
-/
theorem isEnum_mem {n : ℕ} {S : Finset (ℚ × Bool)} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε)
    (a : Fin n) : ∃ x ∈ S, lam a = (x.1 : ℝ) ∧ ε a = x.2 := by
  obtain ⟨-, q, hq, rfl⟩ := h
  exact ⟨(q a, ε a), Finset.mem_image_of_mem _ (Finset.mem_univ a), hq a, rfl⟩

variable {G : GridData}

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro i hi hk; exact hv i hi (by omega)`. Consider the case `succ d ih`. Introduce `i hi hk`.

Establish `h1` using `ih i hi (by omega)`. Establish `h2` using `hv (i + d + 1) (by omega) (by omega)`. Rewrite using `[show i + (d + 1) + 1 = i + d + 1 + 1 by omega]`. Use linear arithmetic over natural numbers and integers.
-/
theorem v_add_two_le_of_gaps (hv : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) :
    ∀ d i, 2 ≤ i → i + d + 1 ≤ G.k → G.v (i + d + 1) + 2 ≤ G.v i := by
  intro d
  induction d with
  | zero => intro i hi hk; exact hv i hi (by omega)
  | succ d ih =>
    intro i hi hk
    have h1 := ih i hi (by omega)
    have h2 := hv (i + d + 1) (by omega) (by omega)
    rw [show i + (d + 1) + 1 = i + d + 1 + 1 by omega]
    omega

/- English proof (translation)
Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt hij`. Conclude with `v_add_two_le_of_gaps hv d i hi hjk`. Use linear arithmetic over natural numbers and integers. Use `G.v_anti j i hj hij hik` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem v_sep_of_gaps (hv : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) {i j : ℕ} (hi : 2 ≤ i) (hik : i ≤ G.k)
    (hj : 2 ≤ j) (hjk : j ≤ G.k) (h : G.v j < G.v i) : G.v j + 2 ≤ G.v i := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    exact v_add_two_le_of_gaps hv d i hi hjk
  · omega
  · have := G.v_anti j i hj hij hik; omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Break down `hik.eq_or_lt with rfl | h` into its components or cases. Conclude with `le_rfl`. Conclude with `(G.v_anti i G.k hi h le_rfl).le`. Break down `hi.eq_or_lt with rfl | h` into its components or cases.

Conclude with `le_rfl`. Conclude with `(G.v_anti 2 i le_rfl h hik).le`.
-/
theorem v_le_v_two {i : ℕ} (hi : 2 ≤ i) (hik : i ≤ G.k) : G.v G.k ≤ G.v i ∧ G.v i ≤ G.v 2 := by
  constructor
  · rcases hik.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (G.v_anti i G.k hi h le_rfl).le
  · rcases hi.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (G.v_anti 2 i le_rfl h hik).le

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro l hl hm; exact hb l hl (by omega)`. Consider the case `succ d ih`. Introduce `l hl hm`.

Establish `h1` using `ih l hl (by omega)`. Establish `h2` using `hb (l + d + 1) (by omega) (by omega)`. Rewrite using `[show l + (d + 1) + 1 = l + d + 1 + 1 by omega]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem b_add_le_of_gaps {H : ℝ} (hH : 0 ≤ H) (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) :
    ∀ d l, 1 ≤ l → l + d + 1 ≤ G.m → (G.b l : ℝ) + H ≤ G.b (l + d + 1) := by
  intro d
  induction d with
  | zero => intro l hl hm; exact hb l hl (by omega)
  | succ d ih =>
    intro l hl hm
    have h1 := ih l hl (by omega)
    have h2 := hb (l + d + 1) (by omega) (by omega)
    rw [show l + (d + 1) + 1 = l + d + 1 + 1 by omega]
    linarith

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt h`. Conclude with `b_add_le_of_gaps hH hb d l hl hlm'`.
-/
theorem b_sep_of_gaps {H : ℝ} (hH : 0 ≤ H) (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) {l l' : ℕ}
    (hl : 1 ≤ l) (hlm : l ≤ G.m) (hl' : 1 ≤ l') (hlm' : l' ≤ G.m) (h : l < l') : (G.b l : ℝ) + H ≤ G.b l' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
  exact b_add_le_of_gaps hH hb d l hl hlm'

/- English proof (translation)
Break down `lt_or_gt_of_ne h with h | h` into its components or cases. Use `b_sep_of_gaps hH hb hl hlm hl' hlm' h` as an intermediate fact. Rewrite using `[abs_sub_comm]; exact le_abs.2 (Or.inl (by linarith))`. Use `b_sep_of_gaps hH hb hl' hlm' hl hlm h` as an intermediate fact. Conclude with `le_abs.2 (Or.inl (by linarith))`.
-/
theorem b_abs_of_gaps {H : ℝ} (hH : 0 ≤ H) (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) {l l' : ℕ}
    (hl : 1 ≤ l) (hlm : l ≤ G.m) (hl' : 1 ≤ l') (hlm' : l' ≤ G.m) (h : l ≠ l') : H ≤ |(G.b l : ℝ) - G.b l'| := by
  rcases lt_or_gt_of_ne h with h | h
  · have := b_sep_of_gaps hH hb hl hlm hl' hlm' h
    rw [abs_sub_comm]; exact le_abs.2 (Or.inl (by linarith))
  · have := b_sep_of_gaps hH hb hl' hlm' hl hlm h
    exact le_abs.2 (Or.inl (by linarith))

/- English proof (translation)
Break down `hl.eq_or_lt with rfl | h` into its components or cases. Conclude with `le_rfl`. Conclude with `(G.b_mono 1 l le_rfl h hlm).le`.
-/
theorem b_one_le {l : ℕ} (hl : 1 ≤ l) (hlm : l ≤ G.m) : G.b 1 ≤ G.b l := by
  rcases hl.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (G.b_mono 1 l le_rfl h hlm).le

/- English proof (translation)
Simplify using `only [GridData.a]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem a_real (i : ℕ) : ((G.a i : ℚ) : ℝ) = (G.v 2 : ℝ) + 1 / 2 + ((G.m : ℝ) + 1 - i) * G.ga := by
  simp only [GridData.a]; push_cast; ring

/- English proof (translation)
Simplify using `only [GridData.vHalf]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vHalf_real (i : ℕ) : ((G.vHalf i : ℚ) : ℝ) = (G.v i : ℝ) - 1 / 2 := by
  simp only [GridData.vHalf]; push_cast; ring

/- English proof (translation)
Rewrite using `[a_real, vHalf_real]`. Establish `h1 : (G.v j : ℝ) ≤ G.v 2` using `by exact_mod_cast (v_le_v_two hj hjk).2`. Establish `h2 : (i : ℝ) ≤ G.m` using `by exact_mod_cast hi`. Establish `h3 : (0 : ℝ) ≤ G.ga` using `by positivity`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 h2) h3]`.
-/
theorem a_sub_vHalf {i j : ℕ} (hi : i ≤ G.m) (hj : 2 ≤ j) (hjk : j ≤ G.k) :
    (G.ga : ℝ) + 1 ≤ ((G.a i : ℚ) : ℝ) - ((G.vHalf j : ℚ) : ℝ) := by
  rw [a_real, vHalf_real]
  have h1 : (G.v j : ℝ) ≤ G.v 2 := by exact_mod_cast (v_le_v_two hj hjk).2
  have h2 : (i : ℝ) ≤ G.m := by exact_mod_cast hi
  have h3 : (0 : ℝ) ≤ G.ga := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 h2) h3]

/- English proof (translation)
Rewrite using `[a_real, a_real]`. Establish `h3 : (0 : ℝ) ≤ G.ga` using `by positivity`. Break down `lt_or_gt_of_ne h with h | h` into its components or cases. Establish `: (i : ℝ) + 1 ≤ j` using `by exact_mod_cast h`. Conclude with `le_abs.2 (Or.inl (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ j - i - 1) h3]))`.

Establish `: (j : ℝ) + 1 ≤ i` using `by exact_mod_cast h`. Conclude with `le_abs.2 (Or.inr (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ i - j - 1) h3]))`.
-/
theorem a_abs_sub {i j : ℕ} (h : i ≠ j) : (G.ga : ℝ) ≤ |((G.a i : ℚ) : ℝ) - ((G.a j : ℚ) : ℝ)| := by
  rw [a_real, a_real]
  have h3 : (0 : ℝ) ≤ G.ga := by positivity
  rcases lt_or_gt_of_ne h with h | h
  · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    exact le_abs.2 (Or.inl (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ j - i - 1) h3]))
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    exact le_abs.2 (Or.inr (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ i - j - 1) h3]))

end GlobalTheory.SignedHC.GridData

namespace GlobalTheory.SignedHC.GridData

variable {G : GridData}

/- English proof (translation)
Introduce `x hx y hy hxy`. Apply the tactic sequence `rcases mem_lam.1 hx with ⟨i, hi, rfl⟩ | ⟨hx1, -⟩ <;> rcases mem_lam.1 hy with ⟨j, hj, rfl⟩ | ⟨hy1, -⟩`. Simplify using `only at hxy ⊢`. Establish `hij : i ≠ j` using `by rintro rfl; exact lt_irrefl _ hxy`. Use `a_abs_sub (G := G) hij` as an intermediate fact.

Rewrite `this` using `[abs_of_pos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨j, hj2, hjk, hye⟩` from `mem_cloudHalf.1 hy1`. Simplify using `only at hxy ⊢`. Rewrite using `[hye]`.

Use `a_sub_vHalf (G := G) hi hj2 hjk` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨i, hi2, hik, hxe⟩` from `mem_cloudHalf.1 hx1`. Simplify using `only at hxy ⊢`. Rewrite `hxy` using `[hxe]`.

Use `a_sub_vHalf (G := G) hj hi2 hik` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨i, hi2, hik, hxe⟩` from `mem_cloudHalf.1 hx1`. Take `⟨j, hj2, hjk, hye⟩` from `mem_cloudHalf.1 hy1`. Rewrite `hxy`, the goal using `[hxe, hye, vHalf_real, vHalf_real]`.

Establish `h1 : G.v j < G.v i`. Establish `: (G.v j : ℝ) < G.v i` using `by linarith`. Conclude with `this` after adjusting the coercions. Use `v_sep_of_gaps hv hi2 hik hj2 hjk h1` as an intermediate fact. Establish `: (G.v j : ℝ) + 2 ≤ G.v i` using `by exact_mod_cast this`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lam_wide {H : ℝ} (hH : 2 ≤ H) (hga : H ≤ G.ga) (hv : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) :
    ∀ x ∈ G.lam, ∀ y ∈ G.lam, ((y.1 : ℚ) : ℝ) < x.1 → 2 ≤ ((x.1 : ℚ) : ℝ) - y.1 := by
  intro x hx y hy hxy
  rcases mem_lam.1 hx with ⟨i, hi, rfl⟩ | ⟨hx1, -⟩ <;> rcases mem_lam.1 hy with ⟨j, hj, rfl⟩ | ⟨hy1, -⟩
  · simp only at hxy ⊢
    have hij : i ≠ j := by rintro rfl; exact lt_irrefl _ hxy
    have := a_abs_sub (G := G) hij
    rw [abs_of_pos (by linarith)] at this
    linarith
  · obtain ⟨j, hj2, hjk, hye⟩ := mem_cloudHalf.1 hy1
    simp only at hxy ⊢
    rw [hye]
    have := a_sub_vHalf (G := G) hi hj2 hjk
    linarith
  · obtain ⟨i, hi2, hik, hxe⟩ := mem_cloudHalf.1 hx1
    simp only at hxy ⊢
    rw [hxe] at hxy
    have := a_sub_vHalf (G := G) hj hi2 hik
    linarith
  · obtain ⟨i, hi2, hik, hxe⟩ := mem_cloudHalf.1 hx1
    obtain ⟨j, hj2, hjk, hye⟩ := mem_cloudHalf.1 hy1
    rw [hxe, hye, vHalf_real, vHalf_real] at hxy ⊢
    have h1 : G.v j < G.v i := by
      have : (G.v j : ℝ) < G.v i := by linarith
      exact_mod_cast this
    have := v_sep_of_gaps hv hi2 hik hj2 hjk h1
    have : (G.v j : ℝ) + 2 ≤ G.v i := by exact_mod_cast this
    linarith

/- English proof (translation)
Introduce `x hx y hy hs`. Apply the tactic sequence `rcases mem_lam.1 hx with ⟨i, hi, rfl⟩ | ⟨hx1, hx2⟩ <;> rcases mem_lam.1 hy with ⟨j, hj, rfl⟩ | ⟨hy1, hy2⟩`. Establish `hij : i ≠ j` using `by rintro rfl; exact hs rfl`. Conclude with `hga.trans (a_abs_sub hij)`. Take `⟨j, hj2, hjk, hye⟩` from `mem_cloudHalf.1 hy1`.

Simplify using `only`. Rewrite using `[hye]`. Use `a_sub_vHalf (G := G) hi hj2 hjk` as an intermediate fact. Conclude with `le_abs.2 (Or.inl (by linarith))`. Take `⟨i, hi2, hik, hxe⟩` from `mem_cloudHalf.1 hx1`.

Simplify using `only`. Rewrite using `[hxe]`. Use `a_sub_vHalf (G := G) hj hi2 hik` as an intermediate fact. Conclude with `le_abs.2 (Or.inr (by linarith))`. Conclude with `absurd (hx2.trans hy2.symm) hs`.
-/
theorem lam_gap {H : ℝ} (hH : 2 ≤ H) (hga : H ≤ G.ga) :
    ∀ x ∈ G.lam, ∀ y ∈ G.lam, x.2 ≠ y.2 → H ≤ |((x.1 : ℚ) : ℝ) - y.1| := by
  intro x hx y hy hs
  rcases mem_lam.1 hx with ⟨i, hi, rfl⟩ | ⟨hx1, hx2⟩ <;> rcases mem_lam.1 hy with ⟨j, hj, rfl⟩ | ⟨hy1, hy2⟩
  · have hij : i ≠ j := by rintro rfl; exact hs rfl
    exact hga.trans (a_abs_sub hij)
  · obtain ⟨j, hj2, hjk, hye⟩ := mem_cloudHalf.1 hy1
    simp only
    rw [hye]
    have := a_sub_vHalf (G := G) hi hj2 hjk
    exact le_abs.2 (Or.inl (by linarith))
  · obtain ⟨i, hi2, hik, hxe⟩ := mem_cloudHalf.1 hx1
    simp only
    rw [hxe]
    have := a_sub_vHalf (G := G) hj hi2 hik
    exact le_abs.2 (Or.inr (by linarith))
  · exact absurd (hx2.trans hy2.symm) hs

/- English proof (translation)
Introduce `x hx y hy hxy`. Establish `cl : ∀ i l, 2 ≤ i → i ≤ G.k → 1 ≤ l → l ≤ G.m → (2 : ℝ) ≤ (G.v i : ℝ) + G.b l`. Introduce `i l hi hik hl hlm`. Establish `h1` using `(v_le_v_two (G := G) hi hik).1`. Establish `h2` using `b_one_le (G := G) hl hlm`.

Establish `: (2 : ℤ) ≤ G.v i + G.b l` using `by omega`. Conclude with `this` after adjusting the coercions. Apply the tactic sequence `rcases mem_discrete_parameter_iff.1 hx with ⟨hx1, -⟩ | ⟨l, hl, hlm, rfl⟩ <;>`. Break down `mem_discrete_parameter_iff.1 hy with ⟨hy1, -⟩ | ⟨l', hl', hlm', rfl⟩` into its components or cases. Take `⟨i, hi2, hik, hxe⟩` from `mem_cloud.1 hx1`.

Take `⟨j, hj2, hjk, hye⟩` from `mem_cloud.1 hy1`. Rewrite `hxy`, the goal using `[hxe, hye]`. Move the coercions through the operations in `at hxy ⊢`. Establish `h1 : G.v j < G.v i` using `by exact_mod_cast hxy`. Use `v_sep_of_gaps hv hi2 hik hj2 hjk h1` as an intermediate fact.

Establish `: (G.v j : ℝ) + 2 ≤ G.v i` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨i, hi2, hik, hxe⟩` from `mem_cloud.1 hx1`. Rewrite using `[hxe]`. Simplify using `only`.

Use `push_cast`. Combine the linear relations using `[cl i l' hi2 hik hl' hlm']`. Take `⟨j, hj2, hjk, hye⟩` from `mem_cloud.1 hy1`. Rewrite `hxy` using `[hye]`. Simplify using `only at hxy`.

Move the coercions through the operations in `at hxy`. Combine the linear relations using `[cl j l hj2 hjk hl hlm]`. Simplify using `only at hxy ⊢`. Move the coercions through the operations in `at hxy ⊢`. Establish `hll : l < l'`.

Assume the negation of the conclusion as `h`. Break down `(not_lt.1 h).eq_or_lt with rfl | h` into its components or cases. Conclude with `lt_irrefl _ hxy`. Use `G.b_mono l' l hl' h hlm` as an intermediate fact. Establish `: (G.b l' : ℝ) < G.b l` using `by exact_mod_cast this`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `b_sep_of_gaps (by linarith) hb hl hlm hl' hlm' hll` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem two_le_sub_of_mem_parD0_of_lt {H : ℝ} (hH : 2 ≤ H) (hv : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i)
    (hvb : 2 ≤ G.v G.k + G.b 1) (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) :
    ∀ x ∈ G.parD0, ∀ y ∈ G.parD0, ((y.1 : ℚ) : ℝ) < x.1 → 2 ≤ ((x.1 : ℚ) : ℝ) - y.1 := by
  intro x hx y hy hxy
  have cl : ∀ i l, 2 ≤ i → i ≤ G.k → 1 ≤ l → l ≤ G.m → (2 : ℝ) ≤ (G.v i : ℝ) + G.b l := by
    intro i l hi hik hl hlm
    have h1 := (v_le_v_two (G := G) hi hik).1
    have h2 := b_one_le (G := G) hl hlm
    have : (2 : ℤ) ≤ G.v i + G.b l := by omega
    exact_mod_cast this
  rcases mem_discrete_parameter_iff.1 hx with ⟨hx1, -⟩ | ⟨l, hl, hlm, rfl⟩ <;>
    rcases mem_discrete_parameter_iff.1 hy with ⟨hy1, -⟩ | ⟨l', hl', hlm', rfl⟩
  · obtain ⟨i, hi2, hik, hxe⟩ := mem_cloud.1 hx1
    obtain ⟨j, hj2, hjk, hye⟩ := mem_cloud.1 hy1
    rw [hxe, hye] at hxy ⊢
    push_cast at hxy ⊢
    have h1 : G.v j < G.v i := by exact_mod_cast hxy
    have := v_sep_of_gaps hv hi2 hik hj2 hjk h1
    have : (G.v j : ℝ) + 2 ≤ G.v i := by exact_mod_cast this
    linarith
  · obtain ⟨i, hi2, hik, hxe⟩ := mem_cloud.1 hx1
    rw [hxe]
    simp only
    push_cast
    linarith [cl i l' hi2 hik hl' hlm']
  · obtain ⟨j, hj2, hjk, hye⟩ := mem_cloud.1 hy1
    rw [hye] at hxy
    simp only at hxy
    push_cast at hxy
    linarith [cl j l hj2 hjk hl hlm]
  · simp only at hxy ⊢
    push_cast at hxy ⊢
    have hll : l < l' := by
      by_contra h
      rcases (not_lt.1 h).eq_or_lt with rfl | h
      · exact lt_irrefl _ hxy
      · have := G.b_mono l' l hl' h hlm
        have : (G.b l' : ℝ) < G.b l := by exact_mod_cast this
        linarith
    have := b_sep_of_gaps (by linarith) hb hl hlm hl' hlm' hll
    linarith

/- English proof (translation)
Introduce `x hx y hy hs`. Establish `cl : ∀ i l, 2 ≤ i → i ≤ G.k → 1 ≤ l → l ≤ G.m → decide (Even (l - 1)) = false → H ≤ (G.v i : ℝ) + G.b l`. Introduce `i l hi hik hl hlm hsl`. Establish `hl2 : 2 ≤ l`. Break down `(show l = 1 ∨ 2 ≤ l by omega) with rfl | h` into its components or cases.

Simplify using `at hsl`. Conclude with `h`. Establish `h1` using `(v_le_v_two (G := G) hi hik).1`. Establish `h2` using `b_sep_of_gaps (by linarith) hb le_rfl (by omega) (by omega) hlm (by omega : 1 < l)`. Establish `h3 : (G.v G.k : ℝ) ≤ G.v i` using `by exact_mod_cast h1`.

Establish `h4 : (2 : ℝ) ≤ G.v G.k + G.b 1` using `by exact_mod_cast hvb`. Combine the linear equalities and inequalities to obtain the conclusion. Apply the tactic sequence `rcases mem_discrete_parameter_iff.1 hx with ⟨hx1, hx2⟩ | ⟨l, hl, hlm, rfl⟩ <;>`. Break down `mem_discrete_parameter_iff.1 hy with ⟨hy1, hy2⟩ | ⟨l', hl', hlm', rfl⟩` into its components or cases. Conclude with `absurd (hx2.trans hy2.symm) hs`.

Take `⟨i, hi2, hik, hxe⟩` from `mem_cloud.1 hx1`. Rewrite using `[hxe]`. Simplify using `only at hs ⊢`. Rewrite `hs` using `[hx2]`. Use `cl i l' hi2 hik hl' hlm' (by simpa [eq_comm] using hs)` as an intermediate fact.

Use `push_cast`. Conclude with `le_abs.2 (Or.inl (by linarith))`. Take `⟨j, hj2, hjk, hye⟩` from `mem_cloud.1 hy1`. Rewrite using `[hye]`. Simplify using `only at hs ⊢`.

Rewrite `hs` using `[hy2]`. Use `cl j l hj2 hjk hl hlm (by simpa using hs)` as an intermediate fact. Use `push_cast`. Conclude with `le_abs.2 (Or.inr (by linarith))`. Simplify using `only at hs ⊢`.

Establish `hll : l ≠ l'` using `by rintro rfl; exact hs rfl`. Use `b_abs_of_gaps (by linarith) hb hl hlm hl' hlm' hll` as an intermediate fact. Use `push_cast`. Rewrite `this` using `[abs_sub_comm]`. Rewrite using `[show -(G.b l : ℝ) - -(G.b l' : ℝ) = (G.b l' : ℝ) - G.b l by ring]` and apply the resulting hypothesis.
-/
theorem le_abs_sub_of_mem_parD0_of_ne_sign {H : ℝ} (hH : 2 ≤ H) (hvb : 2 ≤ G.v G.k + G.b 1)
    (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) :
    ∀ x ∈ G.parD0, ∀ y ∈ G.parD0, x.2 ≠ y.2 → H ≤ |((x.1 : ℚ) : ℝ) - y.1| := by
  intro x hx y hy hs

  have cl : ∀ i l, 2 ≤ i → i ≤ G.k → 1 ≤ l → l ≤ G.m → decide (Even (l - 1)) = false →
      H ≤ (G.v i : ℝ) + G.b l := by
    intro i l hi hik hl hlm hsl
    have hl2 : 2 ≤ l := by
      rcases (show l = 1 ∨ 2 ≤ l by omega) with rfl | h
      · simp at hsl
      · exact h
    have h1 := (v_le_v_two (G := G) hi hik).1
    have h2 := b_sep_of_gaps (by linarith) hb le_rfl (by omega) (by omega) hlm (by omega : 1 < l)
    have h3 : (G.v G.k : ℝ) ≤ G.v i := by exact_mod_cast h1
    have h4 : (2 : ℝ) ≤ G.v G.k + G.b 1 := by exact_mod_cast hvb
    linarith
  rcases mem_discrete_parameter_iff.1 hx with ⟨hx1, hx2⟩ | ⟨l, hl, hlm, rfl⟩ <;>
    rcases mem_discrete_parameter_iff.1 hy with ⟨hy1, hy2⟩ | ⟨l', hl', hlm', rfl⟩
  · exact absurd (hx2.trans hy2.symm) hs
  · obtain ⟨i, hi2, hik, hxe⟩ := mem_cloud.1 hx1
    rw [hxe]
    simp only at hs ⊢
    rw [hx2] at hs
    have := cl i l' hi2 hik hl' hlm' (by simpa [eq_comm] using hs)
    push_cast
    exact le_abs.2 (Or.inl (by linarith))
  · obtain ⟨j, hj2, hjk, hye⟩ := mem_cloud.1 hy1
    rw [hye]
    simp only at hs ⊢
    rw [hy2] at hs
    have := cl j l hj2 hjk hl hlm (by simpa using hs)
    push_cast
    exact le_abs.2 (Or.inr (by linarith))
  · simp only at hs ⊢
    have hll : l ≠ l' := by rintro rfl; exact hs rfl
    have := b_abs_of_gaps (by linarith) hb hl hlm hl' hlm' hll
    push_cast
    rw [abs_sub_comm] at this
    rwa [show -(G.b l : ℝ) - -(G.b l' : ℝ) = (G.b l' : ℝ) - G.b l by ring]

/- English proof (translation)
Introduce `G n lam ε mu ε' H hH hga hv hvb hb hl hm`. Rewrite `hl` using `[G.parPi_zero]`. Use `⟨fun a c hac => ?_, fun a c hac => ?_, fun a c hs => ?_, fun a c hs => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hxa, -⟩` from `isEnum_mem hl a`. Take `⟨y, hy, hyc, -⟩` from `isEnum_mem hl c`.

Use `hl.1 hac` as an intermediate fact. Rewrite `this`, the goal using `[hxa, hyc]`. Conclude with `lam_wide hH hga hv x hx y hy this`. Take `⟨x, hx, hxa, -⟩` from `isEnum_mem hm a`. Take `⟨y, hy, hyc, -⟩` from `isEnum_mem hm c`.

Use `hm.1 hac` as an intermediate fact. Rewrite `this`, the goal using `[hxa, hyc]`. Conclude with `two_le_sub_of_mem_parD0_of_lt hH hv hvb hb x hx y hy this`. Take `⟨x, hx, hxa, hxe⟩` from `isEnum_mem hl a`. Take `⟨y, hy, hyc, hye⟩` from `isEnum_mem hl c`.

Rewrite using `[hxa, hyc]`. Conclude with `lam_gap hH hga x hx y hy (by rw [← hxe, ← hye]; exact hs)`. Take `⟨x, hx, hxa, hxe⟩` from `isEnum_mem hm a`. Take `⟨y, hy, hyc, hye⟩` from `isEnum_mem hm c`. Rewrite using `[hxa, hyc]`.

Conclude with `le_abs_sub_of_mem_parD0_of_ne_sign hH hvb hb x hx y hy (by rw [← hxe, ← hye]; exact hs)`.
-/
theorem pi_zero_and_D0_spacing : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ}
    {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool} {H : ℝ}, 2 ≤ H → H ≤ G.ga →
    (∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) → 2 ≤ G.v G.k + G.b 1 →
    (∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' →
    (∀ a c, a < c → 2 ≤ lam a - lam c) ∧ (∀ a c, a < c → 2 ≤ mu a - mu c) ∧ Formalism.QuantumDeterminants.GapAtLeast ε lam H ∧
      Formalism.QuantumDeterminants.GapAtLeast ε' mu H := by
  intro G n lam ε mu ε' H hH hga hv hvb hb hl hm
  rw [G.parPi_zero] at hl
  refine ⟨fun a c hac => ?_, fun a c hac => ?_, fun a c hs => ?_, fun a c hs => ?_⟩
  · obtain ⟨x, hx, hxa, -⟩ := isEnum_mem hl a
    obtain ⟨y, hy, hyc, -⟩ := isEnum_mem hl c
    have := hl.1 hac
    rw [hxa, hyc] at this ⊢
    exact lam_wide hH hga hv x hx y hy this
  · obtain ⟨x, hx, hxa, -⟩ := isEnum_mem hm a
    obtain ⟨y, hy, hyc, -⟩ := isEnum_mem hm c
    have := hm.1 hac
    rw [hxa, hyc] at this ⊢
    exact two_le_sub_of_mem_parD0_of_lt hH hv hvb hb x hx y hy this
  · obtain ⟨x, hx, hxa, hxe⟩ := isEnum_mem hl a
    obtain ⟨y, hy, hyc, hye⟩ := isEnum_mem hl c
    rw [hxa, hyc]
    exact lam_gap hH hga x hx y hy (by rw [← hxe, ← hye]; exact hs)
  · obtain ⟨x, hx, hxa, hxe⟩ := isEnum_mem hm a
    obtain ⟨y, hy, hyc, hye⟩ := isEnum_mem hm c
    rw [hxa, hyc]
    exact le_abs_sub_of_mem_parD0_of_ne_sign hH hvb hb x hx y hy (by rw [← hxe, ← hye]; exact hs)

end GlobalTheory.SignedHC.GridData
