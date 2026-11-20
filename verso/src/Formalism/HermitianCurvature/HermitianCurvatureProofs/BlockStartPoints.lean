import Mathlib
import Formalism.HermitianCurvature.StatementTB

namespace Formalism.FourierDecayAlt.P.BlockStartPoints

open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
open Classical

noncomputable section

variable {E W : Type} [Field E]

/- English proof (translation)
Establish `h` using `(Matrix.PosSemidef.hadamard hk hg).dotProduct_mulVec_nonneg (fun _ => (1 : ℂ))`. Establish `e : star (fun _ : Y => (1 : ℂ)) ⬝ᵥ (Matrix.mulVec (Matrix.hadamard (Matrix.of fun x y : Y => k x y) (Matrix.of fun x y : Y => g x y)) (fun _ => (1 : ℂ))) = ∑ p ∈ Y, ∑ q ∈ Y, k p q * g p q`. Simplify using `only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.of_apply, Pi.star_apply, star_one, one_mul, mul_one]`. Rewrite using `[← Finset.sum_coe_sort Y]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_coe_sort Y]`. Rewrite `h` using `[e]`. Conclude with `(Complex.le_def.1 h).1`.
-/
lemma psd_sum_nonneg {α : Type} (Y : Finset α) (k g : α → α → ℂ) (hk : PSDOn Y k)
    (hg : PSDOn Y g) : 0 ≤ (∑ p ∈ Y, ∑ q ∈ Y, k p q * g p q).re := by
  have h := (Matrix.PosSemidef.hadamard hk hg).dotProduct_mulVec_nonneg (fun _ => (1 : ℂ))
  have e : star (fun _ : Y => (1 : ℂ)) ⬝ᵥ (Matrix.mulVec (Matrix.hadamard
      (Matrix.of fun x y : Y => k x y) (Matrix.of fun x y : Y => g x y)) (fun _ => (1 : ℂ))) =
      ∑ p ∈ Y, ∑ q ∈ Y, k p q * g p q := by
    simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.of_apply, Pi.star_apply,
      star_one, one_mul, mul_one]
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_coe_sort Y]
  rw [e] at h
  exact (Complex.le_def.1 h).1

/- English proof (translation)
The claim follows from `Matrix.PosSemidef.submatrix hk (fun a : Y => (⟨φ a, hφ a a.2⟩ : Z))`.
-/
lemma psd_comp {α β : Type} (Y : Finset α) (Z : Finset β) (φ : α → β) (hφ : ∀ a ∈ Y, φ a ∈ Z)
    (k : β → β → ℂ) (hk : PSDOn Z k) : PSDOn Y (fun a b => k (φ a) (φ b)) :=
  Matrix.PosSemidef.submatrix hk (fun a : Y => (⟨φ a, hφ a a.2⟩ : Z))

/- English proof (translation)
Simplify using `[level, join]`.
-/
lemma level_join (h : Pt E) (s : ℕ) (t : E) : level (join h s t) = level h + s := by
  simp [level, join]

/- English proof (translation)
Simplify using `[blockStart, join, List.take_append_of_le_length hk]`.
-/
lemma blockStart_join (h : Pt E) (s : ℕ) (t : E) (k : ℕ) (hk : k ≤ h.length) :
    blockStart (join h s t) k = blockStart h k := by
  simp [blockStart, join, List.take_append_of_le_length hk]

/- English proof (translation)
Simplify using `[blockStart, level]`.
-/
lemma blockStart_length (h : Pt E) : blockStart h h.length = level h + 1 := by
  simp [blockStart, level]

/- English proof (translation)
Rewrite using `[T.isTower, T.isTower, level_join]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, ⟨rfl, fun k hk => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hk' : k < (join h s t).length` using `by simp [join]; omega`.

Establish `h3` using `h2 k hk'`. Rewrite `h3` using `[blockStart_join _ _ _ _ hk.le]`. Establish `e : (join h s t)[k]'hk' = h[k]'hk` using `by simp [join, List.getElem_append_left hk]`. Rewrite `h3` using `[e]`. Then use the resulting hypothesis. Establish `hk' : h.length < (join h s t).length` using `by simp [join]`.

Establish `h3` using `h2 h.length hk'`. Rewrite `h3` using `[blockStart_join _ _ _ _ le_rfl, blockStart_length]`. Establish `e : (join h s t)[h.length]'hk' = (s, t)` using `by simp [join]`. Rewrite `h3` using `[e]`. Then use the resulting hypothesis. Introduce and unpack `⟨h1, ⟨_, h2⟩, h3, h4⟩`.

Use `⟨h1, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hk' : k < h.length + 1` using `by simpa [join] using hk`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | heq` into its components or cases. Rewrite using `[blockStart_join _ _ _ _ hlt.le]`. Establish `e : (join h s t)[k]'hk = h[k]'hlt` using `by simp [join, List.getElem_append_left hlt]`.

Rewrite using `[e]`. Conclude with `h2 k hlt`. Substitute `heq` using the available equality. Rewrite using `[blockStart_join _ _ _ _ le_rfl, blockStart_length]`. Establish `e : (join h s t)[h.length]'hk = (s, t)` using `by simp [join]`.

Rewrite using `[e]`. Conclude with `⟨h3, h4⟩`.
-/
lemma mem_X_join (T : Tower E) (h : Pt E) (s : ℕ) (t : E) (i : ℕ) :
    join h s t ∈ T.X i ↔
      level h + s = i ∧ h ∈ T.X (level h) ∧ 1 ≤ s ∧ t ∈ T.Sg (level h + 1) s := by
  rw [T.isTower, T.isTower, level_join]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ⟨rfl, fun k hk => ?_⟩, ?_⟩
    · have hk' : k < (join h s t).length := by simp [join]; omega
      have h3 := h2 k hk'
      rw [blockStart_join _ _ _ _ hk.le] at h3
      have e : (join h s t)[k]'hk' = h[k]'hk := by simp [join, List.getElem_append_left hk]
      rwa [e] at h3
    · have hk' : h.length < (join h s t).length := by simp [join]
      have h3 := h2 h.length hk'
      rw [blockStart_join _ _ _ _ le_rfl, blockStart_length] at h3
      have e : (join h s t)[h.length]'hk' = (s, t) := by simp [join]
      rwa [e] at h3
  · rintro ⟨h1, ⟨_, h2⟩, h3, h4⟩
    refine ⟨h1, fun k hk => ?_⟩
    have hk' : k < h.length + 1 := by simpa [join] using hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | heq
    · rw [blockStart_join _ _ _ _ hlt.le]
      have e : (join h s t)[k]'hk = h[k]'hlt := by simp [join, List.getElem_append_left hlt]
      rw [e]
      exact h2 k hlt
    · subst heq
      rw [blockStart_join _ _ _ _ le_rfl, blockStart_length]
      have e : (join h s t)[h.length]'hk = (s, t) := by simp [join]
      rw [e]
      exact ⟨h3, h4⟩

/- English proof (translation)
Use extensionality with `p`. Simplify using `only [Xs, pts, mem_filter, mem_image, mem_product, Prod.exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hp, hl⟩`. Break down `List.eq_nil_or_concat p with rfl | ⟨h, x, rfl⟩` into its components or cases.

Simplify using `at hl`. Take `⟨s', t⟩` from `x`. Establish `hss : s' = s` using `by simpa using hl`. Substitute `hss` using the available equality. Rewrite `hp` using `[List.concat_eq_append]`.

Take `⟨h1, h2, h3, h4⟩` from `(mem_X_join T h s' t i).1 hp`. Establish `hlev : level h = i - s'` using `by omega`. Use `⟨h, t, ⟨?_, ?_⟩, by rw [List.concat_eq_append]; rfl⟩` and prove the remaining obligations. Rewrite using `[← hlev]`. Conclude with `h2`.

Rewrite using `[← hlev]`. Conclude with `h4`. Introduce and unpack `⟨h, t, ⟨hh, ht⟩, rfl⟩`. Establish `hlev : level h = i - s` using `((T.isTower _ _).1 hh).1`. Conclude with `⟨(mem_X_join T h s t i).2 ⟨by omega, by rw [hlev]; exact hh, hs, by rw [hlev]; exact ht⟩, by simp [join]⟩`.
-/
lemma Xs_eq (T : Tower E) (i s : ℕ) (hs : 1 ≤ s) (hsi : s ≤ i) :
    Xs T i s = pts (T.X (i - s)) s (T.Sg (i - s + 1) s) := by
  ext p
  simp only [Xs, pts, mem_filter, mem_image, mem_product, Prod.exists]
  constructor
  · rintro ⟨hp, hl⟩
    rcases List.eq_nil_or_concat p with rfl | ⟨h, x, rfl⟩
    · simp at hl
    · obtain ⟨s', t⟩ := x
      have hss : s' = s := by simpa using hl
      subst hss
      rw [List.concat_eq_append] at hp
      obtain ⟨h1, h2, h3, h4⟩ := (mem_X_join T h s' t i).1 hp
      have hlev : level h = i - s' := by omega
      refine ⟨h, t, ⟨?_, ?_⟩, by rw [List.concat_eq_append]; rfl⟩
      · rw [← hlev]; exact h2
      · rw [← hlev]; exact h4
  · rintro ⟨h, t, ⟨hh, ht⟩, rfl⟩
    have hlev : level h = i - s := ((T.isTower _ _).1 hh).1
    exact ⟨(mem_X_join T h s t i).2 ⟨by omega, by rw [hlev]; exact hh, hs, by rw [hlev]; exact ht⟩,
      by simp [join]⟩

/- English proof (translation)
Unfold `pts`. Rewrite using `[Finset.sum_image, Finset.sum_product_right]`. Introduce and unpack `⟨h, t⟩ _ ⟨h', t'⟩ _ e`. Simplify using `only [join] at e`. Establish `h2` using `List.append_inj' e rfl`.

Simplify using `using h2`.
-/
lemma sum_pts {β : Type} [AddCommMonoid β] (Y : Finset (Pt E)) (s : ℕ) (S : Finset E)
    (F : Pt E → β) : ∑ p ∈ pts Y s S, F p = ∑ t ∈ S, ∑ h ∈ Y, F (join h s t) := by
  unfold pts
  rw [Finset.sum_image, Finset.sum_product_right]
  rintro ⟨h, t⟩ _ ⟨h', t'⟩ _ e
  simp only [join] at e
  have h2 := List.append_inj' e rfl
  simpa using h2

/- English proof (translation)
Establish `e : ∑ t ∈ S, ∑ t' ∈ S, m t t' * ((a t + b t') / 2) = (∑ t ∈ S, a t * ∑ t' ∈ S, m t t') / 2 + (∑ t' ∈ S, b t' * ∑ t ∈ S, m t t') / 2`. Establish `e2 : ∑ t' ∈ S, b t' * ∑ t ∈ S, m t t' = ∑ t ∈ S, ∑ t' ∈ S, b t' * m t t'`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun t' _ => Finset.mul_sum _ _ _`. Rewrite using `[e2, ← add_div, ← Finset.sum_add_distrib, Finset.sum_div]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]`. Conclude with `Finset.sum_congr rfl fun t' _ => by ring`. Rewrite using `[e]`. Establish `h1 : ∑ t ∈ S, a t * ∑ t' ∈ S, m t t' ≤ ep * M`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ∑ t' ∈ S, b t' * ∑ t ∈ S, m t t' ≤ ep * M`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma schur_real {τ : Type} (S : Finset τ) (m : τ → τ → ℝ) (ep M : ℝ) (hep : 0 ≤ ep)
    (row : ∀ t ∈ S, ∑ t' ∈ S, m t t' ≤ ep) (col : ∀ t' ∈ S, ∑ t ∈ S, m t t' ≤ ep)
    (a b : τ → ℝ) (ha : ∀ t, 0 ≤ a t) (hb : ∀ t, 0 ≤ b t)
    (hA : ∑ t ∈ S, a t ≤ M) (hB : ∑ t ∈ S, b t ≤ M) :
    ∑ t ∈ S, ∑ t' ∈ S, m t t' * ((a t + b t') / 2) ≤ ep * M := by
  have e : ∑ t ∈ S, ∑ t' ∈ S, m t t' * ((a t + b t') / 2) =
      (∑ t ∈ S, a t * ∑ t' ∈ S, m t t') / 2 + (∑ t' ∈ S, b t' * ∑ t ∈ S, m t t') / 2 := by
    have e2 : ∑ t' ∈ S, b t' * ∑ t ∈ S, m t t' = ∑ t ∈ S, ∑ t' ∈ S, b t' * m t t' := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t' _ => Finset.mul_sum _ _ _
    rw [e2, ← add_div, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun t' _ => by ring
  rw [e]
  have h1 : ∑ t ∈ S, a t * ∑ t' ∈ S, m t t' ≤ ep * M := by
    calc ∑ t ∈ S, a t * ∑ t' ∈ S, m t t' ≤ ∑ t ∈ S, a t * ep :=
          Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (row t ht) (ha t)
      _ = ep * ∑ t ∈ S, a t := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ ep * M := mul_le_mul_of_nonneg_left hA hep
  have h2 : ∑ t' ∈ S, b t' * ∑ t ∈ S, m t t' ≤ ep * M := by
    calc ∑ t' ∈ S, b t' * ∑ t ∈ S, m t t' ≤ ∑ t' ∈ S, b t' * ep :=
          Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (col t ht) (hb t)
      _ = ep * ∑ t ∈ S, b t := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ ep * M := mul_le_mul_of_nonneg_left hB hep
  linarith

/- English proof (translation)
Repeatedly rewrite using `[Finset.mul_sum]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma phi_sum {τ J : Type} (S : Finset τ) (Js : Finset J) (m : τ → τ → ℝ) (g : J → τ → τ → ℝ) :
    ∑ t ∈ S, ∑ t' ∈ S, m t t' * ∑ j ∈ Js, g j t t' =
      ∑ j ∈ Js, ∑ t ∈ S, ∑ t' ∈ S, m t t' * g j t t' := by
  simp_rw [Finset.mul_sum]
  calc ∑ t ∈ S, ∑ t' ∈ S, ∑ j ∈ Js, m t t' * g j t t'
      = ∑ t ∈ S, ∑ j ∈ Js, ∑ t' ∈ S, m t t' * g j t t' :=
        Finset.sum_congr rfl fun t _ => Finset.sum_comm
    _ = ∑ j ∈ Js, ∑ t ∈ S, ∑ t' ∈ S, m t t' * g j t t' := Finset.sum_comm

/- English proof (translation)
Unfold `Data.Nst`. Rewrite using `[Complex.div_ofReal_re]`. Use `div_nonneg ?_ (hW w).le` and prove the remaining obligations. Conclude with `psd_sum_nonneg Y _ (fun h h' => D.gram ε i w (join h s t) (join h' s t)) (psd_comp Y (Y.image fun h => join h s t) (fun h => join h s t) (fun a ha => mem_image_of_mem _ ha) _ (hK.1 i _)) (psd_comp Y (Y.image fun h => join h s t) (fun h => join h s t) (fun a ha => mem_image_of_mem …`.
-/
lemma diag_nonneg (D : Data E W) (hG : D.GramPSD) (hK : D.KernelPSD) (hW : D.WordsPos) (ε : ℝ)
    (hε : 0 < ε) (i s : ℕ) (w : W) (Y : Finset (Pt E)) (t : E) :
    0 ≤ (D.Nst ε i s w Y (blk (D.Kr i) s t t) t t).re := by
  unfold Data.Nst
  rw [Complex.div_ofReal_re]
  refine div_nonneg ?_ (hW w).le
  exact psd_sum_nonneg Y _ (fun h h' => D.gram ε i w (join h s t) (join h' s t))
    (psd_comp Y (Y.image fun h => join h s t) (fun h => join h s t)
      (fun a ha => mem_image_of_mem _ ha) _ (hK.1 i _))
    (psd_comp Y (Y.image fun h => join h s t) (fun h => join h s t)
      (fun a ha => mem_image_of_mem _ ha) _ (hG ε hε i w _))

/- English proof (translation)
Unfold `Data.Sf Data.Nst`. Rewrite using `[sum_pts]`. Repeatedly rewrite using `[sum_pts, Complex.div_ofReal_re, Complex.re_sum, blk]`. Rewrite using `[Finset.sum_div]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm, Finset.sum_div]`.
-/
lemma Sf_pts (D : Data E W) (ε : ℝ) (i s : ℕ) (w : W) (Y : Finset (Pt E)) (S : Finset E) :
    D.Sf ε i w (pts Y s S) / D.wt w =
      ∑ t ∈ S, ∑ t' ∈ S, (D.Nst ε i s w Y (blk (D.Kr i) s t t') t t').re := by
  unfold Data.Sf Data.Nst
  rw [sum_pts]
  simp_rw [sum_pts, Complex.div_ofReal_re, Complex.re_sum, blk]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm, Finset.sum_div]

end

end Formalism.FourierDecayAlt.P.BlockStartPoints

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.BlockStartPoints
open Classical

/- English proof (translation)
Introduce `E W _ D ep hG hK hW hA2 hEL hLS T ε hε i s hs hsi hi w hw hcnt M hM`. Establish `hlev : ∀ h ∈ T.X (i - s), level h = i - s` using `fun h hh => ((T.isTower _ _).1 hh).1`. Establish `hS0 : ∀ t ∈ T.Sg (i - s + 1) s, t ≠ 0` using `fun t ht h0 => T.zero_not_mem _ _ (h0 ▸ ht)`. Establish `hep : 0 ≤ ep` using `by simpa using hLS.1 i (by omega) hi ∅ (by simp)`. Establish `ha : ∀ w' t, 0 ≤ (D.Nst ε i s w' (T.X (i - s)) (blk (D.Kr i) s t t) t t).re` using `fun w' t => diag_nonneg D hG hK hW ε hε i s w' _ t`.

Establish `hM0 : 0 ≤ M` using `le_trans (Finset.sum_nonneg fun t _ => ha w t) (hM w (by simp [Data.Wb, hw]))`. Rewrite using `[Xs_eq T i s hs hsi, Sf_pts]`. Generalize the expression as in `hY : T.X (i - s) = Y at *`. Generalize the expression as in `hS : T.Sg (i - s + 1) s = S at *`. Establish `hDg : ∀ w', D.Dg T ε i s w' = ∑ t ∈ S, (D.Nst ε i s w' Y (blk (D.Kr i) s t t) t t).re`.

Introduce `w'`. Unfold `Data.Dg`. Rewrite using `[hY, hS]`. Simplify using `only [hDg] at hM ⊢`. Establish `hz : ∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → ((i = D.r + 1 ∧ s = 1) ∨ t⁻¹ - t'⁻¹ ∉ D.Lap (i - s + 1) s) → D.Nst ε i s w Y (blk (D.Kr i) s t t') t t' = 0`.

Introduce `t ht t' ht' hne hc`. Unfold `Data.Nst`. Rewrite using `[Finset.sum_eq_zero, zero_div]`. Introduce `h hh`. Use `Finset.sum_eq_zero fun h' hh' => ?_` and prove the remaining obligations.

Establish `hk0 : D.Kr i (join h s t) (join h' s t') = 0`. Assume the negation of the conclusion as `hk`. Take `⟨h1, h2⟩` from `hA2 i s hs hsi hi h h' t t' (hlev h hh) (hlev h' hh') (hS0 t ht) (hS0 t' ht') hne hk`. Break down `hc with hc | hc` into its components or cases. Conclude with `h1 hc`.

Conclude with `hc h2`. Simplify using `[blk, hk0]`. Establish `split : ∀ B : E → E → ℝ, (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → (D.Nst ε i s w Y (blk (D.Kr i) s t t') t t').re ≤ B t t') → (∀ t, 0 ≤ B t t) → ∑ t ∈ S, ∑ t' ∈ S, (D.Nst ε i s w Y (blk (D.Kr i) s t t') t t').re ≤ ∑ t ∈ S, (D.Nst ε i s w Y (blk (D.Kr i) s t t) t t).re + ∑ t ∈ S, ∑ t' ∈ S, B …`. Introduce `B hB hB0`. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_le_sum fun t ht => ?_` and prove the remaining obligations. Establish `e : (D.Nst ε i s w Y (blk (D.Kr i) s t t) t t).re = ∑ t' ∈ S, if t' = t then (D.Nst ε i s w Y (blk (D.Kr i) s t' t') t' t').re else 0`. Rewrite using `[Finset.sum_ite_eq' S t, if_pos ht]`. Rewrite using `[e, ← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun t' ht' => ?_` and prove the remaining obligations.

Distinguish the cases in `htt : t' = t`. Substitute `htt` using the available equality. Rewrite using `[if_pos rfl]`. Combine the linear relations using `[hB0 t']`. Rewrite using `[if_neg htt, zero_add]`.

Conclude with `hB t ht t' ht' (Ne.symm htt)`. Distinguish the cases in `htop : i = D.r + 1 ∧ s = 1`. Establish `h1` using `split (fun _ _ => 0) (fun t ht t' ht' hne => by rw [hz t ht t' ht' hne (Or.inl htop)]; simp) (fun _ => le_rfl)`. Establish `h2 : 0 ≤ 3 ^ D.f * ep * M` using `by positivity`. Simplify using `only [Finset.sum_const_zero, add_zero] at h1`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨θ, hθ, hE⟩` from `hEL ε hε i s hs hsi hi htop w hw hcnt`. Establish `hE'` using `hE Y S (D.Kr i) hlev (hK.1 i _)`. Use `set WW := D.Wb (D.cnt w + D.K) ×ˢ D.Wb (D.cnt w + D.K) with hWW`. Use `set ρ := D.szL (i - s + 1) s with hρ`.

Use `set a : W → E → ℝ := fun w' t => (D.Nst ε i s w' Y (blk (D.Kr i) s t t) t t).re with hadef`. Set `P : E → E → Prop` to `fun t t' => t ≠ t' ∧ t⁻¹ - t'⁻¹ ∈ D.Lap (i - s + 1) s ∧ 0 ≤ D.maj ρ (t⁻¹ - t'⁻¹)`. Set `m : E → E → ℝ` to `fun t t' => if P t t' then D.maj ρ (t⁻¹ - t'⁻¹) else 0`. Establish `hm0 : ∀ t t', 0 ≤ m t t'`. Introduce `t t'`.

Distinguish the cases in `hP : P t t'`. Simplify using `only [m, if_pos hP]`. Conclude with `hP.2.2`. Simplify using `only [m, if_neg hP]`. Conclude with `le_rfl`.

Establish `row : ∀ t ∈ S, ∑ t' ∈ S, m t t' ≤ ep`. Introduce `t _`. Establish `h1` using `hLS.2 i s hs hsi hi htop ((S.filter fun t' => P t t').image fun t' => t⁻¹ - t'⁻¹) (by`. Introduce `l hl`. Take `⟨t', ht', rfl⟩` from `Finset.mem_image.1 hl`.

Establish `hP` using `(Finset.mem_filter.1 ht').2`. Conclude with `⟨hP.2.1, sub_ne_zero.2 fun e => hP.1 (inv_injective e)⟩)`. Rewrite using `[Finset.sum_image (by`. Introduce `x _ y _ e`. Conclude with `inv_injective (sub_right_injective e)), Finset.sum_filter] at h1`.

Conclude with `h1`. Establish `col : ∀ t' ∈ S, ∑ t ∈ S, m t t' ≤ ep`. Introduce `t' _`. Establish `h1` using `hLS.2 i s hs hsi hi htop ((S.filter fun t => P t t').image fun t => t⁻¹ - t'⁻¹) (by`. Introduce `l hl`.

Take `⟨t, ht, rfl⟩` from `Finset.mem_image.1 hl`. Establish `hP` using `(Finset.mem_filter.1 ht).2`. Conclude with `⟨hP.2.1, sub_ne_zero.2 fun e => hP.1 (inv_injective e)⟩)`. Rewrite using `[Finset.sum_image (by`. Introduce `x _ y _ e`.

Conclude with `inv_injective (sub_left_injective e)), Finset.sum_filter] at h1`. Conclude with `h1`. Establish `hX0 : ∀ π t t', 0 ≤ ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2)`. Introduce `π t t'`. Use `Finset.sum_nonneg fun x _ => mul_nonneg ((hθ π).1 x) ?_` and prove the remaining obligations.

Use `ha x.1 t` as an intermediate fact. Use `ha x.2 t'` as an intermediate fact. Simplify using `only [hadef]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `split (fun t t' => m t t' * ∑ π, ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2)) (by`.

Introduce `t ht t' ht' hne`. Establish `hG0 : 0 ≤ ∑ π, ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2)` using `Finset.sum_nonneg fun π _ => hX0 π t t'`. Distinguish the cases in `hL : t⁻¹ - t'⁻¹ ∈ D.Lap (i - s + 1) s`. Take `⟨π, hπ⟩` from `hE' t ht t' ht' (hS0 t ht) (hS0 t' ht') (sub_ne_zero.2 fun e => hne (inv_injective e))`. Establish `h2 : (D.Nst ε i s w Y (blk (D.Kr i) s t t') t t').re ≤ D.maj ρ (t⁻¹ - t'⁻¹) * ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2)` using `le_trans (Complex.re_le_norm _) hπ`.

Establish `h3 : ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) ≤ ∑ π, ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2)` using `Finset.single_le_sum (f := fun π => ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2)) (fun π _ => hX0 π t t') (Finset.mem_univ π)`. Distinguish the cases in `hmj : 0 ≤ D.maj ρ (t⁻¹ - t'⁻¹)`. Establish `hP : P t t'` using `⟨hne, hL, hmj⟩`. Simplify using `only [m, if_pos hP]`. Conclude with `le_trans h2 (mul_le_mul_of_nonneg_left h3 hmj)`.

Establish `h4 : D.maj ρ (t⁻¹ - t'⁻¹) * ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg (not_le.1 hmj).le (hX0 π t t')`. Conclude with `le_trans (le_trans h2 h4) (mul_nonneg (hm0 t t') hG0)`. Rewrite using `[hz t ht t' ht' hne (Or.inr hL)]`. Conclude with `mul_nonneg (hm0 t t') hG0)`. Use the proof step `(fun t => mul_nonneg (hm0 t t) (Finset.sum_nonneg fun π _ => hX0 π t t))`.

Use `le_trans h1 (add_le_add le_rfl ?_)` and prove the remaining obligations. Rewrite using `[phi_sum]`. Establish `h5 : ∀ π : Fin D.f → Fin 3, ∑ t ∈ S, ∑ t' ∈ S, m t t' * ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) ≤ ep * M`. Introduce `π`. Rewrite using `[phi_sum]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun t' _ => by ring`. Use `_ ≤ ∑ x ∈ WW, θ π x * (ep * M) := by`. Use `Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left ?_ ((hθ π).1 x)` and prove the remaining obligations. Establish `hx'` using `Finset.mem_product.1 hx`. Conclude with `schur_real S m ep M hep row col (a x.1) (a x.2) (ha x.1) (ha x.2) (hM x.1 hx'.1) (hM x.2 hx'.2)`.

Use `_ = ep * M := by rw [← Finset.sum_mul, (hθ π).2.2, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem schurRecursion_true : Formalism.FourierDecayAlt.TB.SchurStep := by
  intro E W _ D ep hG hK hW hA2 hEL hLS T ε hε i s hs hsi hi w hw hcnt M hM
  have hlev : ∀ h ∈ T.X (i - s), level h = i - s := fun h hh => ((T.isTower _ _).1 hh).1
  have hS0 : ∀ t ∈ T.Sg (i - s + 1) s, t ≠ 0 := fun t ht h0 => T.zero_not_mem _ _ (h0 ▸ ht)
  have hep : 0 ≤ ep := by simpa using hLS.1 i (by omega) hi ∅ (by simp)
  have ha : ∀ w' t, 0 ≤ (D.Nst ε i s w' (T.X (i - s)) (blk (D.Kr i) s t t) t t).re :=
    fun w' t => diag_nonneg D hG hK hW ε hε i s w' _ t
  have hM0 : 0 ≤ M :=
    le_trans (Finset.sum_nonneg fun t _ => ha w t) (hM w (by simp [Data.Wb, hw]))
  rw [Xs_eq T i s hs hsi, Sf_pts]
  generalize hY : T.X (i - s) = Y at *
  generalize hS : T.Sg (i - s + 1) s = S at *
  have hDg : ∀ w', D.Dg T ε i s w' =
      ∑ t ∈ S, (D.Nst ε i s w' Y (blk (D.Kr i) s t t) t t).re := by
    intro w'; unfold Data.Dg; rw [hY, hS]
  simp only [hDg] at hM ⊢

  have hz : ∀ t ∈ S, ∀ t' ∈ S, t ≠ t' →
      ((i = D.r + 1 ∧ s = 1) ∨ t⁻¹ - t'⁻¹ ∉ D.Lap (i - s + 1) s) →
      D.Nst ε i s w Y (blk (D.Kr i) s t t') t t' = 0 := by
    intro t ht t' ht' hne hc
    unfold Data.Nst
    rw [Finset.sum_eq_zero, zero_div]
    intro h hh
    refine Finset.sum_eq_zero fun h' hh' => ?_
    have hk0 : D.Kr i (join h s t) (join h' s t') = 0 := by
      by_contra hk
      obtain ⟨h1, h2⟩ := hA2 i s hs hsi hi h h' t t' (hlev h hh) (hlev h' hh') (hS0 t ht)
        (hS0 t' ht') hne hk
      rcases hc with hc | hc
      · exact h1 hc
      · exact hc h2
    simp [blk, hk0]

  have split : ∀ B : E → E → ℝ,
      (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → (D.Nst ε i s w Y (blk (D.Kr i) s t t') t t').re ≤ B t t') →
      (∀ t, 0 ≤ B t t) →
      ∑ t ∈ S, ∑ t' ∈ S, (D.Nst ε i s w Y (blk (D.Kr i) s t t') t t').re ≤
        ∑ t ∈ S, (D.Nst ε i s w Y (blk (D.Kr i) s t t) t t).re + ∑ t ∈ S, ∑ t' ∈ S, B t t' := by
    intro B hB hB0
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t ht => ?_
    have e : (D.Nst ε i s w Y (blk (D.Kr i) s t t) t t).re =
        ∑ t' ∈ S, if t' = t then (D.Nst ε i s w Y (blk (D.Kr i) s t' t') t' t').re else 0 := by
      rw [Finset.sum_ite_eq' S t, if_pos ht]
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t' ht' => ?_
    by_cases htt : t' = t
    · subst htt
      rw [if_pos rfl]
      linarith [hB0 t']
    · rw [if_neg htt, zero_add]
      exact hB t ht t' ht' (Ne.symm htt)
  by_cases htop : i = D.r + 1 ∧ s = 1
  · have h1 := split (fun _ _ => 0)
      (fun t ht t' ht' hne => by rw [hz t ht t' ht' hne (Or.inl htop)]; simp) (fun _ => le_rfl)
    have h2 : 0 ≤ 3 ^ D.f * ep * M := by positivity
    simp only [Finset.sum_const_zero, add_zero] at h1
    linarith
  obtain ⟨θ, hθ, hE⟩ := hEL ε hε i s hs hsi hi htop w hw hcnt
  have hE' := hE Y S (D.Kr i) hlev (hK.1 i _)
  set WW := D.Wb (D.cnt w + D.K) ×ˢ D.Wb (D.cnt w + D.K) with hWW
  set ρ := D.szL (i - s + 1) s with hρ
  set a : W → E → ℝ := fun w' t => (D.Nst ε i s w' Y (blk (D.Kr i) s t t) t t).re with hadef

  let P : E → E → Prop := fun t t' =>
    t ≠ t' ∧ t⁻¹ - t'⁻¹ ∈ D.Lap (i - s + 1) s ∧ 0 ≤ D.maj ρ (t⁻¹ - t'⁻¹)
  let m : E → E → ℝ := fun t t' => if P t t' then D.maj ρ (t⁻¹ - t'⁻¹) else 0
  have hm0 : ∀ t t', 0 ≤ m t t' := by
    intro t t'
    by_cases hP : P t t'
    · simp only [m, if_pos hP]; exact hP.2.2
    · simp only [m, if_neg hP]; exact le_rfl
  have row : ∀ t ∈ S, ∑ t' ∈ S, m t t' ≤ ep := by
    intro t _
    have h1 := hLS.2 i s hs hsi hi htop ((S.filter fun t' => P t t').image fun t' => t⁻¹ - t'⁻¹)
      (by
        intro l hl
        obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hl
        have hP := (Finset.mem_filter.1 ht').2
        exact ⟨hP.2.1, sub_ne_zero.2 fun e => hP.1 (inv_injective e)⟩)
    rw [Finset.sum_image (by
      intro x _ y _ e
      exact inv_injective (sub_right_injective e)), Finset.sum_filter] at h1
    exact h1
  have col : ∀ t' ∈ S, ∑ t ∈ S, m t t' ≤ ep := by
    intro t' _
    have h1 := hLS.2 i s hs hsi hi htop ((S.filter fun t => P t t').image fun t => t⁻¹ - t'⁻¹)
      (by
        intro l hl
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hl
        have hP := (Finset.mem_filter.1 ht).2
        exact ⟨hP.2.1, sub_ne_zero.2 fun e => hP.1 (inv_injective e)⟩)
    rw [Finset.sum_image (by
      intro x _ y _ e
      exact inv_injective (sub_left_injective e)), Finset.sum_filter] at h1
    exact h1
  have hX0 : ∀ π t t', 0 ≤ ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) := by
    intro π t t'
    refine Finset.sum_nonneg fun x _ => mul_nonneg ((hθ π).1 x) ?_
    have := ha x.1 t
    have := ha x.2 t'
    simp only [hadef]
    linarith
  have h1 := split (fun t t' => m t t' * ∑ π, ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2))
    (by
      intro t ht t' ht' hne
      have hG0 : 0 ≤ ∑ π, ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) :=
        Finset.sum_nonneg fun π _ => hX0 π t t'
      by_cases hL : t⁻¹ - t'⁻¹ ∈ D.Lap (i - s + 1) s
      · obtain ⟨π, hπ⟩ := hE' t ht t' ht' (hS0 t ht) (hS0 t' ht')
          (sub_ne_zero.2 fun e => hne (inv_injective e))
        have h2 : (D.Nst ε i s w Y (blk (D.Kr i) s t t') t t').re ≤
            D.maj ρ (t⁻¹ - t'⁻¹) * ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) :=
          le_trans (Complex.re_le_norm _) hπ
        have h3 : ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) ≤
            ∑ π, ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) :=
          Finset.single_le_sum (f := fun π => ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2))
            (fun π _ => hX0 π t t') (Finset.mem_univ π)
        by_cases hmj : 0 ≤ D.maj ρ (t⁻¹ - t'⁻¹)
        · have hP : P t t' := ⟨hne, hL, hmj⟩
          simp only [m, if_pos hP]
          exact le_trans h2 (mul_le_mul_of_nonneg_left h3 hmj)
        · have h4 : D.maj ρ (t⁻¹ - t'⁻¹) * ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (not_le.1 hmj).le (hX0 π t t')
          exact le_trans (le_trans h2 h4) (mul_nonneg (hm0 t t') hG0)
      · rw [hz t ht t' ht' hne (Or.inr hL)]
        exact mul_nonneg (hm0 t t') hG0)
    (fun t => mul_nonneg (hm0 t t) (Finset.sum_nonneg fun π _ => hX0 π t t))
  refine le_trans h1 (add_le_add le_rfl ?_)
  rw [phi_sum]
  have h5 : ∀ π : Fin D.f → Fin 3,
      ∑ t ∈ S, ∑ t' ∈ S, m t t' * ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) ≤ ep * M := by
    intro π
    rw [phi_sum]
    calc ∑ x ∈ WW, ∑ t ∈ S, ∑ t' ∈ S, m t t' * (θ π x * ((a x.1 t + a x.2 t') / 2))
        = ∑ x ∈ WW, θ π x * ∑ t ∈ S, ∑ t' ∈ S, m t t' * ((a x.1 t + a x.2 t') / 2) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t' _ => by ring
      _ ≤ ∑ x ∈ WW, θ π x * (ep * M) := by
          refine Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left ?_ ((hθ π).1 x)
          have hx' := Finset.mem_product.1 hx
          exact schur_real S m ep M hep row col (a x.1) (a x.2) (ha x.1) (ha x.2)
            (hM x.1 hx'.1) (hM x.2 hx'.2)
      _ = ep * M := by rw [← Finset.sum_mul, (hθ π).2.2, one_mul]
  calc ∑ π : Fin D.f → Fin 3,
        ∑ t ∈ S, ∑ t' ∈ S, m t t' * ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2)
      ≤ ∑ _π : Fin D.f → Fin 3, ep * M := Finset.sum_le_sum fun π _ => h5 π
    _ = 3 ^ D.f * ep * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end Formalism.FourierDecayAlt.P
