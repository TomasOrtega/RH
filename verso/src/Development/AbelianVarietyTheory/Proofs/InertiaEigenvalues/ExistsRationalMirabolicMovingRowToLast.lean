import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

/- English proof (translation)
Introduce `E _ _ a m hma ξ hξ`. Use `set mm : Fin a := ⟨m, by omega⟩ with hmm`. Use `set c : Fin a := ⟨m + 1, hma⟩ with hc`. Set `v : Fin a → E` to `fun k => if h : (k : ℕ) ≤ m then ξ ⟨(k, c), by simp [hc]; omega⟩ else 0`. Establish `hv : ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), v t.1.1 = ξ t`.

Introduce `t`. Establish `h1` using `t.2`. Establish `hle : (t.1.1 : ℕ) ≤ m` using `by omega`. Simplify using `only [v, dif_pos hle]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Both sides reduce to the same expression. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[hc]`.

Use linear arithmetic over natural numbers and integers. Take `⟨t₀, ht₀⟩` from `Function.ne_iff.1 hξ`. Use `set i₀ : Fin a := t₀.1.1 with hi₀`. Establish `hi₀m : (i₀ : ℕ) ≤ m` using `by have := t₀.2; omega`. Establish `hvi₀ : v i₀ ≠ 0` using `by rw [hi₀, hv]; exact ht₀`.

Set `M : Matrix (Fin a) (Fin a) E` to `Matrix.of fun i k => if i = mm then v k else if i = i₀ then (if k = mm then 1 else 0) else (1 : Matrix (Fin a) (Fin a) E) i k`. Establish `hdet : M.det ≠ 0`. Introduce `h0`. Take `⟨x, hx0, hx⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Establish `hrow : ∀ j, (M *ᵥ x) j = 0` using `fun j => by rw [hx]; rfl`.

Establish `hoff : ∀ j, j ≠ i₀ → x j = 0`. Introduce `j hj`. Distinguish the cases in `hjm : j = mm`. Establish `hi₀ne : i₀ ≠ mm` using `hjm ▸ Ne.symm hj`. Use `hrow i₀` as an intermediate fact.

Simplify `this` using `[M, Matrix.mulVec, dotProduct, hi₀ne, hjm]`. Use `hrow j` as an intermediate fact. Simplify `this` using `[M, Matrix.mulVec, dotProduct, hjm, hj, Matrix.one_apply]`. Apply `hx0` to reduce the goal to its premises. Use function extensionality and compare the values at `j`.

Distinguish the cases in `hj : j = i₀`. Substitute `hj` using the available equality. Use `hrow mm` as an intermediate fact. Simplify using `only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, if_true] at this`. Rewrite `this` using `[Finset.sum_eq_single i₀ (fun k _ hk => by rw [hoff k hk, mul_zero]) (by simp)]`.

Conclude with `(mul_eq_zero.1 this).resolve_left hvi₀`. Conclude with `hoff j hj`. Establish `hu : IsUnit M` using `(Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)`. Use `⟨hu.unit, ?_, ?_⟩` and prove the remaining obligations. Introduce `i k hik`.

Rewrite using `[IsUnit.unit_spec]`. Simplify using `only [M, Matrix.of_apply]`. Break down `hik with hi | hk` into its components or cases. Establish `h1 : i ≠ mm` using `fun e => by rw [e] at hi; simp [hmm] at hi`. Establish `h2 : i ≠ i₀` using `fun e => by rw [e] at hi; omega`.

Simplify using `[h1, h2]`. Establish `h1 : k ≠ mm` using `fun e => by rw [e] at hk; simp [hmm] at hk`. Establish `h2 : k ≠ i₀` using `fun e => by rw [e] at hk; omega`. Use `split_ifs with e1 e2`. Substitute `e1` using the available equality.

Simplify using `only [v, Matrix.one_apply, h1.symm, if_false]`. Rewrite using `[dif_neg (by omega)]`. Simplify using `[e2, Matrix.one_apply, Ne.symm h2]`. Both sides reduce to the same expression. Introduce `t`.

Rewrite using `[IsUnit.unit_spec]`. Establish `hs : ∃ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), s.1.1 = mm` using `⟨⟨(mm, c), by simp [hmm, hc]⟩, rfl⟩`. Take `⟨s₀, hs₀⟩` from `hs`. Rewrite using `[Finset.sum_eq_single s₀]`. Simplify using `only [eLast, hs₀, hmm, M, Matrix.of_apply, if_true, one_mul]`.

Conclude with `hv t`. Introduce `s _ hs`. Establish `: ¬ ((s.1.1 : ℕ) + 1 = m + 1)`. Introduce `e`. Apply `hs` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `s.2`. Establish `h2` using `s₀.2`. Apply `Prod.ext` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises.

Rewrite using `[hs₀]`. Simplify using `[hmm]`. Use linear arithmetic over natural numbers and integers. Apply `Fin.ext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.

Simplify using `only [eLast, if_neg this, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem mir_exists_row : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ), m + 1 < a →
    ∀ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, ξ ≠ 0 → ∃ γ : GL (Fin a) E, IsMir (m + 1) γ ∧
      ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1 = ξ t := by
  intro E _ _ a m hma ξ hξ
  classical
  set mm : Fin a := ⟨m, by omega⟩ with hmm
  set c : Fin a := ⟨m + 1, hma⟩ with hc
  let v : Fin a → E := fun k => if h : (k : ℕ) ≤ m then ξ ⟨(k, c), by simp [hc]; omega⟩ else 0
  have hv : ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), v t.1.1 = ξ t := by
    intro t
    have h1 := t.2
    have hle : (t.1.1 : ℕ) ≤ m := by omega
    simp only [v, dif_pos hle]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext; simp [hc]; omega
  obtain ⟨t₀, ht₀⟩ := Function.ne_iff.1 hξ
  set i₀ : Fin a := t₀.1.1 with hi₀
  have hi₀m : (i₀ : ℕ) ≤ m := by have := t₀.2; omega
  have hvi₀ : v i₀ ≠ 0 := by rw [hi₀, hv]; exact ht₀
  let M : Matrix (Fin a) (Fin a) E := Matrix.of fun i k =>
    if i = mm then v k else if i = i₀ then (if k = mm then 1 else 0) else (1 : Matrix (Fin a) (Fin a) E) i k
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hrow : ∀ j, (M *ᵥ x) j = 0 := fun j => by rw [hx]; rfl
    have hoff : ∀ j, j ≠ i₀ → x j = 0 := by
      intro j hj
      by_cases hjm : j = mm
      · have hi₀ne : i₀ ≠ mm := hjm ▸ Ne.symm hj
        have := hrow i₀
        simpa [M, Matrix.mulVec, dotProduct, hi₀ne, hjm] using this
      · have := hrow j
        simpa [M, Matrix.mulVec, dotProduct, hjm, hj, Matrix.one_apply] using this
    apply hx0
    funext j
    by_cases hj : j = i₀
    · subst hj
      have := hrow mm
      simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, if_true] at this
      rw [Finset.sum_eq_single i₀ (fun k _ hk => by rw [hoff k hk, mul_zero]) (by simp)] at this
      exact (mul_eq_zero.1 this).resolve_left hvi₀
    · exact hoff j hj
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)
  refine ⟨hu.unit, ?_, ?_⟩
  · intro i k hik
    rw [IsUnit.unit_spec]
    simp only [M, Matrix.of_apply]
    rcases hik with hi | hk
    · have h1 : i ≠ mm := fun e => by rw [e] at hi; simp [hmm] at hi
      have h2 : i ≠ i₀ := fun e => by rw [e] at hi; omega
      simp [h1, h2]
    · have h1 : k ≠ mm := fun e => by rw [e] at hk; simp [hmm] at hk
      have h2 : k ≠ i₀ := fun e => by rw [e] at hk; omega
      split_ifs with e1 e2
      · subst e1
        simp only [v, Matrix.one_apply, h1.symm, if_false]
        rw [dif_neg (by omega)]
      · simp [e2, Matrix.one_apply, Ne.symm h2]
      · rfl
  · intro t
    rw [IsUnit.unit_spec]
    have hs : ∃ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), s.1.1 = mm := ⟨⟨(mm, c), by simp [hmm, hc]⟩, rfl⟩
    obtain ⟨s₀, hs₀⟩ := hs
    rw [Finset.sum_eq_single s₀]
    · simp only [eLast, hs₀, hmm, M, Matrix.of_apply, if_true, one_mul]
      exact hv t
    · intro s _ hs
      have : ¬ ((s.1.1 : ℕ) + 1 = m + 1) := by
        intro e
        apply hs
        apply Subtype.ext
        have h1 := s.2; have h2 := s₀.2
        apply Prod.ext
        · apply Fin.ext; rw [hs₀]; simp [hmm]; omega
        · apply Fin.ext; omega
      simp only [eLast, if_neg this, zero_mul]
    · simp

end GlobalTheory.CuspGeneric
