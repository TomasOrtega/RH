import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmEqSumFilterPermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurMulDetEqDetStatement
open scoped Classical

open MvPolynomial in
/- English proof (translation)
Establish `h : (Matrix.of fun i j : Fin n => (X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) = (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin n) ℤ))).submatrix id Fin.revPerm`. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply, id, Fin.revPerm_apply, Fin.val_rev]`. Rewrite using `[show n - 1 - (j : ℕ) = n - ((j : ℕ) + 1) by omega]`. Rewrite using `[h, Matrix.det_permute']`.

Use `mul_ne_zero (by simp [Units.ne_zero]) ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_vandermonde_ne_zero_iff]`. Conclude with `MvPolynomial.X_injective`.
-/
theorem GlobalTheory.JSW.PieriDeterminant.vdm_ne (n : ℕ) : Matrix.det (Matrix.of fun i j : Fin n => (X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) ≠ 0 := by
  have h : (Matrix.of fun i j : Fin n => (X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin n) ℤ))).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply, id, Fin.revPerm_apply, Fin.val_rev]
    rw [show n - 1 - (j : ℕ) = n - ((j : ℕ) + 1) by omega]
  rw [h, Matrix.det_permute']
  refine mul_ne_zero (by simp [Units.ne_zero]) ?_
  rw [Matrix.det_vandermonde_ne_zero_iff]
  exact MvPolynomial.X_injective

namespace GlobalTheory.JSW.PieriDeterminant

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro a b h1 h2 h3 h4; exact ⟨a, b, by omega, h2, h3, h4⟩`. Consider the case `succ d ih`. Introduce `a b h1 h2 h3 h4`.

Establish `hc : (a : ℕ) + 1 < n` using `by have := b.isLt; omega`. Set `c : Fin n` to `⟨a + 1, hc⟩`. Establish `hac : a ≤ c` using `by show (a : ℕ) ≤ a + 1; omega`. Establish `hcb : c ≤ b` using `by show (a : ℕ) + 1 ≤ b; omega`. Establish `hlc : l c = l a` using `le_antisymm (hl hac) (h2 ▸ hl hcb)`.

Distinguish the cases in `hcJ : c ∈ J`. Conclude with `⟨a, c, rfl, hlc.symm, h3, hcJ⟩`. Conclude with `ih c b (by show (b : ℕ) = a + 1 + d + 1; omega) (hlc.trans h2) hcJ h4`.
-/
theorem adj {n : ℕ} (l : Fin n → ℕ) (hl : Antitone l) (J : Finset (Fin n)) :
    ∀ d : ℕ, ∀ a b : Fin n, (b : ℕ) = a + d + 1 → l a = l b → a ∉ J → b ∈ J →
      ∃ a' b' : Fin n, (b' : ℕ) = a' + 1 ∧ l a' = l b' ∧ a' ∉ J ∧ b' ∈ J := by
  intro d
  induction d with
  | zero => intro a b h1 h2 h3 h4; exact ⟨a, b, by omega, h2, h3, h4⟩
  | succ d ih =>
    intro a b h1 h2 h3 h4
    have hc : (a : ℕ) + 1 < n := by have := b.isLt; omega
    let c : Fin n := ⟨a + 1, hc⟩
    have hac : a ≤ c := by show (a : ℕ) ≤ a + 1; omega
    have hcb : c ≤ b := by show (a : ℕ) + 1 ≤ b; omega
    have hlc : l c = l a := le_antisymm (hl hac) (h2 ▸ hl hcb)
    by_cases hcJ : c ∈ J
    · exact ⟨a, c, rfl, hlc.symm, h3, hcJ⟩
    · exact ih c b (by show (b : ℕ) = a + 1 + d + 1; omega) (hlc.trans h2) hcJ h4

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab, hlt⟩ : ∃ a b : Fin n, a ≤ b ∧ ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) a < ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) b := by`. Simplify using `only [Antitone, not_forall, not_le] at hJ`. Take `⟨a, b, h1, h2⟩` from `hJ`. Conclude with `⟨a, b, h1, h2⟩`. Simplify using `only [Pi.add_apply] at hlt`.

Establish `hla` using `hl hab`. Apply the tactic sequence `have hA : a ∉ J := by intro h; simp only [h, if_true] at hlt; split_ifs at hlt <;> omega`. Apply the tactic sequence `have hB : b ∈ J := by by_contra h; simp only [h, if_false] at hlt; split_ifs at hlt <;> omega`. Establish `hE : l a = l b` using `by simp only [hA, hB, if_true, if_false] at hlt; omega`. Establish `hne : a ≠ b` using `by rintro rfl; exact hA hB`.

Take `⟨a', b', h1, h2, h3, h4⟩` from `adj l hl J ((b : ℕ) - a - 1) a b (by have : (a : ℕ) < b := lt_of_le_of_ne hab (fun h => hne (Fin.ext h)); omega) hE hA hB`. Use `Matrix.det_zero_of_column_eq (i := a') (j := b') (fun h => by rw [h] at h1; omega) (fun i => ?_)` and prove the remaining obligations. Simplify using `only [Matrix.of_apply, h3, h4, if_true, if_false]`. Use `congr 1`. Use `b'.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem det_zero {n : ℕ} (l : Fin n → ℕ) (hl : Antitone l) (J : Finset (Fin n))
    (hJ : ¬ Antitone (l + (fun i => if i ∈ J then 1 else 0))) :
    Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
      ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) = 0 := by
  obtain ⟨a, b, hab, hlt⟩ : ∃ a b : Fin n, a ≤ b ∧ ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) a <
      ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) b := by
    simp only [Antitone, not_forall, not_le] at hJ
    obtain ⟨a, b, h1, h2⟩ := hJ; exact ⟨a, b, h1, h2⟩
  simp only [Pi.add_apply] at hlt
  have hla := hl hab
  have hA : a ∉ J := by intro h; simp only [h, if_true] at hlt; split_ifs at hlt <;> omega
  have hB : b ∈ J := by by_contra h; simp only [h, if_false] at hlt; split_ifs at hlt <;> omega
  have hE : l a = l b := by simp only [hA, hB, if_true, if_false] at hlt; omega
  have hne : a ≠ b := by rintro rfl; exact hA hB
  obtain ⟨a', b', h1, h2, h3, h4⟩ :=
    adj l hl J ((b : ℕ) - a - 1) a b (by have : (a : ℕ) < b := lt_of_le_of_ne hab (fun h => hne (Fin.ext h)); omega) hE hA hB
  refine Matrix.det_zero_of_column_eq (i := a') (j := b') (fun h => by rw [h] at h1; omega) (fun i => ?_)
  simp only [Matrix.of_apply, h3, h4, if_true, if_false]
  congr 1
  have := b'.isLt
  omega

end GlobalTheory.JSW.PieriDeterminant

open MvPolynomial in
/- English proof (translation)
Introduce `n l hl j _`. Apply `mul_right_cancel₀ (GlobalTheory.JSW.PieriDeterminant.vdm_ne n)` to reduce the goal to its premises. Establish `h1` using `GlobalTheory.T.esymm_mul_det_pow_eq_sum_det_shifted n (fun k => l k + n - 1 - k) j`. Use `beta_reduce at h1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, GlobalTheory.T.schur_mul_vandermonde_det_eq_det n l hl, h1]`. Use `_ = ∑ J ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j)).filter (fun J => Antitone (l + (fun i => if i ∈ J then 1 else 0))), Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 e …`. Use `(Finset.sum_filter_of_ne fun J _ hJ => ?_).symm` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hJ (GlobalTheory.JSW.PieriDeterminant.det_zero l hl J h)`.

Use `_ = ∑ J ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j)).filter (fun J => Antitone (l + (fun i => if i ∈ J then 1 else 0))), GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) * Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvP …`. Use `Finset.sum_congr rfl fun J hJ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.schur_mul_vandermonde_det_eq_det n _ (Finset.mem_filter.1 hJ).2]`. Establish `e : ∀ k : Fin n, ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) k + n - 1 - (k : ℕ) = (l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0`. Apply the tactic sequence `intro k; have := k.isLt; simp only [Pi.add_apply]; split_ifs <;> omega`.

Simplify using `only [e]`. Use `_ = _ := by rw [Finset.filter_filter, Finset.sum_mul]`.
-/
theorem GlobalTheory.JSW.esymm_mul_schur : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → ∀ j ≤ n, MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j ∧ Antitone (l + (fun i => if i ∈ J then 1 else 0))), GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) := by
  intro n l hl j _
  apply mul_right_cancel₀ (GlobalTheory.JSW.PieriDeterminant.vdm_ne n)
  have h1 := GlobalTheory.T.esymm_mul_det_pow_eq_sum_det_shifted n (fun k => l k + n - 1 - k) j
  beta_reduce at h1
  calc MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l * _
      = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j),
          Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
            ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) := by
        rw [mul_assoc, GlobalTheory.T.schur_mul_vandermonde_det_eq_det n l hl, h1]
    _ = ∑ J ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j)).filter
          (fun J => Antitone (l + (fun i => if i ∈ J then 1 else 0))),
          Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
            ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) := by
        refine (Finset.sum_filter_of_ne fun J _ hJ => ?_).symm
        by_contra h
        exact hJ (GlobalTheory.JSW.PieriDeterminant.det_zero l hl J h)
    _ = ∑ J ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j)).filter
          (fun J => Antitone (l + (fun i => if i ∈ J then 1 else 0))),
          GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) *
            Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        rw [GlobalTheory.T.schur_mul_vandermonde_det_eq_det n _ (Finset.mem_filter.1 hJ).2]
        have e : ∀ k : Fin n, ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) k + n - 1 - (k : ℕ) =
            (l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0 := by
          intro k; have := k.isLt; simp only [Pi.add_apply]; split_ifs <;> omega
        simp only [e]
    _ = _ := by rw [Finset.filter_filter, Finset.sum_mul]
