import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.CommonTransversal

/- English proof (translation)
Take `⟨L, L', D, hD⟩` from `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec a`. Take `⟨P, hP⟩ : ∃ P, P = (L.map Matrix.TransvectionStruct.toMatrix).prod` from `⟨_, rfl⟩`. Take `⟨Q, hQ⟩ : ∃ Q, Q = (L'.map Matrix.TransvectionStruct.toMatrix).prod` from `⟨_, rfl⟩`. Rewrite `hD` using `[← hP, ← hQ]`. Establish `hP1 : P.det = 1` using `by rw [hP]; exact Matrix.TransvectionStruct.det_toMatrix_prod L`.

Establish `hQ1 : Q.det = 1` using `by rw [hQ]; exact Matrix.TransvectionStruct.det_toMatrix_prod L'`. Establish `hst1 : ∀ M : Matrix β β F, M.det = 1 → ((M.map σ)ᵀ).det = 1`. Introduce `M hM`. Rewrite using `[Matrix.det_transpose]`. Establish `e : (M.map σ).det = σ M.det` using `(RingHom.map_det σ M).symm`.

Rewrite using `[e, hM, map_one]`. Establish `cancel : ∀ (M : Matrix β β F) (x : β → F), M.det = 1 → x ᵥ* M = 0 → x = 0`. Introduce `M x hM hx`. Establish `hu : IsUnit M.det` using `by rw [hM]; exact isUnit_one`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨z, hz⟩` from `hz`. Take `⟨c, hcdef⟩ : ∃ c, c = z - σ z` from `⟨_, rfl⟩`. Establish `hc : c ≠ 0` using `by rw [hcdef]; exact sub_ne_zero.2 (Ne.symm hz)`. Establish `hσc : σ c = -c` using `by rw [hcdef, map_sub, hσ]; ring`. Take `⟨s0, hs0⟩ : ∃ s0 : Matrix β β F, s0 = diagonal (fun i => if D i = 0 then c else 0)` from `⟨_, rfl⟩`.

Establish `hss : (s0.map σ)ᵀ = -s0`. Rewrite using `[hs0, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.diagonal_neg]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `split_ifs <;> simp [hσc]`.

Establish `hQQ : ((((Q.map σ)ᵀ).map σ)ᵀ) = Q`. Use extensionality with `i j`. Simplify using `[hσ]`. Establish `hsta : (a.map σ)ᵀ = (Q.map σ)ᵀ * diagonal (fun i => σ (D i)) * (P.map σ)ᵀ`. Rewrite using `[hD, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_assoc]`.

Use `⟨(Q.map σ)ᵀ * s0 * Q, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, hss, hQQ, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc]`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `hdet`. Take `⟨v, hv0, hvM⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 hdet`.

Apply `hv0` to reduce the goal to its premises. Establish `e1 : a + b * ((Q.map σ)ᵀ * s0 * Q) = (P * diagonal D + b * (Q.map σ)ᵀ * s0) * Q`. Rewrite using `[hD]`. Simplify using `only [Matrix.add_mul, Matrix.mul_assoc]`. Establish `h0 : v ᵥ* (P * diagonal D + b * (Q.map σ)ᵀ * s0) = 0` using `cancel Q _ hQ1 (by rw [Matrix.vecMul_vecMul, ← e1]; exact hvM)`.

Establish `h0' : (v ᵥ* P) ᵥ* diagonal D + ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) ᵥ* s0 = 0`. Simplify `h0` using `only [Matrix.vecMul_vecMul, Matrix.vecMul_add]`. Establish `hE : ∀ j, (v ᵥ* P) j * D j + ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) j * (if D j = 0 then c else 0) = 0`. Introduce `j`. Establish `e` using `congr_fun h0' j`.

Rewrite `e` using `[Pi.add_apply, Matrix.vecMul_diagonal, hs0, Matrix.vecMul_diagonal]`. Conclude with `e`. Establish `hwD : (v ᵥ* P) ᵥ* diagonal D = 0`. Use function extensionality and compare the values at `j`. Rewrite using `[Matrix.vecMul_diagonal, Pi.zero_apply]`.

Distinguish the cases in `hDj : D j = 0`. Rewrite using `[hDj, mul_zero]`. Establish `e` using `hE j`. Rewrite `e` using `[if_neg hDj, mul_zero, add_zero]`. Rewrite using `[(mul_eq_zero.1 e).resolve_right hDj, zero_mul]`.

Establish `hva : v ᵥ* a = 0`. Rewrite using `[hD, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hwD, Matrix.zero_vecMul]`. Establish `hc1 : v ᵥ* (a * (b.map σ)ᵀ + b * (a.map σ)ᵀ) = 0` using `by rw [h, Matrix.vecMul_zero]`. Rewrite `hc1` using `[Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hva, Matrix.zero_vecMul, zero_add, hsta, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]`. Establish `hud : ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) ᵥ* diagonal (fun i => σ (D i)) = 0` using `cancel _ _ (hst1 P hP1) hc1`.

Establish `hu : (v ᵥ* b) ᵥ* (Q.map σ)ᵀ = 0`. Use function extensionality and compare the values at `j`. Rewrite using `[Pi.zero_apply]`. Distinguish the cases in `hDj : D j = 0`. Establish `e` using `hE j`.

Rewrite `e` using `[if_pos hDj, hDj, mul_zero, zero_add]`. Conclude with `(mul_eq_zero.1 e).resolve_right hc`. Establish `e` using `congr_fun hud j`. Rewrite `e` using `[Matrix.vecMul_diagonal, Pi.zero_apply]`. Conclude with `(mul_eq_zero.1 e).resolve_right ((map_ne_zero σ).2 hDj)`.

Conclude with `hv v hva (cancel _ _ (hst1 Q hQ1) hu)`.
-/
theorem exists_skew_isUnit_det {F : Type} [Field F] (σ : F →+* F) {β : Type} [Fintype β]
    [DecidableEq β] (a b : Matrix β β F) (hσ : ∀ z, σ (σ z) = z) (hz : ∃ z, σ z ≠ z)
    (h : a * (b.map σ)ᵀ + b * (a.map σ)ᵀ = 0)
    (hv : ∀ v : β → F, Matrix.vecMul v a = 0 → Matrix.vecMul v b = 0 → v = 0) :
    ∃ s : Matrix β β F, (s.map σ)ᵀ = -s ∧ IsUnit (a + b * s).det := by
  classical
  obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec a
  obtain ⟨P, hP⟩ : ∃ P, P = (L.map Matrix.TransvectionStruct.toMatrix).prod := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (L'.map Matrix.TransvectionStruct.toMatrix).prod := ⟨_, rfl⟩
  rw [← hP, ← hQ] at hD
  have hP1 : P.det = 1 := by rw [hP]; exact Matrix.TransvectionStruct.det_toMatrix_prod L
  have hQ1 : Q.det = 1 := by rw [hQ]; exact Matrix.TransvectionStruct.det_toMatrix_prod L'
  have hst1 : ∀ M : Matrix β β F, M.det = 1 → ((M.map σ)ᵀ).det = 1 := by
    intro M hM
    rw [Matrix.det_transpose]
    have e : (M.map σ).det = σ M.det := (RingHom.map_det σ M).symm
    rw [e, hM, map_one]
  have cancel : ∀ (M : Matrix β β F) (x : β → F), M.det = 1 → x ᵥ* M = 0 → x = 0 := by
    intro M x hM hx
    have hu : IsUnit M.det := by rw [hM]; exact isUnit_one
    calc x = x ᵥ* (M * M⁻¹) := by rw [Matrix.mul_nonsing_inv (A := M) hu, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, hx, Matrix.zero_vecMul]
  obtain ⟨z, hz⟩ := hz
  obtain ⟨c, hcdef⟩ : ∃ c, c = z - σ z := ⟨_, rfl⟩
  have hc : c ≠ 0 := by rw [hcdef]; exact sub_ne_zero.2 (Ne.symm hz)
  have hσc : σ c = -c := by rw [hcdef, map_sub, hσ]; ring
  obtain ⟨s0, hs0⟩ : ∃ s0 : Matrix β β F, s0 = diagonal (fun i => if D i = 0 then c else 0) :=
    ⟨_, rfl⟩
  have hss : (s0.map σ)ᵀ = -s0 := by
    rw [hs0, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.diagonal_neg]
    congr 1
    funext i
    split_ifs <;> simp [hσc]
  have hQQ : ((((Q.map σ)ᵀ).map σ)ᵀ) = Q := by
    ext i j
    simp [hσ]
  have hsta : (a.map σ)ᵀ = (Q.map σ)ᵀ * diagonal (fun i => σ (D i)) * (P.map σ)ᵀ := by
    rw [hD, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_assoc]
  refine ⟨(Q.map σ)ᵀ * s0 * Q, ?_, ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, hss, hQQ,
      Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc]
  · rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply hv0
    have e1 : a + b * ((Q.map σ)ᵀ * s0 * Q) = (P * diagonal D + b * (Q.map σ)ᵀ * s0) * Q := by
      rw [hD]
      simp only [Matrix.add_mul, Matrix.mul_assoc]
    have h0 : v ᵥ* (P * diagonal D + b * (Q.map σ)ᵀ * s0) = 0 :=
      cancel Q _ hQ1 (by rw [Matrix.vecMul_vecMul, ← e1]; exact hvM)
    have h0' : (v ᵥ* P) ᵥ* diagonal D + ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) ᵥ* s0 = 0 := by
      simpa only [Matrix.vecMul_vecMul, Matrix.vecMul_add] using h0
    have hE : ∀ j, (v ᵥ* P) j * D j +
        ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) j * (if D j = 0 then c else 0) = 0 := by
      intro j
      have e := congr_fun h0' j
      rw [Pi.add_apply, Matrix.vecMul_diagonal, hs0, Matrix.vecMul_diagonal] at e
      exact e
    have hwD : (v ᵥ* P) ᵥ* diagonal D = 0 := by
      funext j
      rw [Matrix.vecMul_diagonal, Pi.zero_apply]
      by_cases hDj : D j = 0
      · rw [hDj, mul_zero]
      · have e := hE j
        rw [if_neg hDj, mul_zero, add_zero] at e
        rw [(mul_eq_zero.1 e).resolve_right hDj, zero_mul]
    have hva : v ᵥ* a = 0 := by
      rw [hD, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hwD, Matrix.zero_vecMul]
    have hc1 : v ᵥ* (a * (b.map σ)ᵀ + b * (a.map σ)ᵀ) = 0 := by rw [h, Matrix.vecMul_zero]
    rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hva, Matrix.zero_vecMul,
      zero_add, hsta, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul] at hc1
    have hud : ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) ᵥ* diagonal (fun i => σ (D i)) = 0 :=
      cancel _ _ (hst1 P hP1) hc1
    have hu : (v ᵥ* b) ᵥ* (Q.map σ)ᵀ = 0 := by
      funext j
      rw [Pi.zero_apply]
      by_cases hDj : D j = 0
      · have e := hE j
        rw [if_pos hDj, hDj, mul_zero, zero_add] at e
        exact (mul_eq_zero.1 e).resolve_right hc
      · have e := congr_fun hud j
        rw [Matrix.vecMul_diagonal, Pi.zero_apply] at e
        exact (mul_eq_zero.1 e).resolve_right ((map_ne_zero σ).2 hDj)
    exact hv v hva (cancel _ _ (hst1 Q hQ1) hu)

end GlobalTheory.CompanionTheory.CommonTransversal
