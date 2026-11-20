import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin.BdU

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem gram_apply {L : Type} [CommRing L] (s : L →+* L) {a b c : Type} [Fintype a]
    (M : Matrix a b L) (H : Matrix a a L) (N : Matrix a c L) (i : b) (j : c) :
    (cT s M * H * N) i j = ∑ k, ∑ l, s (M k i) * H k l * N l j := by
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, hs]`.
-/
theorem cT_cT_self {L : Type} [CommRing L] (s : L →+* L) (hs : ∀ x, s (s x) = x) {a b : Type}
    (M : Matrix a b L) : cT s (cT s M) = M := by
  ext i j
  simp [cT, hs]

/- English proof (translation)
Use extensionality with `i j`. Establish `e` using `congrFun (congrFun hGH i) j`. Rewrite `e`, the goal using `[gram_apply]`. Distinguish the cases in `hij : b i + b j = 0`. Rewrite using `[← e]`.

Use `Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))` and prove the remaining obligations. Simplify using `only [bd, Matrix.of_apply]`. Distinguish the cases in `hGki : G k i = 0`. Simplify using `[hGki]`. Distinguish the cases in `hGlj : G l j = 0`.

Simplify using `[hGlj]`. Distinguish the cases in `hHkl : H k l = 0`. Simplify using `[hHkl]`. Establish `h1` using `hH k l hHkl`. Establish `h2 : ¬ b i < b k` using `fun hlt => hGki (hG hlt)`.

Establish `h3 : ¬ b j < b l` using `fun hlt => hGlj (hG hlt)`. Establish `hk : b k = b i` using `by omega`. Establish `hl : b l = b j` using `by omega`. Simplify using `[hk, hl]`. Establish `hHij : H i j = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `hij (hH i j hne)`. Rewrite using `[hHij]`. Use `Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => ?_))` and prove the remaining obligations. Simplify using `only [bd, Matrix.of_apply]`.

Distinguish the cases in `hk : b k = b i`. Distinguish the cases in `hl : b l = b j`. Establish `hHkl : H k l = 0`. Assume the negation of the conclusion as `hne`. Use `hH k l hne` as an intermediate fact.

Conclude with `hij (by omega)`. Simplify using `[hHkl]`. Simplify using `[hl]`. Simplify using `[hk]`.
-/
theorem gram_bd {ι L : Type} [Fintype ι] [CommRing L] (s : L →+* L) (b : ι → ℤ)
    (G H : Matrix ι ι L) (hG : G.BlockTriangular b) (hH : ∀ u v, H u v ≠ 0 → b u + b v = 0)
    (hGH : cT s G * H * G = H) : cT s (bd b G) * H * bd b G = H := by
  ext i j
  have e := congrFun (congrFun hGH i) j
  rw [gram_apply] at e ⊢
  by_cases hij : b i + b j = 0
  · rw [← e]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    simp only [bd, Matrix.of_apply]
    by_cases hGki : G k i = 0
    · simp [hGki]
    by_cases hGlj : G l j = 0
    · simp [hGlj]
    by_cases hHkl : H k l = 0
    · simp [hHkl]
    have h1 := hH k l hHkl
    have h2 : ¬ b i < b k := fun hlt => hGki (hG hlt)
    have h3 : ¬ b j < b l := fun hlt => hGlj (hG hlt)
    have hk : b k = b i := by omega
    have hl : b l = b j := by omega
    simp [hk, hl]
  · have hHij : H i j = 0 := by
      by_contra hne
      exact hij (hH i j hne)
    rw [hHij]
    refine Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => ?_))
    simp only [bd, Matrix.of_apply]
    by_cases hk : b k = b i
    · by_cases hl : b l = b j
      · have hHkl : H k l = 0 := by
          by_contra hne
          have := hH k l hne
          exact hij (by omega)
        simp [hHkl]
      · simp [hl]
    · simp [hk]

/- English proof (translation)
Establish `cTm : ∀ {a b c : Type} [Fintype b] (A : Matrix a b L) (B : Matrix b c L), cT s (A * B) = cT s B * cT s A`. Introduce `a b c _ A B`. Unfold `Formalism.UG.cT`. Rewrite using `[Matrix.map_mul, Matrix.transpose_mul]`. Establish `cT1 : cT s (1 : Matrix (Fin n) (Fin n) L) = 1`.

Unfold `Formalism.UG.cT`. Rewrite using `[Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]`. Establish `hQQ : cT s Qi * cT s Q = 1` using `by rw [← cTm, h2, cT1]`. Establish `hGu : cT s (Qi * g * Q) * (cT s Q * J * Q) * (Qi * g * Q) = cT s Q * J * Q`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[cTm, cTm]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = cT s Q * ((cT s g * J * g) * Q) := by`. Rewrite using `[hQQ, h2, Matrix.one_mul, Matrix.one_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = cT s Q * J * Q := by rw [hgJ, Matrix.mul_assoc]`. Establish `hbdu` using `gram_bd s b (Qi * g * Q) (cT s Q * J * Q) hB hH hGu`. Take `⟨u, hu⟩` from `hg`. Establish `hGunit : IsUnit (Qi * g * Q)`. Use `⟨⟨Qi * g * Q, Qi * (↑u⁻¹ : Matrix (Fin n) (Fin n) L) * Q, ?_, ?_⟩, rfl⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [h2, Matrix.mul_one, ← hu, Units.mul_inv, Matrix.mul_one, h1]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = 1 := by rw [h2, Matrix.mul_one, ← hu, Units.inv_mul, Matrix.mul_one, h1]`. Establish `hbdtri : (bd b (Qi * g * Q)).BlockTriangular b`. Introduce `i j hij`. Simplify using `only [bd, Matrix.of_apply]`. Rewrite using `[if_neg (ne_of_gt hij)]`.

Establish `hdet : (bd b (Qi * g * Q)).det = (Qi * g * Q).det`. Rewrite using `[hbdtri.det, hB.det]`. Use `Finset.prod_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Use `congr 1`. Use extensionality with `i j`.

Simplify using `only [Matrix.toSquareBlock_def, Matrix.of_apply, bd]`. Rewrite using `[if_pos (i.2.trans j.2.symm)]`. Establish `hbdunit : IsUnit (bd b (Qi * g * Q))`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, hdet, ← Matrix.isUnit_iff_isUnit_det]`. Conclude with `hGunit`.

Take `⟨w, hw⟩` from `hbdunit`. Use `⟨⟨⟨Q * (↑w : Matrix ι ι L) * Qi, Q * (↑w⁻¹ : Matrix ι ι L) * Qi, ?_, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [h1, Matrix.mul_one, Units.mul_inv, Matrix.mul_one, h2]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [h1, Matrix.mul_one, Units.inv_mul, Matrix.mul_one, h2]`. Use `show Q * (↑w : Matrix ι ι L) * Qi = Q * bd b (Qi * g * Q) * Qi`. Rewrite using `[hw]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[cTm, cTm]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = cT s Qi * ((cT s Q * J * Q) * Qi) := by rw [hbdu]`. Use `_ = (cT s Qi * cT s Q) * J * (Q * Qi) := by simp only [Matrix.mul_assoc]`.

Use `_ = J := by rw [hQQ, h2, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem levi_unitary {ι L : Type} [Fintype ι] [DecidableEq ι] [Field L] (s : L →+* L) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) L) (Q : Matrix (Fin n) ι L) (Qi : Matrix ι (Fin n) L) (b : ι → ℤ)
    (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hH : ∀ u v, (cT s Q * J * Q) u v ≠ 0 → b u + b v = 0)
    (g : Matrix (Fin n) (Fin n) L) (hg : IsUnit g) (hgJ : cT s g * J * g = J)
    (hB : (Qi * g * Q).BlockTriangular b) :
    IsUnit (Q * bd b (Qi * g * Q) * Qi) ∧
      cT s (Q * bd b (Qi * g * Q) * Qi) * J * (Q * bd b (Qi * g * Q) * Qi) = J := by
  have cTm : ∀ {a b c : Type} [Fintype b] (A : Matrix a b L) (B : Matrix b c L),
      cT s (A * B) = cT s B * cT s A := by
    intro a b c _ A B
    unfold Formalism.UG.cT
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have cT1 : cT s (1 : Matrix (Fin n) (Fin n) L) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]
  have hQQ : cT s Qi * cT s Q = 1 := by rw [← cTm, h2, cT1]
  have hGu : cT s (Qi * g * Q) * (cT s Q * J * Q) * (Qi * g * Q) = cT s Q * J * Q := by
    calc cT s (Qi * g * Q) * (cT s Q * J * Q) * (Qi * g * Q)
        = cT s Q * (cT s g * ((cT s Qi * cT s Q) * (J * ((Q * Qi) * (g * Q))))) := by
          rw [cTm, cTm]
          simp only [Matrix.mul_assoc]
      _ = cT s Q * ((cT s g * J * g) * Q) := by
          rw [hQQ, h2, Matrix.one_mul, Matrix.one_mul]
          simp only [Matrix.mul_assoc]
      _ = cT s Q * J * Q := by rw [hgJ, Matrix.mul_assoc]
  have hbdu := gram_bd s b (Qi * g * Q) (cT s Q * J * Q) hB hH hGu
  obtain ⟨u, hu⟩ := hg
  have hGunit : IsUnit (Qi * g * Q) := by
    refine ⟨⟨Qi * g * Q, Qi * (↑u⁻¹ : Matrix (Fin n) (Fin n) L) * Q, ?_, ?_⟩, rfl⟩
    · calc Qi * g * Q * (Qi * (↑u⁻¹ : Matrix (Fin n) (Fin n) L) * Q) = Qi * (g * (Q * Qi) * (↑u⁻¹ : Matrix (Fin n) (Fin n) L)) * Q := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, ← hu, Units.mul_inv, Matrix.mul_one, h1]
    · calc Qi * (↑u⁻¹ : Matrix (Fin n) (Fin n) L) * Q * (Qi * g * Q) = Qi * ((↑u⁻¹ : Matrix (Fin n) (Fin n) L) * (Q * Qi) * g) * Q := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, ← hu, Units.inv_mul, Matrix.mul_one, h1]
  have hbdtri : (bd b (Qi * g * Q)).BlockTriangular b := by
    intro i j hij
    simp only [bd, Matrix.of_apply]
    rw [if_neg (ne_of_gt hij)]
  have hdet : (bd b (Qi * g * Q)).det = (Qi * g * Q).det := by
    rw [hbdtri.det, hB.det]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    congr 1
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, bd]
    rw [if_pos (i.2.trans j.2.symm)]
  have hbdunit : IsUnit (bd b (Qi * g * Q)) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet, ← Matrix.isUnit_iff_isUnit_det]
    exact hGunit
  obtain ⟨w, hw⟩ := hbdunit
  refine ⟨⟨⟨Q * (↑w : Matrix ι ι L) * Qi, Q * (↑w⁻¹ : Matrix ι ι L) * Qi, ?_, ?_⟩, ?_⟩, ?_⟩
  · calc Q * (↑w : Matrix ι ι L) * Qi * (Q * (↑w⁻¹ : Matrix ι ι L) * Qi) = Q * ((↑w : Matrix ι ι L) * (Qi * Q) * (↑w⁻¹ : Matrix ι ι L)) * Qi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, Units.mul_inv, Matrix.mul_one, h2]
  · calc Q * (↑w⁻¹ : Matrix ι ι L) * Qi * (Q * (↑w : Matrix ι ι L) * Qi) = Q * ((↑w⁻¹ : Matrix ι ι L) * (Qi * Q) * (↑w : Matrix ι ι L)) * Qi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, Units.inv_mul, Matrix.mul_one, h2]
  · show Q * (↑w : Matrix ι ι L) * Qi = Q * bd b (Qi * g * Q) * Qi
    rw [hw]
  · calc cT s (Q * bd b (Qi * g * Q) * Qi) * J * (Q * bd b (Qi * g * Q) * Qi)
        = cT s Qi * ((cT s (bd b (Qi * g * Q)) * (cT s Q * J * Q) * bd b (Qi * g * Q)) * Qi) := by
          rw [cTm, cTm]
          simp only [Matrix.mul_assoc]
      _ = cT s Qi * ((cT s Q * J * Q) * Qi) := by rw [hbdu]
      _ = (cT s Qi * cT s Q) * J * (Q * Qi) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hQQ, h2, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Establish `cTm : ∀ {a b c : Type} [Fintype b] (A : Matrix a b L) (B : Matrix b c L), cT s (A * B) = cT s B * cT s A`. Introduce `a b c _ A B`. Unfold `Formalism.UG.cT`. Rewrite using `[Matrix.map_mul, Matrix.transpose_mul]`. Establish `cT1 : cT s (1 : Matrix (Fin r) (Fin r) L) = 1`.

Unfold `Formalism.UG.cT`. Rewrite using `[Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]`. Establish `cT0 : ∀ {a b : Type}, cT s (0 : Matrix a b L) = 0`. Introduce `a b`. Unfold `Formalism.UG.cT`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `hYX : cT s Y * J * X = 1`. Establish `e` using `congrArg (cT s) hXY`. Rewrite `e` using `[cTm, cTm, cT_cT_self s hs, hJ, cT1, ← Matrix.mul_assoc]`.

Conclude with `e`. Establish `hZX : cT s Z * J * X = 0`. Establish `e` using `congrArg (cT s) hXZ`. Rewrite `e` using `[cTm, cTm, cT_cT_self s hs, hJ, cT0, ← Matrix.mul_assoc]`. Conclude with `e`.

Establish `hZY : cT s Z * J * Y = 0`. Establish `e` using `congrArg (cT s) hYZ`. Rewrite `e` using `[cTm, cTm, cT_cT_self s hs, hJ, cT0, ← Matrix.mul_assoc]`. Conclude with `e`. Apply the tactic sequence `rcases u with i | i | i <;> rcases v with j | j | j`.

Establish `e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inl j) = (cT s X * J * X) i j`. Rewrite using `[gram_apply, gram_apply]`. Both sides reduce to the same expression. Rewrite `h` using `[e, hXX]`. Simplify using `at h`.

Establish `e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inr (Sum.inl j)) = (cT s X * J * Z) i j`. Rewrite using `[gram_apply, gram_apply]`. Both sides reduce to the same expression. Rewrite `h` using `[e, hXZ]`. Simplify using `at h`.

Establish `e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inr (Sum.inr j)) = (cT s X * J * Y) i j`. Rewrite using `[gram_apply, gram_apply]`. Both sides reduce to the same expression. Rewrite `h` using `[e, hXY]`. Establish `hij : i = j`.

Assume the negation of the conclusion as `hne`. Conclude with `h (Matrix.one_apply_ne hne)`. Substitute `hij` using the available equality. Use `show (cnt S i - (S.card : ℤ)) + ((S.card : ℤ) - cnt S i) = 0`. Expand and normalize the polynomial expressions, which then agree.

Establish `e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inl i)) (Sum.inl j) = (cT s Z * J * X) i j`. Rewrite using `[gram_apply, gram_apply]`. Both sides reduce to the same expression. Rewrite `h` using `[e, hZX]`. Simplify using `at h`.

Use `show (0 : ℤ) + 0 = 0`. Both sides reduce to the same expression. Establish `e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)) = (cT s Z * J * Y) i j`. Rewrite using `[gram_apply, gram_apply]`. Both sides reduce to the same expression.

Rewrite `h` using `[e, hZY]`. Simplify using `at h`. Establish `e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inl j) = (cT s Y * J * X) i j`. Rewrite using `[gram_apply, gram_apply]`. Both sides reduce to the same expression.

Rewrite `h` using `[e, hYX]`. Establish `hij : i = j`. Assume the negation of the conclusion as `hne`. Conclude with `h (Matrix.one_apply_ne hne)`. Substitute `hij` using the available equality.

Use `show ((S.card : ℤ) - cnt S i) + (cnt S i - (S.card : ℤ)) = 0`. Expand and normalize the polynomial expressions, which then agree. Establish `e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) = (cT s Y * J * Z) i j`. Rewrite using `[gram_apply, gram_apply]`. Both sides reduce to the same expression.

Rewrite `h` using `[e, hYZ]`. Simplify using `at h`. Establish `e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) = (cT s Y * J * Y) i j`. Rewrite using `[gram_apply, gram_apply]`. Both sides reduce to the same expression.

Rewrite `h` using `[e, hYY]`. Simplify using `at h`.
-/
theorem gram_frm_degree {L : Type} [Field L] (s : L →+* L) (hs : ∀ x, s (s x) = x) {n r m : ℕ}
    (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L)
    (hJ : cT s J = J) (hXX : cT s X * J * X = 0) (hYY : cT s Y * J * Y = 0)
    (hXY : cT s X * J * Y = 1) (hXZ : cT s X * J * Z = 0) (hYZ : cT s Y * J * Z = 0)
    (S : Finset (Fin r)) (u v : Idx r m)
    (h : (cT s (frm X Z Y) * J * frm X Z Y) u v ≠ 0) : lev m S u + lev m S v = 0 := by
  have cTm : ∀ {a b c : Type} [Fintype b] (A : Matrix a b L) (B : Matrix b c L),
      cT s (A * B) = cT s B * cT s A := by
    intro a b c _ A B
    unfold Formalism.UG.cT
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have cT1 : cT s (1 : Matrix (Fin r) (Fin r) L) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]
  have cT0 : ∀ {a b : Type}, cT s (0 : Matrix a b L) = 0 := by
    intro a b
    unfold Formalism.UG.cT
    ext i j
    simp
  have hYX : cT s Y * J * X = 1 := by
    have e := congrArg (cT s) hXY
    rw [cTm, cTm, cT_cT_self s hs, hJ, cT1, ← Matrix.mul_assoc] at e
    exact e
  have hZX : cT s Z * J * X = 0 := by
    have e := congrArg (cT s) hXZ
    rw [cTm, cTm, cT_cT_self s hs, hJ, cT0, ← Matrix.mul_assoc] at e
    exact e
  have hZY : cT s Z * J * Y = 0 := by
    have e := congrArg (cT s) hYZ
    rw [cTm, cTm, cT_cT_self s hs, hJ, cT0, ← Matrix.mul_assoc] at e
    exact e
  rcases u with i | i | i <;> rcases v with j | j | j
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inl j) = (cT s X * J * X) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hXX] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inr (Sum.inl j)) = (cT s X * J * Z) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hXZ] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inr (Sum.inr j)) = (cT s X * J * Y) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hXY] at h
    have hij : i = j := by
      by_contra hne
      exact h (Matrix.one_apply_ne hne)
    subst hij
    show (cnt S i - (S.card : ℤ)) + ((S.card : ℤ) - cnt S i) = 0
    ring
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inl i)) (Sum.inl j) = (cT s Z * J * X) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hZX] at h
    simp at h
  · show (0 : ℤ) + 0 = 0
    rfl
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)) = (cT s Z * J * Y) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hZY] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inl j) = (cT s Y * J * X) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hYX] at h
    have hij : i = j := by
      by_contra hne
      exact h (Matrix.one_apply_ne hne)
    subst hij
    show ((S.card : ℤ) - cnt S i) + (cnt S i - (S.card : ℤ)) = 0
    ring
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) = (cT s Y * J * Z) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hYZ] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) = (cT s Y * J * Y) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hYY] at h
    simp at h

/- English proof (translation)
Introduce `L _ s hs n r m J X Y Z Qi hJ hXX hYY hXY hXZ hYZ h1 h2 S g hg hgJ hB`. Conclude with `levi_unitary s J (frm X Z Y) Qi (lev m S) h1 h2 (fun u v h => gram_frm_degree s hs J X Y Z hJ hXX hYY hXY hXZ hYZ S u v h) g hg hgJ hB`.
-/
theorem bd_unitary : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (Qi * g * frm X Z Y).BlockTriangular (lev m S) → IsUnit (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) ∧ cT s (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) * J * (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) = J := by
  intro L _ s hs n r m J X Y Z Qi hJ hXX hYY hXY hXZ hYZ h1 h2 S g hg hgJ hB
  exact levi_unitary s J (frm X Z Y) Qi (lev m S) h1 h2
    (fun u v h => gram_frm_degree s hs J X Y Z hJ hXX hYY hXY hXZ hYZ S u v h) g hg hgJ hB

end GlobalTheory.CompanionTheory.CFin.BdU

end
