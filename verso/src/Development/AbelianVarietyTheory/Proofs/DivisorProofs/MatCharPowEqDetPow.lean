import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTvalNeZero
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim

noncomputable section

namespace GlobalTheory.DefPt

open Matrix

section Char

variable {K : Type} [Field K] {n : ℕ} (χ : Matrix (Fin n) (Fin n) K →* K)

/- English proof (translation)
Establish `h1 : ∀ N : Matrix (Fin n) (Fin n) K, σ.toPEquiv.toMatrix * N * σ.symm.toPEquiv.toMatrix = N.submatrix σ σ`. Introduce `N`. Rewrite using `[PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm, submatrix_submatrix]`. Both sides reduce to the same expression. Establish `h2` using `congrArg χ (h1 1)`.

Rewrite `h2` using `[submatrix_one_equiv, Matrix.mul_one, map_mul, map_one]`. Rewrite using `[← h1 M, map_mul, map_mul, mul_comm (χ _) (χ M), mul_assoc, h2, mul_one]`.
-/
theorem matChar_submatrix (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) K) :
    χ (M.submatrix σ σ) = χ M := by
  have h1 : ∀ N : Matrix (Fin n) (Fin n) K,
      σ.toPEquiv.toMatrix * N * σ.symm.toPEquiv.toMatrix = N.submatrix σ σ := by
    intro N
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm, submatrix_submatrix]
    rfl
  have h2 := congrArg χ (h1 1)
  rw [submatrix_one_equiv, Matrix.mul_one, map_mul, map_one] at h2
  rw [← h1 M, map_mul, map_mul, mul_comm (χ _) (χ M), mul_assoc, h2, mul_one]

/- English proof (translation)
Use `set D : Matrix (Fin n) (Fin n) K := diagonal (Function.update 1 i 2)`. Use `set D' : Matrix (Fin n) (Fin n) K := diagonal (Function.update 1 i (1 / 2))`. Establish `hDD : D * D' = 1`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hk]`.

Establish `hD : χ D ≠ 0` using `fun h => by`. Use `congrArg χ hDD` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, h, zero_mul]`. Conclude with `zero_ne_one this`. Establish `hT : χ (transvection i j c) ≠ 0` using `fun h => by`.

Use `congrArg χ (transvection_mul_transvection_same i j hij c (-c))` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, transvection_zero, map_mul, map_one, h, zero_mul]`. Conclude with `zero_ne_one this`. Establish `hcomm : D * transvection i j c = transvection i j (c + c) * D`. Use extensionality with `a b`.

Rewrite using `[diagonal_mul, mul_diagonal]`. Establish `hdi : Function.update (1 : Fin n → K) i 2 i = 2` using `by simp`. Establish `hdj : Function.update (1 : Fin n → K) i 2 j = 1` using `by simp [Ne.symm hij]`. Simplify using `only [transvection, Matrix.add_apply, Matrix.single_apply]`. Distinguish the cases in `h : a = i ∧ b = j`.

Take `⟨rfl, rfl⟩` from `h`. Rewrite using `[Matrix.one_apply_ne hij, hdi, hdj]`. Simplify using `only [and_self, ite_true]`. Expand and normalize the polynomial expressions, which then agree. Establish `h' : ¬(i = a ∧ j = b)` using `fun h' => h ⟨h'.1.symm, h'.2.symm⟩`.

Rewrite using `[if_neg h', if_neg h']`. Simplify using `only [add_zero]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Matrix.one_apply_ne hab]`. Expand and normalize the polynomial expressions, which then agree. Establish `e` using `congrArg χ hcomm`. Rewrite `e` using `[map_mul, map_mul, ← transvection_mul_transvection_same i j hij, map_mul, mul_comm (χ D)]`. Establish `e2 : χ (transvection i j c) * 1 = χ (transvection i j c) * χ (transvection i j c)`.

Rewrite using `[mul_one]`. Conclude with `mul_right_cancel₀ hD e`. Conclude with `(mul_left_cancel₀ hT e2).symm`.
-/
theorem matChar_transvection [CharZero K] {i j : Fin n} (hij : i ≠ j) (c : K) :
    χ (transvection i j c) = 1 := by
  set D : Matrix (Fin n) (Fin n) K := diagonal (Function.update 1 i 2)
  set D' : Matrix (Fin n) (Fin n) K := diagonal (Function.update 1 i (1 / 2))
  have hDD : D * D' = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  have hD : χ D ≠ 0 := fun h => by
    have := congrArg χ hDD
    rw [map_mul, map_one, h, zero_mul] at this
    exact zero_ne_one this
  have hT : χ (transvection i j c) ≠ 0 := fun h => by
    have := congrArg χ (transvection_mul_transvection_same i j hij c (-c))
    rw [add_neg_cancel, transvection_zero, map_mul, map_one, h, zero_mul] at this
    exact zero_ne_one this
  have hcomm : D * transvection i j c = transvection i j (c + c) * D := by
    ext a b
    rw [diagonal_mul, mul_diagonal]
    have hdi : Function.update (1 : Fin n → K) i 2 i = 2 := by simp
    have hdj : Function.update (1 : Fin n → K) i 2 j = 1 := by simp [Ne.symm hij]
    simp only [transvection, Matrix.add_apply, Matrix.single_apply]
    by_cases h : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h
      rw [Matrix.one_apply_ne hij, hdi, hdj]
      simp only [and_self, ite_true]
      ring
    · have h' : ¬(i = a ∧ j = b) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
      rw [if_neg h', if_neg h']
      simp only [add_zero]
      by_cases hab : a = b
      · subst hab; ring
      · rw [Matrix.one_apply_ne hab]; ring
  have e := congrArg χ hcomm
  rw [map_mul, map_mul, ← transvection_mul_transvection_same i j hij, map_mul, mul_comm (χ D)] at e
  have e2 : χ (transvection i j c) * 1 = χ (transvection i j c) * χ (transvection i j c) := by
    rw [mul_one]
    exact mul_right_cancel₀ hD e
  exact (mul_left_cancel₀ hT e2).symm

/- English proof (translation)
Rewrite using `[← matChar_submatrix χ (Equiv.swap k k') (diagonal (Pi.mulSingle k' a)), submatrix_diagonal_equiv]`. Use `congr 2`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, Pi.mulSingle_apply]`. Distinguish the cases in `hx : x = k`.

Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Distinguish the cases in `hx' : x = k'`. Substitute `hx'` using the available equality. Rewrite using `[Equiv.swap_apply_right]`.

Simplify using `[hx, Ne.symm hx]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne hx hx']`. Simplify using `[hx, hx']`.
-/
theorem matChar_mulSingle (k k' : Fin n) (a : K) :
    χ (diagonal (Pi.mulSingle k a)) = χ (diagonal (Pi.mulSingle k' a)) := by
  rw [← matChar_submatrix χ (Equiv.swap k k') (diagonal (Pi.mulSingle k' a)), submatrix_diagonal_equiv]
  congr 2
  funext x
  simp only [Function.comp_apply, Pi.mulSingle_apply]
  by_cases hx : x = k
  · subst hx; simp
  · by_cases hx' : x = k'
    · subst hx'; rw [Equiv.swap_apply_right]; simp [hx, Ne.symm hx]
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']; simp [hx, hx']

/- English proof (translation)
Set `ψ : (Fin n → K) →* K` to `χ.comp (diagonalRingHom (Fin n) K).toMonoidHom`. Establish `hψ : ∀ v, ψ v = χ (diagonal v)` using `fun v => rfl`. Establish `hone : ∀ (k : Fin n) (a : K), χ (diagonal (Pi.mulSingle k a)) ^ n = a ^ m`. Introduce `k a`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.prod_congr rfl fun k' _ => (hψ _).trans (matChar_mulSingle χ k' k a), Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Use `_ = ψ (fun _ => a) := by rw [← map_prod, Finset.univ_prod_mulSingle]`. Use `_ = a ^ m := by rw [hψ, ← smul_one_eq_diagonal, hs]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← map_prod, Finset.univ_prod_mulSingle, hψ]`.

Use `_ = ∏ k, d k ^ m := by`. Rewrite using `[← Finset.prod_pow]`. Conclude with `Finset.prod_congr rfl fun k _ => hone k (d k)`. Use `_ = (diagonal d).det ^ m := by rw [det_diagonal, Finset.prod_pow]`.
-/
theorem matChar_diagonal_pow (m : ℕ) (hs : ∀ t : K, χ (t • 1) = t ^ m) (d : Fin n → K) :
    χ (diagonal d) ^ n = (diagonal d).det ^ m := by
  let ψ : (Fin n → K) →* K := χ.comp (diagonalRingHom (Fin n) K).toMonoidHom
  have hψ : ∀ v, ψ v = χ (diagonal v) := fun v => rfl
  have hone : ∀ (k : Fin n) (a : K), χ (diagonal (Pi.mulSingle k a)) ^ n = a ^ m := by
    intro k a
    calc χ (diagonal (Pi.mulSingle k a)) ^ n = ∏ k' : Fin n, ψ (Pi.mulSingle k' a) := by
          rw [Finset.prod_congr rfl fun k' _ => (hψ _).trans (matChar_mulSingle χ k' k a), Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
      _ = ψ (fun _ => a) := by rw [← map_prod, Finset.univ_prod_mulSingle]
      _ = a ^ m := by rw [hψ, ← smul_one_eq_diagonal, hs]
  calc χ (diagonal d) ^ n = (∏ k, ψ (Pi.mulSingle k (d k))) ^ n := by
        rw [← map_prod, Finset.univ_prod_mulSingle, hψ]
    _ = ∏ k, d k ^ m := by
        rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun k _ => hone k (d k)
    _ = (diagonal d).det ^ m := by rw [det_diagonal, Finset.prod_pow]

/- English proof (translation)
Use `diagonal_transvection_induction (fun M => χ M ^ n = M.det ^ m) g (fun D _ => matChar_diagonal_pow χ m hs D) (fun t => ?_) (fun A B hA hB => ?_)` and prove the remaining obligations. Use `show χ t.toMatrix ^ n = t.toMatrix.det ^ m`. Rewrite using `[show t.toMatrix = transvection t.i t.j t.c from rfl, matChar_transvection χ t.hij, det_transvection_of_ne _ _ t.hij]`. Simplify using the standard rewrite rules. Use `show χ (A * B) ^ n = (A * B).det ^ m`.

Establish `hA' : χ A ^ n = A.det ^ m` using `hA`. Establish `hB' : χ B ^ n = B.det ^ m` using `hB`. Rewrite using `[map_mul, det_mul, mul_pow, mul_pow, hA', hB']`.
-/
theorem matChar_pow_eq_det_pow [CharZero K] (m : ℕ) (hs : ∀ t : K, χ (t • 1) = t ^ m)
    (g : Matrix (Fin n) (Fin n) K) : χ g ^ n = g.det ^ m := by
  refine diagonal_transvection_induction (fun M => χ M ^ n = M.det ^ m) g
    (fun D _ => matChar_diagonal_pow χ m hs D) (fun t => ?_) (fun A B hA hB => ?_)
  · show χ t.toMatrix ^ n = t.toMatrix.det ^ m
    rw [show t.toMatrix = transvection t.i t.j t.c from rfl, matChar_transvection χ t.hij,
      det_transvection_of_ne _ _ t.hij]
    simp
  · show χ (A * B) ^ n = (A * B).det ^ m
    have hA' : χ A ^ n = A.det ^ m := hA
    have hB' : χ B ^ n = B.det ^ m := hB
    rw [map_mul, det_mul, mul_pow, mul_pow, hA', hB']

end Char

end GlobalTheory.DefPt

namespace GlobalTheory.DefPt

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine MvPolynomial
open scoped Matrix

def rhoDetHom {n : ℕ} (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] : Matrix (Fin n) (Fin n) K →* K where
  toFun g := (GlobalTheory.DefPt.rhoMat la g).det
  map_one' := by rw [Model.rhoMat_one, Matrix.det_one]
  map_mul' g h := by rw [Model.rhoMat_mul, Matrix.det_mul, mul_comm]

/- English proof (translation)
Introduce `K _ _ n la _ g`. Establish `hs : ∀ t : K, rhoDetHom la K (t • 1) = t ^ (size la * dim la)`. Introduce `t`. Use `show (GlobalTheory.DefPt.rhoMat la (t • 1)).det = _`. Rewrite using `[Model.rhoMat_scalar, Matrix.det_smul, Matrix.det_one, mul_one, dim_eq_card, pow_mul]`.

Conclude with `matChar_pow_eq_det_pow (rhoDetHom la K) _ hs g`.
-/
theorem det_rhoMat_pow : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (la : Fin n → ℕ), Antitone la →
    ∀ g : Matrix (Fin n) (Fin n) K, (rhoMat la g).det ^ n = g.det ^ (size la * dim la) := by
  intro K _ _ n la _ g
  have hs : ∀ t : K, rhoDetHom la K (t • 1) = t ^ (size la * dim la) := by
    intro t
    show (GlobalTheory.DefPt.rhoMat la (t • 1)).det = _
    rw [Model.rhoMat_scalar, Matrix.det_smul, Matrix.det_one, mul_one, dim_eq_card, pow_mul]
  exact matChar_pow_eq_det_pow (rhoDetHom la K) _ hs g

end GlobalTheory.DefPt

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial in
open scoped Matrix in
/- English proof (translation)
The claim follows from `GlobalTheory.DefPt.det_rhoMat_pow`.
-/
example : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ g : Matrix (Fin n) (Fin n) K, (rhoMat la g).det ^ n = g.det ^ (size la * dim la) :=
  GlobalTheory.DefPt.det_rhoMat_pow
