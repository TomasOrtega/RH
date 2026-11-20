import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnitaryZariskiDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Matrix Complex

noncomputable section

namespace UnitaryZariskiDense

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq, map_add]`. Consider the case `mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]`.
-/
theorem eval_aeval_subst {σ τ : Type*} (F : σ → MvPolynomial τ ℂ) (p : MvPolynomial σ ℂ)
    (x : τ → ℂ) : eval x (aeval F p) = eval (fun i => eval x (F i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p i hp => simp [hp]`.
-/
theorem polyEval_aeval_subst {σ : Type*} (F : σ → Polynomial ℂ) (p : MvPolynomial σ ℂ) (z : ℂ) :
    (aeval F p).eval z = eval (fun i => (F i).eval z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/- English proof (translation)
Introduce `hfin`. Establish `hsub : Polynomial.nthRootsFinset (hfin.toFinset.card + 1) (1 : ℂ) ⊆ hfin.toFinset`. Introduce `z hz`. Rewrite `hz` using `[Polynomial.mem_nthRootsFinset (Nat.succ_pos _)]`. Rewrite using `[Set.Finite.mem_toFinset]`.

Conclude with `Complex.norm_eq_one_of_pow_eq_one hz (Nat.succ_ne_zero _)`. Establish `hc` using `Finset.card_le_card hsub`. Rewrite `hc` using `[(Complex.isPrimitiveRoot_exp (hfin.toFinset.card + 1) (Nat.succ_ne_zero _)).card_nthRootsFinset]`. Use linear arithmetic over natural numbers and integers.
-/
theorem unit_circle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  intro hfin
  have hsub : Polynomial.nthRootsFinset (hfin.toFinset.card + 1) (1 : ℂ) ⊆ hfin.toFinset := by
    intro z hz
    rw [Polynomial.mem_nthRootsFinset (Nat.succ_pos _)] at hz
    rw [Set.Finite.mem_toFinset]
    exact Complex.norm_eq_one_of_pow_eq_one hz (Nat.succ_ne_zero _)
  have hc := Finset.card_le_card hsub
  rw [(Complex.isPrimitiveRoot_exp (hfin.toFinset.card + 1) (Nat.succ_ne_zero _)).card_nthRootsFinset]
    at hc
  omega

/- English proof (translation)
Establish `hD : diagonal d ∈ unitaryGroup (Fin n) ℂ`. Rewrite using `[mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hd k]`.

Evaluate the numerical expressions. Conclude with `Submonoid.mul_mem _ (Submonoid.mul_mem _ hV hD) (Unitary.star_mem hV)`.
-/
theorem conj_diagonal_mem {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ unitaryGroup (Fin n) ℂ)
    {d : Fin n → ℂ} (hd : ∀ k, ‖d k‖ = 1) : V * diagonal d * star V ∈ unitaryGroup (Fin n) ℂ := by
  have hD : diagonal d ∈ unitaryGroup (Fin n) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext k
    simp only [Pi.star_apply, RCLike.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hd k]
    norm_num
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hV hD) (Unitary.star_mem hV)

end UnitaryZariskiDense

open UnitaryZariskiDense in

/- English proof (translation)
Introduce `n p hp`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Apply `hp` to reduce the goal to its premises. Establish `herm : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → eval (fun ij : Fin n × Fin n => H ij.1 ij.2) p = 0`.

Introduce `H hH`. Establish `hspec` using `hH.spectral_theorem`. Rewrite `hspec` using `[Unitary.conjStarAlgAut_apply]`. Use `set V : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hVdef`. Establish `hV : V ∈ unitaryGroup (Fin n) ℂ` using `hH.eigenvectorUnitary.2`.

Apply the tactic sequence `have hentry : ∀ d : Fin n → ℂ, eval d (aeval (fun ij : Fin n × Fin n => ∑ k, C (V ij.1 k * star V k ij.2) * X k) p) = eval (fun ij : Fin n × Fin n => (V * diagonal d * star V) ij.1 ij.2) p := by`. Introduce `d`. Rewrite using `[eval_aeval_subst]`. Use `congrArg (fun f => eval f p) (funext fun ij => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`.

Simplify using `only [map_sum, map_mul, eval_C, eval_X, Matrix.mul_diagonal]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Establish `hr : aeval (fun ij : Fin n × Fin n => ∑ k, C (V ij.1 k * star V k ij.2) * X k) p = 0` using `funext_set (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => unit_circle_infinite) fun d hd => by`. Rewrite using `[hentry, map_zero]`. Conclude with `hall _ (conj_diagonal_mem hV fun k => hd k trivial)`.

Apply the tactic sequence `have h0 := hentry (RCLike.ofReal ∘ hH.eigenvalues)`. Rewrite `h0` using `[hr, map_zero]`. Rewrite using `[h0]`. Use `congrArg (fun f => eval f p) (funext fun ij => ?_)` and prove the remaining obligations. Conclude with `congrFun (congrFun hspec ij.1) ij.2`.

Establish `all : ∀ A : Matrix (Fin n) (Fin n) ℂ, eval (fun ij : Fin n × Fin n => A ij.1 ij.2) p = 0`. Introduce `A`. Use `set g : Polynomial ℂ := aeval (fun ij : Fin n × Fin n => Polynomial.C (A ij.1 ij.2) * (Polynomial.C (1 / 2) - Polynomial.C (I / 2) * Polynomial.X) + Polynomial.C (Aᴴ ij.1 ij.2) * (Polynomial.C (1 / 2) + Polynomial.C (I / 2) * Polynomial.X)) p with hgdef`. Establish `hg : ∀ z : ℂ, g.eval z = eval (fun ij : Fin n × Fin n => A ij.1 ij.2 * (1 / 2 - I / 2 * z) + Aᴴ ij.1 ij.2 * (1 / 2 + I / 2 * z)) p`. Introduce `z`.

Rewrite using `[hgdef, polyEval_aeval_subst]`. Use `congrArg (fun f => eval f p) (funext fun ij => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `g0 : g = 0`. Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises.

Apply `(Set.infinite_range_of_injective Complex.ofReal_injective).mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨t, rfl⟩`. Simplify using `only [Set.mem_ofPred_eq, Polynomial.IsRoot, hg]`. Establish `hstar : star (1 / 2 - I / 2 * (t : ℂ)) = 1 / 2 + I / 2 * (t : ℂ)`. Apply the tactic sequence `apply Complex.ext <;> (simp; try ring)`.

Establish `hM : ((1 / 2 - I / 2 * (t : ℂ)) • A + (1 / 2 + I / 2 * (t : ℂ)) • Aᴴ).IsHermitian`. Unfold `IsHermitian`. Rewrite using `[conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_conjTranspose, hstar, ← hstar, star_star, add_comm]`. Establish `h` using `herm _ hM`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h`.

Rewrite using `[← h]`. Use `congrArg (fun f => eval f p) (funext fun ij => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `hg I`. Rewrite `h` using `[g0, Polynomial.eval_zero]`.

Rewrite using `[h]`. Use `congrArg (fun f => eval f p) (funext fun ij => ?_)` and prove the remaining obligations. Establish `h1 : (1 / 2 - I / 2 * I : ℂ) = 1`. Put the polynomial expressions in normal form. Rewrite using `[I_sq]`.

Evaluate the numerical expressions. Establish `h2 : (1 / 2 + I / 2 * I : ℂ) = 0`. Put the polynomial expressions in normal form. Rewrite using `[I_sq]`. Evaluate the numerical expressions.

Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `MvPolynomial.funext fun x => by`. Simplify using `using all (Matrix.of fun i j => x (i, j))`.
-/
theorem UnitaryZariskiDense.proof : UnitaryZariskiDense.Statement := by
  intro n p hp
  by_contra hall
  push Not at hall
  apply hp

  have herm : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian →
      eval (fun ij : Fin n × Fin n => H ij.1 ij.2) p = 0 := by
    intro H hH
    have hspec := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    set V : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hVdef
    have hV : V ∈ unitaryGroup (Fin n) ℂ := hH.eigenvectorUnitary.2
    have hentry : ∀ d : Fin n → ℂ,
        eval d (aeval (fun ij : Fin n × Fin n => ∑ k, C (V ij.1 k * star V k ij.2) * X k) p) =
          eval (fun ij : Fin n × Fin n => (V * diagonal d * star V) ij.1 ij.2) p := by
      intro d
      rw [eval_aeval_subst]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      rw [Matrix.mul_apply]
      simp only [map_sum, map_mul, eval_C, eval_X, Matrix.mul_diagonal]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hr : aeval (fun ij : Fin n × Fin n => ∑ k, C (V ij.1 k * star V k ij.2) * X k) p = 0 :=
      funext_set (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => unit_circle_infinite) fun d hd => by
        rw [hentry, map_zero]
        exact hall _ (conj_diagonal_mem hV fun k => hd k trivial)
    have h0 := hentry (RCLike.ofReal ∘ hH.eigenvalues)
    rw [hr, map_zero] at h0
    rw [h0]
    refine congrArg (fun f => eval f p) (funext fun ij => ?_)
    exact congrFun (congrFun hspec ij.1) ij.2

  have all : ∀ A : Matrix (Fin n) (Fin n) ℂ, eval (fun ij : Fin n × Fin n => A ij.1 ij.2) p = 0 := by
    intro A
    set g : Polynomial ℂ := aeval (fun ij : Fin n × Fin n =>
      Polynomial.C (A ij.1 ij.2) * (Polynomial.C (1 / 2) - Polynomial.C (I / 2) * Polynomial.X) +
        Polynomial.C (Aᴴ ij.1 ij.2) * (Polynomial.C (1 / 2) + Polynomial.C (I / 2) * Polynomial.X)) p
      with hgdef
    have hg : ∀ z : ℂ, g.eval z = eval (fun ij : Fin n × Fin n =>
        A ij.1 ij.2 * (1 / 2 - I / 2 * z) + Aᴴ ij.1 ij.2 * (1 / 2 + I / 2 * z)) p := by
      intro z
      rw [hgdef, polyEval_aeval_subst]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      simp
    have g0 : g = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
      rintro _ ⟨t, rfl⟩
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, hg]
      have hstar : star (1 / 2 - I / 2 * (t : ℂ)) = 1 / 2 + I / 2 * (t : ℂ) := by
        apply Complex.ext <;> (simp; try ring)
      have hM : ((1 / 2 - I / 2 * (t : ℂ)) • A + (1 / 2 + I / 2 * (t : ℂ)) • Aᴴ).IsHermitian := by
        unfold IsHermitian
        rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_conjTranspose,
          hstar, ← hstar, star_star, add_comm]
      have h := herm _ hM
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
      rw [← h]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      ring
    have h := hg I
    rw [g0, Polynomial.eval_zero] at h
    rw [h]
    refine congrArg (fun f => eval f p) (funext fun ij => ?_)
    have h1 : (1 / 2 - I / 2 * I : ℂ) = 1 := by
      ring_nf
      rw [I_sq]
      norm_num
    have h2 : (1 / 2 + I / 2 * I : ℂ) = 0 := by
      ring_nf
      rw [I_sq]
      norm_num
    rw [h1, h2]
    ring

  exact MvPolynomial.funext fun x => by
    simpa using all (Matrix.of fun i j => x (i, j))

end

end GroundTheory.Heights₂.Heights.ComplexSets
