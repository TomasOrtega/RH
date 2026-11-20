import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.ActSFirstBlock

open GlobalTheory.DefLift.BilFischer

/- English proof (translation)
Proceed by induction on `A using MvPolynomial.induction_on' with`. Consider the case `add A A' h h' => simp only [map_add, LinearMap.add_apply, h, h']`. Consider the case `monomial α c`. Proceed by induction on `B using MvPolynomial.induction_on' with`. Consider the case `add B B' h h' => simp only [map_add, LinearMap.add_apply, h, h']`.

Consider the case `monomial β d`. Rewrite using `[pair_monomial, pair_monomial, coeff_monomial, coeff_monomial]`. Distinguish the cases in `e : α = β`. Substitute `e` using the available equality. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[e, Ne.symm e]`.
-/
theorem pair_comm {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) : pair A B = pair B A := by
  classical
  induction A using MvPolynomial.induction_on' with
  | add A A' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | monomial α c =>
    induction B using MvPolynomial.induction_on' with
    | add B B' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | monomial β d =>
      rw [pair_monomial, pair_monomial, coeff_monomial, coeff_monomial]
      by_cases e : α = β
      · subst e; simp; ring
      · simp [e, Ne.symm e]

/- English proof (translation)
Rewrite using `[pair_comm, ← pair_mul_X, pair_comm, mul_comm]`.
-/
theorem pair_pderiv {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) (v : σ) :
    pair (pderiv v A) B = pair A (X v * B) := by
  rw [pair_comm, ← pair_mul_X, pair_comm, mul_comm]

/- English proof (translation)
Rewrite using `[mul_comm, pair_mul_X]`.
-/
theorem pair_X_mul {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) (v : σ) :
    pair (X v * A) B = pair A (pderiv v B) := by
  rw [mul_comm, pair_mul_X]

/- English proof (translation)
Establish `: omE u v F = -(pderiv u (X v * F)) + (if u = v then (1 / 2 : ℂ) else 0) • F`. Simplify using `only [omE, raiB, lowB, hu, hv, Bool.false_eq_true, if_false]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[this, Derivation.leibniz, pderiv_X, Pi.single_apply]`. Distinguish the cases in `e : u = v`.

Substitute `e` using the available equality. Simplify using `only [if_true, smul_eq_mul, mul_one]`. Use `module`. Simplify using `[e, Ne.symm e]`.
-/
theorem omE_neg {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = false) (hv : linePos v = false)
    (F : Pol p q r s) :
    omE u v F = -(X v * pderiv u F) - (if u = v then (1 / 2 : ℂ) else 0) • F := by
  have : omE u v F = -(pderiv u (X v * F)) + (if u = v then (1 / 2 : ℂ) else 0) • F := by
    simp only [omE, raiB, lowB, hu, hv, Bool.false_eq_true, if_false]
    split_ifs <;> simp
  rw [this, Derivation.leibniz, pderiv_X, Pi.single_apply]
  by_cases e : u = v
  · subst e
    simp only [if_true, smul_eq_mul, mul_one]
    module
  · simp [e, Ne.symm e]

/- English proof (translation)
Proceed by induction on `G using MvPolynomial.induction_on with`. Consider the case `C c => simp`. Consider the case `add A B h h' => simp only [map_add, h, h', add_mul, Finset.sum_add_distrib]`. Consider the case `mul_X A u h`. Simplify using `only [map_mul, aeval_X, Derivation.leibniz, h, smul_eq_mul, map_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]`.

Use `congr 1`. Rewrite using `[Finset.sum_eq_single u]`. Simplify using the standard rewrite rules. Introduce `w _ hw`. Simplify using `[pderiv_X, Pi.single_apply, hw, Ne.symm hw]`.

Simplify using the standard rewrite rules.
-/
theorem pderiv_aeval {σ τ : Type} [Fintype σ] (m : σ → MvPolynomial τ ℂ) (v : τ) (G : MvPolynomial σ ℂ) :
    pderiv v (aeval m G) = ∑ i, aeval m (pderiv i G) * pderiv v (m i) := by
  classical
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add A B h h' => simp only [map_add, h, h', add_mul, Finset.sum_add_distrib]
  | mul_X A u h =>
    simp only [map_mul, aeval_X, Derivation.leibniz, h, smul_eq_mul, map_add, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    congr 1
    rw [Finset.sum_eq_single u]
    · simp
    · intro w _ hw
      simp [pderiv_X, Pi.single_apply, hw, Ne.symm hw]
    · simp

/- English proof (translation)
Set `g : Fin Q × Fin Q → Ix P Q × Ix 0 S` to `fun bc => (Sum.inr bc.1, Sum.inr (Fin.castLE h bc.2))`. Establish `: detS P Q S h = aeval (fun i => X (g i)) (Matrix.det (Matrix.mvPolynomialX (Fin Q) (Fin Q) ℂ))`. Rewrite using `[detS, ← AlgHom.coe_toRingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `b c`.

Simplify using `[g, Matrix.mvPolynomialX]`. Rewrite using `[this, pderiv_aeval]`. Simplify using `[g, pderiv_X, Pi.single_apply]`.
-/
theorem pderiv_detS (P Q S : ℕ) (h : Q ≤ S) (a : Fin P) (c : Ix 0 S) :
    pderiv (Sum.inl a, c) (detS P Q S h) = 0 := by
  classical
  let g : Fin Q × Fin Q → Ix P Q × Ix 0 S := fun bc => (Sum.inr bc.1, Sum.inr (Fin.castLE h bc.2))
  have : detS P Q S h = aeval (fun i => X (g i)) (Matrix.det (Matrix.mvPolynomialX (Fin Q) (Fin Q) ℂ)) := by
    rw [detS, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext b c; simp [g, Matrix.mvPolynomialX]
  rw [this, pderiv_aeval]
  simp [g, pderiv_X, Pi.single_apply]

/- English proof (translation)
Simplify using `only [mS, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq]`. Use `split_ifs with e`. Simplify using `[e]`. Simplify using `[e]`.
-/
theorem pderiv_mS (P Q S : ℕ) (a a' : Fin P) (c : Fin S) (b : Fin Q) :
    pderiv (Sum.inl a', Sum.inr c) (mS P Q S a b) =
      if a = a' then X (Sum.inr b, Sum.inr c) else 0 := by
  classical
  simp only [mS, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul, Prod.mk.injEq,
    Sum.inl.injEq, Sum.inr.injEq]
  split_ifs with e
  · simp [e]
  · simp [e]

/- English proof (translation)
Simplify using `only [embS, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, Derivation.leibniz, Derivation.leibniz_pow, pderiv_detS, smul_zero, zero_add, smul_eq_mul, pderiv_aeval, pderiv_mS, map_sum, map_mul, aeval_X, Fintype.sum_prod_type, mul_zero, mul_ite, Finset.su …`. Simplify using `only [Finset.sum_comm (s := (Finset.univ : Finset (Fin P))), Finset.sum_ite_eq', Finset.mem_univ, if_true, mS, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem euler_embS (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a a' : Fin P) (G : Mdl P Q) :
    ∑ c : Fin S, X (Sum.inl a, Sum.inr c) * pderiv (Sum.inl a', Sum.inr c) (embS P Q S h k' G) =
      embS P Q S h k' (∑ b, X (a, b) * pderiv (a', b) G) := by
  classical
  simp only [embS, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
    Derivation.leibniz, Derivation.leibniz_pow, pderiv_detS, smul_zero, zero_add, smul_eq_mul,
    pderiv_aeval, pderiv_mS, map_sum, map_mul, aeval_X, Fintype.sum_prod_type, mul_zero, mul_ite,
    Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin P))), Finset.sum_ite_eq', Finset.mem_univ, if_true, mS, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

/- English proof (translation)
Introduce `P Q S h k' a a' G f`. Rewrite using `[fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]`. Simplify using `only [omE_neg (Sum.inl _, Sum.inr _) (Sum.inl _, Sum.inr _) rfl rfl, Finset.univ_eq_empty, Finset.sum_empty, zero_add, map_sum, map_sub, map_neg, map_smul, LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, pair_X_mul, pair_pderiv, opS, Module.En …`. Establish `key` using `congrArg (pair f) (euler_embS P Q S h k' a a' G)`. Simplify using `only [map_sum] at key`.

Rewrite using `[Finset.sum_sub_distrib, Finset.sum_neg_distrib, key]`. Distinguish the cases in `e : a = a'`. Simplify using `[e]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[e]`.
-/
theorem pair_act_first_block : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a a' : Fin P) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inl a) (Sum.inl a')) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inl a') G)) := by
  intro P Q S h k' a a' G f
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [omE_neg (Sum.inl _, Sum.inr _) (Sum.inl _, Sum.inr _) rfl rfl, Finset.univ_eq_empty,
    Finset.sum_empty, zero_add, map_sum, map_sub, map_neg, map_smul, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, pair_X_mul, pair_pderiv,
    opS, Module.End.mul_apply, LinearMap.mulLeft_apply, Module.End.one_apply]
  have key := congrArg (pair f) (euler_embS P Q S h k' a a' G)
  simp only [map_sum] at key
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, key]
  by_cases e : a = a'
  · simp [e]
    ring
  · simp [e]

end GlobalTheory.CharPair.ActSFirstBlock

end
