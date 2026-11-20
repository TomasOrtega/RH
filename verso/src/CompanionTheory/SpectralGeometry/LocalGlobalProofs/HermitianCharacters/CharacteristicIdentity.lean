import Mathlib
import Formalism.FlagUnipotentLattices.QDetNegTranspose
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Finset TensorProduct Formalism.HermitianLatticeCounting.S8

noncomputable section

namespace GlobalTheory.CompanionTheory.Inh.CharId

open Polynomial Formalism.REAL

def IsPolyFun {B : Type*} [Ring B] [Algebra ℂ B] (f : ℂ → B) : Prop :=
  ∃ P : B[X], ∀ u, f u = P.eval (algebraMap ℂ B u)

section
variable {B : Type*} [Ring B] [Algebra ℂ B]

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem eval_mul_scalar (P Q : B[X]) (u : ℂ) :
    (P * Q).eval (algebraMap ℂ B u) = P.eval (algebraMap ℂ B u) * Q.eval (algebraMap ℂ B u) := by
  have := Polynomial.eval₂_mul_noncomm (p := P) (q := Q) (RingHom.id B) (algebraMap ℂ B u)
    (fun k => (Algebra.commutes u _).symm)
  exact this

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem IsPolyFun.const (b : B) : IsPolyFun (fun _ => b) := ⟨C b, fun u => by simp⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem IsPolyFun.scalar : IsPolyFun (fun u => algebraMap ℂ B u) := ⟨X, fun u => by simp⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem IsPolyFun.add {f g : ℂ → B} (hf : IsPolyFun f) (hg : IsPolyFun g) : IsPolyFun (fun u => f u + g u) := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P + Q, fun u => by simp [hP, hQ]⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem IsPolyFun.mul {f g : ℂ → B} (hf : IsPolyFun f) (hg : IsPolyFun g) : IsPolyFun (fun u => f u * g u) := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P * Q, fun u => by simp only [hP, hQ, eval_mul_scalar]⟩

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem IsPolyFun.sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → B) (h : ∀ i, IsPolyFun (f i)) :
    IsPolyFun (fun u => ∑ i ∈ s, f i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPolyFun.const (0 : B)
  | insert a s ha ih => simpa [Finset.sum_insert ha] using (h a).add ih

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IsPolyFun.prod_ofFn : ∀ (t : ℕ) (f : Fin t → ℂ → B), (∀ i, IsPolyFun (f i)) →
    IsPolyFun (fun u => (List.ofFn fun k => f k u).prod)
  | 0, f, _ => by simpa using IsPolyFun.const (1 : B)
  | t + 1, f, h => by
    simpa [List.ofFn_succ] using (h 0).mul (IsPolyFun.prod_ofFn t (fun k => f k.succ) fun k => h _)

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IsPolyFun.map {B' : Type*} [Ring B'] [Algebra ℂ B'] (g : B →ₐ[ℂ] B') {f : ℂ → B}
    (hf : IsPolyFun f) : IsPolyFun (fun u => g (f u)) := by
  obtain ⟨P, hP⟩ := hf
  refine ⟨P.map (g : B →+* B'), fun u => ?_⟩
  show g (f u) = _
  rw [hP, ← g.commutes u]
  exact (Polynomial.eval_map_apply (g : B →+* B') _).symm

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem isPoly_Tm {n : ℕ} (E : Fin n → Fin n → B) (c : ℂ) (a b : Fin n) :
    IsPolyFun (fun u => Tm E (u - c) a b) := by
  unfold Tm
  by_cases h : a = b
  · simp only [h, if_true, sub_eq_add_neg, map_add]
    exact (IsPolyFun.scalar.add (IsPolyFun.const _)).add (IsPolyFun.const _)
  · simp only [h, if_false]
    exact IsPolyFun.const _

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isPoly_qminor {n t : ℕ} (E : Fin n → Fin n → B) (a b : Fin t → Fin n) (c : ℂ) :
    IsPolyFun (fun u => qminor E a b (u + c)) := by
  unfold qminor
  refine IsPolyFun.sum _ _ fun σ => (IsPolyFun.const _).mul
    (IsPolyFun.prod_ofFn t (fun k u => Tm E (u + c - (k : ℂ)) (a (σ k)) (b k)) fun k => ?_)
  have := isPoly_Tm E ((k : ℂ) - c) (a (σ k)) (b k)
  convert this using 3
  ring

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.
-/
theorem eq_zero_of_eval (P : B[X]) (h : ∀ u : ℂ, P.eval (algebraMap ℂ B u) = 0) : P = 0 := by
  ext k
  rw [coeff_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  let q : ℂ[X] := ∑ i ∈ P.support, monomial i (ℓ (P.coeff i))
  have hq : q = 0 := by
    apply Polynomial.funext
    intro u
    have := congrArg ℓ (h u)
    rw [eval_eq_sum, Polynomial.sum, map_sum, map_zero] at this
    rw [eval_zero, ← this, eval_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, eval_monomial, smul_eq_mul,
      mul_comm]
  have hk := congrArg (fun r => r.coeff k) hq
  simp only [q, finset_sum_coeff, coeff_monomial, coeff_zero, Finset.sum_ite_eq'] at hk
  by_cases hs : k ∈ P.support
  · simpa [hs] using hk
  · simp [notMem_support_iff.mp hs]

end

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

def op (M : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (V ⊗[ℂ] (Fin n → ℂ)) :=
  ∑ a, ∑ b, TensorProduct.map (M a b) (stdRep n a b)

end

end GlobalTheory.CompanionTheory.Inh.CharId

namespace GlobalTheory.CompanionTheory.Inh
open CharId

end GlobalTheory.CompanionTheory.Inh
