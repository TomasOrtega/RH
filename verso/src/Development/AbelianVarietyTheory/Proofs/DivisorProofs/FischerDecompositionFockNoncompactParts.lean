import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineKroneckerRightMatrixConjTranspose

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.JointHarm

namespace GlobalTheory.FischerParts

/- English proof (translation)
Set `w : (σ →₀ ℕ) → ℕ` to `fun α => α.prod fun _ k => k.factorial`. Establish `hw : ∀ α, w α ≠ 0` using `fun α => Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _`. Set `v : (σ →₀ ℕ) → lp (fun _ : σ →₀ ℕ => ℂ) 2` to `fun α => lp.single 2 α (√(w α) : ℝ)`. Establish `hv : ∀ α β, inner ℂ (v α) (v β) = if α = β then (w α : ℂ) else 0`. Introduce `α β`.

Simplify using `only [v, lp.inner_single_left, lp.single_apply, Pi.single_apply]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `only [RCLike.inner_apply, Complex.conj_ofReal]`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]`.

Simplify using the standard rewrite rules. Use `⟨(basisMonomials σ ℂ).constr ℂ v, fun α β => ?_, ?_⟩` and prove the remaining obligations. Establish `e : ∀ α, (basisMonomials σ ℂ).constr ℂ v (monomial α 1) = v α` using `fun α => by`. Use `(basisMonomials σ ℂ).constr_basis ℂ v α` as an intermediate fact. Rewrite `this` using `[coe_basisMonomials]`. Then use the resulting hypothesis.

Rewrite using `[e, e, hv]`. Simplify using `[w, Finsupp.prod]`. Use `(basisMonomials σ ℂ).injective_constr_of_linearIndependent ?_` and prove the remaining obligations. Use `linearIndependent_of_ne_zero_of_inner_eq_zero (fun α h => hw α ?_) fun α β h => ?_` and prove the remaining obligations. Use `hv α α` as an intermediate fact.

Rewrite `this` using `[h, inner_zero_left, if_pos rfl]`. Conclude with `this.symm` after adjusting the coercions. Conclude with `(hv α β).trans (if_neg h)`.
-/
theorem exists_fockIP (σ : Type) [DecidableEq σ] :
    ∃ ι : MvPolynomial σ ℂ →ₗ[ℂ] lp (fun _ : σ →₀ ℕ => ℂ) 2,
      IsFockIP ι ∧ Function.Injective ι := by
  classical
  let w : (σ →₀ ℕ) → ℕ := fun α => α.prod fun _ k => k.factorial
  have hw : ∀ α, w α ≠ 0 := fun α => Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  let v : (σ →₀ ℕ) → lp (fun _ : σ →₀ ℕ => ℂ) 2 := fun α => lp.single 2 α (√(w α) : ℝ)
  have hv : ∀ α β, inner ℂ (v α) (v β) = if α = β then (w α : ℂ) else 0 := by
    intro α β
    simp only [v, lp.inner_single_left, lp.single_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      simp only [RCLike.inner_apply, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    · simp
  refine ⟨(basisMonomials σ ℂ).constr ℂ v, fun α β => ?_, ?_⟩
  · have e : ∀ α, (basisMonomials σ ℂ).constr ℂ v (monomial α 1) = v α := fun α => by
      have := (basisMonomials σ ℂ).constr_basis ℂ v α
      rwa [coe_basisMonomials] at this
    rw [e, e, hv]
    simp [w, Finsupp.prod]
  · refine (basisMonomials σ ℂ).injective_constr_of_linearIndependent ?_
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun α h => hw α ?_) fun α β h => ?_
    · have := hv α α
      rw [h, inner_zero_left, if_pos rfl] at this
      exact_mod_cast this.symm
    · exact (hv α β).trans (if_neg h)

/- English proof (translation)
Introduce `p q r s d`. Take `⟨ι, hι, hinj⟩` from `exists_fockIP (Ln p q r s)`. Use `⟨fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron1 r s Z} ?_ ?_ d _ _ (fun P hP => ?_) fun P => ?_, fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron2 p q Z} ?_ ?_ d _ _ (fun P hP => ?_) fun P => ?_, fischer hι hinj {M | (∃ Z, IsPC Z ∧ M = kron1 r s Z) ∨ ∃ Z, IsPC Z ∧ M = kron2 p q Z} ?_ ?_ …` and prove the remaining obligations. Introduce and unpack `_ ⟨Z, hZ, rfl⟩`. Conclude with `odd_kron1 hZ`.

Introduce and unpack `_ ⟨Z, hZ, rfl⟩`. Conclude with `⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩`. Conclude with `fun Z hZ => hP _ ⟨Z, hZ, rfl⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Q, hQ, Z, hZ, rfl⟩`.

Conclude with `⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩`. Introduce and unpack `⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩`. Conclude with `⟨Q, hQ, Z, hZ, rfl⟩`. Introduce and unpack `_ ⟨Z, hZ, rfl⟩`. Conclude with `odd_kron2 hZ`.

Introduce and unpack `_ ⟨Z, hZ, rfl⟩`. Conclude with `⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩`. Conclude with `fun Z hZ => hP _ ⟨Z, hZ, rfl⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Q, hQ, Z, hZ, rfl⟩`.

Conclude with `⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩`. Introduce and unpack `⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩`. Conclude with `⟨Q, hQ, Z, hZ, rfl⟩`. Introduce and unpack `_ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩) exacts [odd_kron1 hZ, odd_kron2 hZ]`. Introduce and unpack `_ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩) exacts [⟨_, .inl ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩, ⟨_, .inr ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩]`.

Conclude with `⟨fun Z hZ => hP _ (.inl ⟨Z, hZ, rfl⟩), fun Z hZ => hP _ (.inr ⟨Z, hZ, rfl⟩)⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Q, hQ, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩⟩ exacts [⟨Q, hQ, _, .inl ⟨Z, hZ, rfl⟩, rfl⟩, ⟨Q, hQ, _, .inr ⟨Z, hZ, rfl⟩, rfl⟩]`. Introduce and unpack `⟨Q, hQ, _, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩, rfl⟩ exacts [⟨Q, hQ, .inl ⟨Z, hZ, rfl⟩⟩, ⟨Q, hQ, .inr ⟨Z, hZ, rfl⟩⟩]`.
-/
theorem fischer_parts : ∀ (p q r s d : ℕ), (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm2 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm1 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (jointHarm p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨ ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) := by
  intro p q r s d
  obtain ⟨ι, hι, hinj⟩ := exists_fockIP (Ln p q r s)
  refine ⟨fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron1 r s Z} ?_ ?_ d _ _ (fun P hP => ?_)
      fun P => ?_,
    fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron2 p q Z} ?_ ?_ d _ _ (fun P hP => ?_)
      fun P => ?_,
    fischer hι hinj {M | (∃ Z, IsPC Z ∧ M = kron1 r s Z) ∨ ∃ Z, IsPC Z ∧ M = kron2 p q Z}
      ?_ ?_ d _ _ (fun P hP => ?_) fun P => ?_⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact odd_kron1 hZ
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩
  · exact fun Z hZ => hP _ ⟨Z, hZ, rfl⟩
  · constructor
    · rintro ⟨Q, hQ, Z, hZ, rfl⟩
      exact ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, Z, hZ, rfl⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact odd_kron2 hZ
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩
  · exact fun Z hZ => hP _ ⟨Z, hZ, rfl⟩
  · constructor
    · rintro ⟨Q, hQ, Z, hZ, rfl⟩
      exact ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, Z, hZ, rfl⟩
  · rintro _ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩)
    exacts [odd_kron1 hZ, odd_kron2 hZ]
  · rintro _ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩)
    exacts [⟨_, .inl ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩,
      ⟨_, .inr ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩]
  · exact ⟨fun Z hZ => hP _ (.inl ⟨Z, hZ, rfl⟩), fun Z hZ => hP _ (.inr ⟨Z, hZ, rfl⟩)⟩
  · constructor
    · rintro ⟨Q, hQ, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩⟩
      exacts [⟨Q, hQ, _, .inl ⟨Z, hZ, rfl⟩, rfl⟩, ⟨Q, hQ, _, .inr ⟨Z, hZ, rfl⟩, rfl⟩]
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩, rfl⟩
      exacts [⟨Q, hQ, .inl ⟨Z, hZ, rfl⟩⟩, ⟨Q, hQ, .inr ⟨Z, hZ, rfl⟩⟩]

end GlobalTheory.FischerParts
