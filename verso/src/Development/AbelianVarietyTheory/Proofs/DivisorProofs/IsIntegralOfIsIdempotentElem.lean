import Mathlib

open TensorProduct

namespace GlobalTheory.IdempotentTensorOne

/- English proof (translation)
Use `⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num)), ?_⟩` and prove the remaining obligations. Simplify using `[sq, he.eq]`.
-/
theorem isIntegral_of_isIdempotentElem {S B : Type} [CommRing S] [CommRing B] [Algebra S B]
    {e : B} (he : IsIdempotentElem e) : IsIntegral S e := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num)), ?_⟩
  simp [sq, he.eq]

/- English proof (translation)
Establish `: Algebra.Smooth R A` using `hA`. Establish `hint : ε ∈ integralClosure A (A ⊗[R] FractionRing R)` using `isIntegral_of_isIdempotentElem hε`. Take `⟨t, ht⟩` from `(TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := A) (B := FractionRing R)).2 ⟨ε, hint⟩`. Establish `hε' : Algebra.TensorProduct.map (AlgHom.id A A) (integralClosure R (FractionRing R)).val t = ε` using `congrArg Subtype.val ht`. Establish `hdesc : ∀ u : A ⊗[R] integralClosure R (FractionRing R), ∃ a : A, a ⊗ₜ[R] (1 : FractionRing R) = Algebra.TensorProduct.map (AlgHom.id A A) (integralClosure R (FractionRing R)).val u`.

Introduce `u`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul x y`. Take `⟨r, hr⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := R) (K := FractionRing R)).1 ((mem_integralClosure_iff _ _).1 y.2)`.

Use `⟨r • x, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]`. Both sides reduce to the same expression. Consider the case `add u w hu hw`. Take `⟨a, ha⟩` from `hu`.

Take `⟨b, hb⟩` from `hw`. Conclude with `⟨a + b, by rw [TensorProduct.add_tmul, ha, hb, map_add]⟩`. Take `⟨a, ha⟩` from `hdesc t`. Rewrite `ha` using `[hε']`. Use `⟨a, ?_, ha⟩` and prove the remaining obligations.

Establish `hinj : Function.Injective (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] FractionRing R)` using `Algebra.TensorProduct.includeLeft_injective (IsFractionRing.injective R (FractionRing R))`. Apply `hinj` to reduce the goal to its premises. Use `show (a * a) ⊗ₜ[R] (1 : FractionRing R) = a ⊗ₜ[R] (1 : FractionRing R)`. Rewrite using `[← mul_one (1 : FractionRing R), ← Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha, hε.eq]`.
-/
theorem exists_idempotent_tmul_one_eq (R A : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing A] [Algebra R A] (hA : Algebra.Smooth R A)
    (ε : A ⊗[R] FractionRing R) (hε : IsIdempotentElem ε) :
    ∃ a : A, IsIdempotentElem a ∧ a ⊗ₜ[R] (1 : FractionRing R) = ε := by
  have : Algebra.Smooth R A := hA

  have hint : ε ∈ integralClosure A (A ⊗[R] FractionRing R) := isIntegral_of_isIdempotentElem hε
  obtain ⟨t, ht⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := A) (B := FractionRing R)).2 ⟨ε, hint⟩
  have hε' : Algebra.TensorProduct.map (AlgHom.id A A) (integralClosure R (FractionRing R)).val t = ε :=
    congrArg Subtype.val ht
  have hdesc : ∀ u : A ⊗[R] integralClosure R (FractionRing R), ∃ a : A,
      a ⊗ₜ[R] (1 : FractionRing R) =
        Algebra.TensorProduct.map (AlgHom.id A A) (integralClosure R (FractionRing R)).val u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x y =>
      obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := FractionRing R)).1
        ((mem_integralClosure_iff _ _).1 y.2)
      refine ⟨r • x, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
      rfl
    | add u w hu hw =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hw
      exact ⟨a + b, by rw [TensorProduct.add_tmul, ha, hb, map_add]⟩
  obtain ⟨a, ha⟩ := hdesc t
  rw [hε'] at ha
  refine ⟨a, ?_, ha⟩

  have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] FractionRing R) :=
    Algebra.TensorProduct.includeLeft_injective (IsFractionRing.injective R (FractionRing R))
  apply hinj
  show (a * a) ⊗ₜ[R] (1 : FractionRing R) = a ⊗ₜ[R] (1 : FractionRing R)
  rw [← mul_one (1 : FractionRing R), ← Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha, hε.eq]

end GlobalTheory.IdempotentTensorOne
