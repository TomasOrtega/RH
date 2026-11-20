import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

open GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hk : k = 1`. Break down `Nat.lt_trichotomy k 1 with hlt | heq | hgt` into its components or cases. Take `⟨a, b, hab⟩` from `h.exists_pair_ne`.

Establish `hk0 : k = 0` using `by omega`. Substitute `hk0` using the available equality. Conclude with `absurd (funext fun i => i.elim0) hab`. Conclude with `heq`. Set `i₀ : Fin k` to `⟨0, by omega⟩`.

Set `i₁ : Fin k` to `⟨1, hgt⟩`. Establish `hne : i₁ ≠ i₀`. Introduce `hij`. Use `congrArg Fin.val hij` as an intermediate fact. Simplify using `[i₀, i₁] at this`.

Establish `hx : (Pi.single i₀ (1 : A i₀) : ∀ i, A i) ≠ 0`. Introduce `hx`. Use `congrFun hx i₀` as an intermediate fact. Simplify using `at this`. Take `⟨y, hy⟩` from `h.mul_inv_cancel hx`.

Use `congrFun hy i₁` as an intermediate fact. Rewrite `this` using `[Pi.mul_apply, Pi.single_eq_of_ne hne, zero_mul, Pi.one_apply]`. Conclude with `absurd this zero_ne_one`. Use `⟨hk, ?_⟩` and prove the remaining obligations. Substitute `hk` using the available equality.

Introduce `i`. Establish `hdef : IsField (A default)` using `(RingEquiv.piUnique A).symm.toMulEquiv.isField h`. Conclude with `(Unique.eq_default i).symm ▸ hdef`. Introduce and unpack `⟨rfl, h⟩`. Conclude with `(RingEquiv.piUnique A).toMulEquiv.isField (h default)`.
-/
theorem isField_pi_fin_iff {k : ℕ} (A : Fin k → Type) [∀ i, CommRing (A i)]
    [∀ i, Nontrivial (A i)] : IsField (∀ i, A i) ↔ k = 1 ∧ ∀ i, IsField (A i) := by
  constructor
  · intro h

    have hk : k = 1 := by
      rcases Nat.lt_trichotomy k 1 with hlt | heq | hgt
      · obtain ⟨a, b, hab⟩ := h.exists_pair_ne
        have hk0 : k = 0 := by omega
        subst hk0
        exact absurd (funext fun i => i.elim0) hab
      · exact heq
      · let i₀ : Fin k := ⟨0, by omega⟩
        let i₁ : Fin k := ⟨1, hgt⟩
        have hne : i₁ ≠ i₀ := by
          intro hij
          have := congrArg Fin.val hij
          simp [i₀, i₁] at this
        have hx : (Pi.single i₀ (1 : A i₀) : ∀ i, A i) ≠ 0 := by
          intro hx
          have := congrFun hx i₀
          simp at this
        obtain ⟨y, hy⟩ := h.mul_inv_cancel hx
        have := congrFun hy i₁
        rw [Pi.mul_apply, Pi.single_eq_of_ne hne, zero_mul, Pi.one_apply] at this
        exact absurd this zero_ne_one
    refine ⟨hk, ?_⟩
    subst hk
    intro i
    have hdef : IsField (A default) := (RingEquiv.piUnique A).symm.toMulEquiv.isField h
    exact (Unique.eq_default i).symm ▸ hdef
  · rintro ⟨rfl, h⟩
    exact (RingEquiv.piUnique A).toMulEquiv.isField (h default)

/- English proof (translation)
Introduce `F E _ _ _ _ P _ _ k K _ _ ⟨e⟩`. Set `φ : P ⊗[F] E ≃ₐ[F] ∀ i, K i ⊗[F] E` to `(Algebra.TensorProduct.congr e AlgEquiv.refl).trans ((Algebra.TensorProduct.comm F _ E).trans ((Algebra.TensorProduct.piRight F F E K).trans (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F E (K i))))`. Establish `: ∀ i, Nontrivial (K i ⊗[F] E)` using `fun i => TensorProduct.nontrivial_of_linearMap_injective_of_flat_right (R := F) (M := K i) (N := E) (Algebra.linearMap F (K i)) (algebraMap F (K i)).injective`. Rewrite using `[φ.toRingEquiv.toMulEquiv.isField_congr]`. Conclude with `isField_pi_fin_iff _`.
-/
theorem tensorFieldIff : TensorFieldIff := by
  intro F E _ _ _ _ P _ _ k K _ _ ⟨e⟩

  let φ : P ⊗[F] E ≃ₐ[F] ∀ i, K i ⊗[F] E :=
    (Algebra.TensorProduct.congr e AlgEquiv.refl).trans
      ((Algebra.TensorProduct.comm F _ E).trans
        ((Algebra.TensorProduct.piRight F F E K).trans
          (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F E (K i))))

  have : ∀ i, Nontrivial (K i ⊗[F] E) := fun i =>
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_right (R := F) (M := K i) (N := E)
      (Algebra.linearMap F (K i)) (algebraMap F (K i)).injective
  rw [φ.toRingEquiv.toMulEquiv.isField_congr]
  exact isField_pi_fin_iff _

end GlobalTheory.RegSS
