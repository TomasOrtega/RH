import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroForallPointExtendSubalgebra
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

/- English proof (translation)
Introduce `k L _ _ _ _ n x s`. Set `f : MvPolynomial (Fin n) k →ₐ[k] L` to `MvPolynomial.aeval x`. Set `J : Ideal (MvPolynomial (Fin n) k)` to `RingHom.ker f`. Use `haveI : J.IsPrime := RingHom.ker_isPrime _`. Set `ξ : (MvPolynomial (Fin n) k ⧸ J) →ₐ[k] L` to `Ideal.kerLiftAlg f`.

Establish `hξinj : Function.Injective ξ` using `Ideal.kerLiftAlg_injective f`. Establish `hξmk : ∀ p, ξ (Ideal.Quotient.mk J p) = MvPolynomial.aeval x p` using `fun p => rfl`. Use `haveI : Algebra.FiniteType k (MvPolynomial (Fin n) k ⧸ J) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J) (Ideal.Quotient.mkₐ_surjective k J)`. Take `⟨a, S, hξ, ha, hs, H⟩` from `GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra k (MvPolynomial (Fin n) k ⧸ J) L ξ hξinj s`. Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective a`.

Use `⟨g, fun h0 => ha (Ideal.Quotient.eq_zero_iff_mem.2 h0), fun c hc hg => ?_⟩` and prove the remaining obligations. Set `e : MvPolynomial (Fin n) k →ₐ[k] k` to `MvPolynomial.aeval c`. Establish `he : ∀ p, e p = MvPolynomial.eval c p` using `fun p => by`. Simplify using `[e, MvPolynomial.coe_aeval_eq_eval]`. Set `φ : (MvPolynomial (Fin n) k ⧸ J) →ₐ[k] k` to `Ideal.Quotient.liftₐ J e (fun p hp => by`.

Rewrite using `[he]`. Conclude with `hc p hp)`. Establish `hφmk : ∀ p, φ (Ideal.Quotient.mk J p) = e p` using `fun p => rfl`. Take `⟨ψ, hψ⟩` from `H φ (by rw [hφmk, he]; exact hg)`. Establish `hxS : ∀ i, x i ∈ S` using `fun i => by`.

Use `hξ (Ideal.Quotient.mk J (MvPolynomial.X i))` as an intermediate fact. Rewrite `this` using `[hξmk, MvPolynomial.aeval_X]`. Then use the resulting hypothesis. Use `⟨S, hxS, ψ, fun t ht => hs t ht, fun i => ?_⟩` and prove the remaining obligations. Establish `h1 : (⟨x i, hxS i⟩ : S) = ⟨ξ (Ideal.Quotient.mk J (MvPolynomial.X i)), hξ _⟩` using `Subtype.ext (((hξmk _).trans (MvPolynomial.aeval_X x i)).symm)`. Rewrite using `[h1, hψ, hφmk, he, MvPolynomial.eval_X]`.
-/
theorem UpperTheory.exists_specialization_of_eval_ne_zero :
    ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] (n : ℕ) (x : Fin n → L) (s : Finset L), ∃ g : MvPolynomial (Fin n) k, MvPolynomial.aeval x g ≠ 0 ∧ ∀ c : Fin n → k, (∀ p : MvPolynomial (Fin n) k, MvPolynomial.aeval x p = 0 → MvPolynomial.eval c p = 0) → MvPolynomial.eval c g ≠ 0 → ∃ (R : Subalgebra k L) (hx : ∀ i, x i ∈ R) (φ : R →ₐ[k] k), (s : Set L) ⊆ R ∧ ∀ i, φ ⟨x i, hx i⟩ = c i := by
  intro k L _ _ _ _ n x s
  let f : MvPolynomial (Fin n) k →ₐ[k] L := MvPolynomial.aeval x
  let J : Ideal (MvPolynomial (Fin n) k) := RingHom.ker f
  haveI : J.IsPrime := RingHom.ker_isPrime _
  let ξ : (MvPolynomial (Fin n) k ⧸ J) →ₐ[k] L := Ideal.kerLiftAlg f
  have hξinj : Function.Injective ξ := Ideal.kerLiftAlg_injective f
  have hξmk : ∀ p, ξ (Ideal.Quotient.mk J p) = MvPolynomial.aeval x p := fun p => rfl
  haveI : Algebra.FiniteType k (MvPolynomial (Fin n) k ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J) (Ideal.Quotient.mkₐ_surjective k J)
  obtain ⟨a, S, hξ, ha, hs, H⟩ := GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra k
    (MvPolynomial (Fin n) k ⧸ J) L ξ hξinj s
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨g, fun h0 => ha (Ideal.Quotient.eq_zero_iff_mem.2 h0), fun c hc hg => ?_⟩
  let e : MvPolynomial (Fin n) k →ₐ[k] k := MvPolynomial.aeval c
  have he : ∀ p, e p = MvPolynomial.eval c p := fun p => by
    simp [e, MvPolynomial.coe_aeval_eq_eval]
  let φ : (MvPolynomial (Fin n) k ⧸ J) →ₐ[k] k :=
    Ideal.Quotient.liftₐ J e (fun p hp => by
      rw [he]
      exact hc p hp)
  have hφmk : ∀ p, φ (Ideal.Quotient.mk J p) = e p := fun p => rfl
  obtain ⟨ψ, hψ⟩ := H φ (by rw [hφmk, he]; exact hg)
  have hxS : ∀ i, x i ∈ S := fun i => by
    have := hξ (Ideal.Quotient.mk J (MvPolynomial.X i))
    rwa [hξmk, MvPolynomial.aeval_X] at this
  refine ⟨S, hxS, ψ, fun t ht => hs t ht, fun i => ?_⟩
  have h1 : (⟨x i, hxS i⟩ : S) = ⟨ξ (Ideal.Quotient.mk J (MvPolynomial.X i)), hξ _⟩ :=
    Subtype.ext (((hξmk _).trans (MvPolynomial.aeval_X x i)).symm)
  rw [h1, hψ, hφmk, he, MvPolynomial.eval_X]
