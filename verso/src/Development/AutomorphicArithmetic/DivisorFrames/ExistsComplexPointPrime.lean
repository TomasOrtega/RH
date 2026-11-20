import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRadicalOfHolomorphicRatioTendsto
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg

open Formalism.L2.Pj in
/- English proof (translation)
Introduce `F A _ _ _ _ σ m ε hε P hP c j₀ hc`. Use `haveI : CharZero F := σ.charZero`. Take `⟨n, f, hf⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType F A)`. Set `g : MvPolynomial (Fin n) F →ₐ[F] A ⧸ P` to `(Ideal.Quotient.mkₐ F P).comp f`. Establish `hg : Function.Surjective g` using `(Ideal.Quotient.mkₐ_surjective F P).comp hf`.

Set `p : TRing F` to `⟨n, RingHom.ker g, (RingHom.ker_isPrime g).isRadical⟩`. Set `e : p.R ≃ₐ[F] A ⧸ P` to `Ideal.quotientKerAlgEquivOfSurjective hg`. Set `q : A →ₐ[F] p.R` to `(e.symm : A ⧸ P →ₐ[F] p.R).comp (Ideal.Quotient.mkₐ F P)`. Establish `hq : ∀ x, q x = 0 ↔ x ∈ P` using `fun x => by show e.symm (Ideal.Quotient.mk P x) = 0 ↔ _`. Rewrite using `[map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]`.

Establish `hli : LinearIndependent F (fun j => toCAt σ (ε j))` using `Fintype.linearIndependent_iff.2 fun a ha j => congrFun (hε a ha) j`. Choose the witnesses or unpack the hypotheses as in `⟨θ, hθ⟩ : ∃ θ : Module.Dual F (CAt σ), ∀ j, θ (toCAt σ (ε j)) = if j = j₀ then 1 else 0 := by`. Take `⟨θ, hθ⟩` from `LinearMap.exists_extend ((Finsupp.lapply j₀ : (Fin m →₀ F) →ₗ[F] F).comp hli.repr)`. Use `⟨θ, fun j => ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun hθ ⟨toCAt σ (ε j), Submodule.subset_span ⟨j, rfl⟩⟩`.

Rewrite `h1` using `[LinearMap.comp_apply, LinearMap.comp_apply, hli.repr_eq_single j _ rfl]`. Simplify `h1` using `[Finsupp.single_apply]`. Assume the negation of the conclusion as `hne`. Establish `h` using `descend_cpts σ p (fun j => q (c j)) ε (fun ψ => by`. Assume the negation of the conclusion as `h0`.

Use `hne ⟨(cvalR σ).comp ((ψ.comp q : A →ₐ[F] CAt σ) : A →+* CAt σ), ?_, fun x hx => ?_, h0⟩` and prove the remaining obligations. Use extensionality with `t show cvalR σ ((ψ.comp q) (algebraMap F A t)) = σ t`. Rewrite using `[AlgHom.commutes, cvalR_algebraMap]`. Use `show cvalR σ (ψ (q x)) = 0`. Rewrite using `[(hq x).2 hx, map_zero, map_zero]) θ`.

Simplify using `only [hθ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`. Conclude with `hc ((hq _).1 h)`.
-/
theorem UpperTheory.exists_complex_point_prime :
    ∀ (F A : Type) [Field F] [CommRing A] [Algebra F A] [Algebra.FiniteType F A] (σ : F →+* ℂ) (m : ℕ) (ε : Fin m → ℂ), (∀ a : Fin m → F, ∑ j, σ (a j) * ε j = 0 → a = 0) → ∀ (P : Ideal A), P.IsPrime → ∀ (c : Fin m → A) (j₀ : Fin m), c j₀ ∉ P → ∃ ψ : A →+* ℂ, ψ.comp (algebraMap F A) = σ ∧ (∀ x ∈ P, ψ x = 0) ∧ ∑ j, ε j * ψ (c j) ≠ 0 := by
  intro F A _ _ _ _ σ m ε hε P hP c j₀ hc
  classical
  haveI : CharZero F := σ.charZero
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType F A)
  let g : MvPolynomial (Fin n) F →ₐ[F] A ⧸ P := (Ideal.Quotient.mkₐ F P).comp f
  have hg : Function.Surjective g := (Ideal.Quotient.mkₐ_surjective F P).comp hf
  let p : TRing F := ⟨n, RingHom.ker g, (RingHom.ker_isPrime g).isRadical⟩
  let e : p.R ≃ₐ[F] A ⧸ P := Ideal.quotientKerAlgEquivOfSurjective hg
  let q : A →ₐ[F] p.R := (e.symm : A ⧸ P →ₐ[F] p.R).comp (Ideal.Quotient.mkₐ F P)
  have hq : ∀ x, q x = 0 ↔ x ∈ P := fun x => by
    show e.symm (Ideal.Quotient.mk P x) = 0 ↔ _
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hli : LinearIndependent F (fun j => toCAt σ (ε j)) :=
    Fintype.linearIndependent_iff.2 fun a ha j => congrFun (hε a ha) j
  obtain ⟨θ, hθ⟩ : ∃ θ : Module.Dual F (CAt σ), ∀ j, θ (toCAt σ (ε j)) = if j = j₀ then 1 else 0 := by
    obtain ⟨θ, hθ⟩ := LinearMap.exists_extend ((Finsupp.lapply j₀ : (Fin m →₀ F) →ₗ[F] F).comp hli.repr)
    refine ⟨θ, fun j => ?_⟩
    have h1 := LinearMap.congr_fun hθ ⟨toCAt σ (ε j), Submodule.subset_span ⟨j, rfl⟩⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hli.repr_eq_single j _ rfl] at h1
    simpa [Finsupp.single_apply] using h1
  by_contra hne
  have h := descend_cpts σ p (fun j => q (c j)) ε (fun ψ => by
    by_contra h0
    refine hne ⟨(cvalR σ).comp ((ψ.comp q : A →ₐ[F] CAt σ) : A →+* CAt σ), ?_, fun x hx => ?_, h0⟩
    · ext t
      show cvalR σ ((ψ.comp q) (algebraMap F A t)) = σ t
      rw [AlgHom.commutes, cvalR_algebraMap]
    · show cvalR σ (ψ (q x)) = 0
      rw [(hq x).2 hx, map_zero, map_zero]) θ
  simp only [hθ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact hc ((hq _).1 h)
