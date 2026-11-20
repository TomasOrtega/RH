import Mathlib

/- English proof (translation)
Introduce `K A _ _ _ _ σ p hp b hb`. Use `haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)`. Establish `hj : p.jacobson = p` using `IsJacobsonRing.out' p hp.isRadical`. Establish `hex : ∃ m : Ideal A, p ≤ m ∧ m.IsMaximal ∧ b ∉ m`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Apply `hb` to reduce the goal to its premises. Rewrite using `[← hj]`. Use `Ideal.mem_sInf.2 ?_` and prove the remaining obligations. Introduce and unpack `J ⟨hpJ, hJ⟩`.

Conclude with `h J hpJ hJ`. Take `⟨m, hpm, hm, hbm⟩` from `hex`. Use `letI : Field (A ⧸ m) := Ideal.Quotient.field m`. Use `haveI : Algebra.FiniteType K (A ⧸ m) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective K m)`. Use `haveI : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)`.

Use `letI : Algebra K ℂ := σ.toAlgebra`. Set `f : (A ⧸ m) →ₐ[K] ℂ` to `IsAlgClosed.lift`. Use `⟨(f : (A ⧸ m) →+* ℂ).comp (Ideal.Quotient.mk m), ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Establish `h1 : Ideal.Quotient.mk m (algebraMap K A x) = algebraMap K (A ⧸ m) x` using `rfl`.

Establish `h2 : f (algebraMap K (A ⧸ m) x) = algebraMap K ℂ x` using `f.commutes x`. Conclude with `h2`. Introduce `a ha`. Establish `: Ideal.Quotient.mk m a = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (hpm ha)`. Simplify using `[this]`.

Introduce `h0`. Establish `h1 : f (Ideal.Quotient.mk m b) = 0` using `h0`. Establish `h2 : Ideal.Quotient.mk m b = 0`. Simplify using `using (map_eq_zero f).1 h1`. Conclude with `hbm (Ideal.Quotient.eq_zero_iff_mem.1 h2)`.
-/
theorem UpperTheory.Reformulated.B.DYhc4.main :
    ∀ {K A : Type} [inst : Field K] [inst_1 : CommRing A] [inst_2 : Algebra K A] [Algebra.FiniteType K A] (σ : K →+* ℂ)
      (p : Ideal A) [hp : p.IsPrime] {b : A},
      b ∉ p →
        ∃ (ψ : A →+* ℂ), ψ.comp (Algebra.algebraMap K A) = σ ∧ (∀ a ∈ p, (ψ : A → ℂ) a = (0 : ℂ)) ∧ (ψ : A → ℂ) b ≠ (0 : ℂ) := by
  intro K A _ _ _ _ σ p hp b hb
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  have hj : p.jacobson = p := IsJacobsonRing.out' p hp.isRadical
  have hex : ∃ m : Ideal A, p ≤ m ∧ m.IsMaximal ∧ b ∉ m := by
    by_contra h
    push_neg at h
    apply hb
    rw [← hj]
    refine Ideal.mem_sInf.2 ?_
    rintro J ⟨hpJ, hJ⟩
    exact h J hpJ hJ
  obtain ⟨m, hpm, hm, hbm⟩ := hex
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective K m)
  haveI : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  letI : Algebra K ℂ := σ.toAlgebra
  let f : (A ⧸ m) →ₐ[K] ℂ := IsAlgClosed.lift
  refine ⟨(f : (A ⧸ m) →+* ℂ).comp (Ideal.Quotient.mk m), ?_, ?_, ?_⟩
  · ext x
    have h1 : Ideal.Quotient.mk m (algebraMap K A x) = algebraMap K (A ⧸ m) x := rfl
    have h2 : f (algebraMap K (A ⧸ m) x) = algebraMap K ℂ x := f.commutes x
    exact h2
  · intro a ha
    have : Ideal.Quotient.mk m a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hpm ha)
    simp [this]
  · intro h0
    have h1 : f (Ideal.Quotient.mk m b) = 0 := h0
    have h2 : Ideal.Quotient.mk m b = 0 := by
      simpa using (map_eq_zero f).1 h1
    exact hbm (Ideal.Quotient.eq_zero_iff_mem.1 h2)
