import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Formalism.ConjugateSelfDual.Statement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsUnitOfInvIntegral
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ResidueHomNorm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteOfIsFiniteLength
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DigitExpansionLattice

/- English proof (translation)
Introduce `l _ c _ R _ _ _ y`. Take `⟨hint, hO, hm⟩` from `UpperTheory.integral_dvr_norm l c.O`. Establish `hO' : ∀ a : c.O, ‖algebraMap c.O (Formalism.ConjugateSelfDual.Qbar l) a‖ ≤ 1` using `hO`. Establish `hres : ∀ x : R, ∃ a : c.O, x - algebraMap c.O R a ∈ IsLocalRing.maximalIdeal R` using `UpperTheory.V.Alg.IsCO.res_surj`. Take `⟨hb1, hb2⟩` from `UpperTheory.residue_hom_norm (O := c.O) (Ω := Formalism.ConjugateSelfDual.Qbar l) hres hO' hint y`.

Use `⟨?_, hb1, hb2⟩` and prove the remaining obligations. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible c.O`. Establish `hJ : ∀ x : R, ∃ P : Polynomial c.O, P.Monic ∧ Polynomial.aeval x P ∈ RingHom.ker y` using `fun x => by`. Take `⟨P, hP, h0⟩` from `hint (y x) (hb1 x)`. Use `⟨P, hP, ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.mem_ker]`. Establish `h1 : Polynomial.aeval (y x) P = 0` using `h0`. Rewrite `h1` using `[Polynomial.aeval_algHom_apply]`. Conclude with `h1`. Establish `hfin` using `UpperTheory.monic_ideal_completion hres (RingHom.ker y) hJ ϖ hϖ`.

Establish `hlt : ‖algebraMap c.O (Formalism.ConjugateSelfDual.Qbar l) ϖ‖ < 1` using `hm ϖ hϖ.not_isUnit`. Use `letI := Fintype.ofFinite (R ⧸ (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}))`. Establish `key` using `UpperTheory.digit_expansion_lattice hO' ϖ hϖ hlt (Subalgebra.toSubmodule y.range) (fun s hs => by`. Take `⟨r, rfl⟩` from `hs`. Conclude with `hb1 r)`.

Use the proof step `(Finset.univ.image fun q : R ⧸ (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}) => y (Quotient.out q))`. Use the proof step `(fun e he => by`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 he`. Conclude with `⟨_, rfl⟩)`. Use the proof step `(fun s hs => by`.

Take `⟨r, rfl⟩` from `hs`. Establish `hq : r - Quotient.out (Ideal.Quotient.mk (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}) r) ∈ RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}`. Rewrite using `[← Ideal.Quotient.eq]`. Simplify using `[Ideal.Quotient.mk_out]`. Take `⟨j, hj, t, ht, hjt⟩` from `Submodule.mem_sup.1 hq`.

Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 ht`. Use `⟨_, Finset.mem_image.2 ⟨Ideal.Quotient.mk _ r, Finset.mem_univ _, rfl⟩, y a, ⟨a, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg y hjt`. Rewrite `h2` using `[map_add, RingHom.mem_ker.1 hj, map_sub, map_mul, AlgHom.commutes]`. Rewrite using `[Algebra.smul_def, mul_comm]`.

Take the linear combination `-h2)`. Conclude with `key`.
-/
theorem UpperTheory.Reformulated.B.CoPoint.coPt :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) [UpperTheory.V.Fr.IsCoef l ↥c.O] (R : Type)
    [inst_2 : CommRing R] [inst_3 : Algebra (↥c.O) R] [inst_4 : UpperTheory.V.Alg.IsCO (↥c.O) R]
    (y : R →ₐ[↥c.O] Formalism.ConjugateSelfDual.Qbar l),
    Module.Finite ↥c.O ↥y.range ∧
      (∀ (a : R), ‖(y : R → Formalism.ConjugateSelfDual.Qbar l) a‖ ≤ (1 : ℝ)) ∧
        ∀ a ∈ IsLocalRing.maximalIdeal R,
          ‖(y : R → Formalism.ConjugateSelfDual.Qbar l) a‖ <
            (1 :
              ℝ) := by
  intro l _ c _ R _ _ _ y
  obtain ⟨hint, hO, hm⟩ := UpperTheory.integral_dvr_norm l c.O
  have hO' : ∀ a : c.O, ‖algebraMap c.O (Formalism.ConjugateSelfDual.Qbar l) a‖ ≤ 1 := hO
  have hres : ∀ x : R, ∃ a : c.O, x - algebraMap c.O R a ∈ IsLocalRing.maximalIdeal R :=
    UpperTheory.V.Alg.IsCO.res_surj
  obtain ⟨hb1, hb2⟩ := UpperTheory.residue_hom_norm (O := c.O) (Ω := Formalism.ConjugateSelfDual.Qbar l) hres hO' hint y
  refine ⟨?_, hb1, hb2⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hJ : ∀ x : R, ∃ P : Polynomial c.O, P.Monic ∧ Polynomial.aeval x P ∈ RingHom.ker y := fun x => by
    obtain ⟨P, hP, h0⟩ := hint (y x) (hb1 x)
    refine ⟨P, hP, ?_⟩
    rw [RingHom.mem_ker]
    have h1 : Polynomial.aeval (y x) P = 0 := h0
    rw [Polynomial.aeval_algHom_apply] at h1
    exact h1
  have hfin := UpperTheory.monic_ideal_completion hres (RingHom.ker y) hJ ϖ hϖ
  have hlt : ‖algebraMap c.O (Formalism.ConjugateSelfDual.Qbar l) ϖ‖ < 1 :=
    hm ϖ hϖ.not_isUnit
  classical
  letI := Fintype.ofFinite (R ⧸ (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}))
  have key := UpperTheory.digit_expansion_lattice hO' ϖ hϖ hlt (Subalgebra.toSubmodule y.range)
    (fun s hs => by
      obtain ⟨r, rfl⟩ := hs
      exact hb1 r)
    (Finset.univ.image fun q : R ⧸ (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}) => y (Quotient.out q))
    (fun e he => by
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 he
      exact ⟨_, rfl⟩)
    (fun s hs => by
      obtain ⟨r, rfl⟩ := hs
      have hq : r - Quotient.out (Ideal.Quotient.mk (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}) r) ∈
          RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ} := by
        rw [← Ideal.Quotient.eq]
        simp [Ideal.Quotient.mk_out]
      obtain ⟨j, hj, t, ht, hjt⟩ := Submodule.mem_sup.1 hq
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 ht
      refine ⟨_, Finset.mem_image.2 ⟨Ideal.Quotient.mk _ r, Finset.mem_univ _, rfl⟩, y a, ⟨a, rfl⟩, ?_⟩
      have h2 := congrArg y hjt
      rw [map_add, RingHom.mem_ker.1 hj, map_sub, map_mul, AlgHom.commutes] at h2
      rw [Algebra.smul_def, mul_comm]
      linear_combination -h2)
  exact key
