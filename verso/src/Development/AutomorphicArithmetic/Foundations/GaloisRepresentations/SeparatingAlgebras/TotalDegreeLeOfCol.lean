import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

/- English proof (translation)
Unfold `MvPolynomial.totalDegree`. Use `Finset.sup_le fun m hm => ?_` and prove the remaining obligations. Establish `hw : Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) m = ν` using `h (MvPolynomial.mem_support_iff.mp hm)`. Rewrite using `[← hw, Finsupp.weight_apply]`. Simplify using `only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW, smul_eq_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `le_of_eq (Finset.sum_congr rfl fun v _ => ?_)` and prove the remaining obligations. Simplify using `[Pi.single_apply]`.
-/
private theorem totalDegree_le_of_col {r n : ℕ} {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) ℂ}
    (h : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) F ν) : F.totalDegree ≤ ∑ i, ν i := by
  unfold MvPolynomial.totalDegree
  refine Finset.sup_le fun m hm => ?_
  have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) m = ν := h (MvPolynomial.mem_support_iff.mp hm)
  rw [← hw, Finsupp.weight_apply]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW, smul_eq_mul]
  rw [Finset.sum_comm]
  refine le_of_eq (Finset.sum_congr rfl fun v _ => ?_)
  simp [Pi.single_apply]

/- English proof (translation)
Introduce `T _ n lam x hx`. Use `Submodule.span_induction (p := fun x _ => MvPolynomial.totalDegree x ≤ ∑ τ, ∑ i, (lam τ).natW i) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `P ⟨F, hF, rfl⟩`. Use `(MvPolynomial.totalDegree_finset_prod _ _).trans (Finset.sum_le_sum fun τ _ => ?_)` and prove the remaining obligations. Use `(MvPolynomial.totalDegree_rename_le (fun v => (τ, v)) (F τ)).trans ?_` and prove the remaining obligations.

Establish `hm` using `(Submodule.mem_inf.mp (hF τ)).1`. Conclude with `totalDegree_le_of_col ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp hm)`. Simplify using the standard rewrite rules. Introduce `a b _ _ ha hb`. Conclude with `(MvPolynomial.totalDegree_add a b).trans (max_le ha hb)`.

Introduce `c a _ ha`. Conclude with `(MvPolynomial.totalDegree_smul_le c a).trans ha`.
-/
theorem UpperTheory.Gal.Gen.degLe_pf :
    UpperTheory.Gal.Gen.DegLe := by
  intro T _ n lam x hx
  refine Submodule.span_induction (p := fun x _ => MvPolynomial.totalDegree x ≤ ∑ τ, ∑ i, (lam τ).natW i)
    ?_ ?_ ?_ ?_ hx
  · rintro P ⟨F, hF, rfl⟩
    refine (MvPolynomial.totalDegree_finset_prod _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    refine (MvPolynomial.totalDegree_rename_le (fun v => (τ, v)) (F τ)).trans ?_
    have hm := (Submodule.mem_inf.mp (hF τ)).1
    exact totalDegree_le_of_col ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp hm)
  · simp
  · intro a b _ _ ha hb
    exact (MvPolynomial.totalDegree_add a b).trans (max_le ha hb)
  · intro c a _ ha
    exact (MvPolynomial.totalDegree_smul_le c a).trans ha
