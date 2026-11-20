import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

/- English proof (translation)
Take `⟨b, ⟨-, hb, -⟩, -⟩` from `Formalism.GradedWeylDivisibility.sSBasis ℂ n n ν`. Establish `: Finite (Formalism.GradedWeylDivisibility.ssIdx n n ν)` using `(Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype`. Rewrite using `[← hb]`. Conclude with `FiniteDimensional.span_of_finite ℂ (Set.finite_range b)`.
-/
private theorem fd_dw (n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν) := by
  obtain ⟨b, ⟨-, hb, -⟩, -⟩ := Formalism.GradedWeylDivisibility.sSBasis ℂ n n ν
  have : Finite (Formalism.GradedWeylDivisibility.ssIdx n n ν) := (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  rw [← hb]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range b)

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Introduce `ℓ`. Simplify using `only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.algHom_C]`. Conclude with `continuous_const`.

Consider the case `add p q hp hq`. Introduce `ℓ`. Simplify using `only [map_add]`. Conclude with `(hp ℓ).add (hq ℓ)`. Consider the case `mul_X p v hp`.

Introduce `ℓ`. Establish `e : ∀ g : Matrix (Fin n) (Fin n) ℂ, ℓ (Formalism.GradedWeylDivisibility.rowAct ℂ g (p * MvPolynomial.X v)) = ∑ b : Fin n, g v.1 b * (ℓ ∘ₗ LinearMap.mulRight ℂ (MvPolynomial.X (b, v.2))) (Formalism.GradedWeylDivisibility.rowAct ℂ g p)`. Introduce `g`. Establish `h1 : Formalism.GradedWeylDivisibility.rowAct ℂ g (MvPolynomial.X v : MvPolynomial (Fin n × Fin n) ℂ) = ∑ b : Fin n, MvPolynomial.C (g v.1 b) * MvPolynomial.X (b, v.2)`. Simplify using `only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]`.

Rewrite using `[map_mul, h1, Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]`. Both sides reduce to the same expression. Simplify using `only [e]`.

Use `continuous_finset_sum _ fun b _ => ?_` and prove the remaining obligations. Conclude with `(continuous_id.matrix_elem v.1 b).mul (hp _)`.
-/
private theorem cont_rowAct (n : ℕ) (f : MvPolynomial (Fin n × Fin n) ℂ) :
    ∀ ℓ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ,
      Continuous fun g : Matrix (Fin n) (Fin n) ℂ => ℓ (Formalism.GradedWeylDivisibility.rowAct ℂ g f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro ℓ
    simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.algHom_C]
    exact continuous_const
  | add p q hp hq =>
    intro ℓ
    simp only [map_add]
    exact (hp ℓ).add (hq ℓ)
  | mul_X p v hp =>
    intro ℓ
    have e : ∀ g : Matrix (Fin n) (Fin n) ℂ, ℓ (Formalism.GradedWeylDivisibility.rowAct ℂ g (p * MvPolynomial.X v)) =
        ∑ b : Fin n, g v.1 b * (ℓ ∘ₗ LinearMap.mulRight ℂ (MvPolynomial.X (b, v.2))) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) := by
      intro g
      have h1 : Formalism.GradedWeylDivisibility.rowAct ℂ g (MvPolynomial.X v : MvPolynomial (Fin n × Fin n) ℂ) =
          ∑ b : Fin n, MvPolynomial.C (g v.1 b) * MvPolynomial.X (b, v.2) := by
        simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]
      rw [map_mul, h1, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
      rfl
    simp only [e]
    refine continuous_finset_sum _ fun b _ => ?_
    exact (continuous_id.matrix_elem v.1 b).mul (hp _)

/- English proof (translation)
Take `⟨L, hL⟩` from `LinearMap.exists_extend ℓ`. Establish `e : ∀ g : GL (Fin n) ℂ, ℓ (Formalism.UG.dualWeylRep ℂ n n ν g u) = L (Formalism.GradedWeylDivisibility.rowAct ℂ ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ))`. Introduce `g`. Rewrite using `[← hL, LinearMap.comp_apply, Submodule.subtype_apply, Formalism.UG.dualWeylRep_apply]`. Both sides reduce to the same expression.

Simplify using `only [e]`. Conclude with `(cont_rowAct n _ L).comp Units.continuous_coe_inv`.
-/
private theorem cont_rep (n : ℕ) (ν : Fin n → ℕ) (ℓ : Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν →ₗ[ℂ] ℂ)
    (u : Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν) :
    Continuous fun g : GL (Fin n) ℂ => ℓ (Formalism.UG.dualWeylRep ℂ n n ν g u) := by
  obtain ⟨L, hL⟩ := LinearMap.exists_extend ℓ
  have e : ∀ g : GL (Fin n) ℂ, ℓ (Formalism.UG.dualWeylRep ℂ n n ν g u) =
      L (Formalism.GradedWeylDivisibility.rowAct ℂ ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ)) := by
    intro g
    rw [← hL, LinearMap.comp_apply, Submodule.subtype_apply, Formalism.UG.dualWeylRep_apply]
    rfl
  simp only [e]
  exact (cont_rowAct n _ L).comp Units.continuous_coe_inv

/- English proof (translation)
Set `b` to `fun i => Module.finBasis ℂ (V i)`. Establish `e : ∀ x, (m fun i => F i x) = ∑ r : ∀ i, Fin (Module.finrank ℂ (V i)), (∏ i, (b i).coord (r i) (F i x)) • m fun i => b i (r i)`. Introduce `x`. Establish `h1 : (fun i => F i x) = fun i => ∑ j, (b i).coord j (F i x) • b i j`. Use function extensionality and compare the values at `i`.

Simplify using `only [Module.Basis.coord_apply, Module.Basis.sum_repr]`. Rewrite using `[h1, MultilinearMap.map_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.map_smul_univ]`. Simplify using `only [e]`.

Use `continuous_finset_sum _ fun r _ => ?_` and prove the remaining obligations. Conclude with `(continuous_finset_prod _ fun i _ => hF i _).smul continuous_const`.
-/
private theorem cont_multi {X ι : Type} [TopologicalSpace X] [Fintype ι] [DecidableEq ι] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (m : MultilinearMap ℂ V ℂ) (F : ∀ i, X → V i) (hF : ∀ i (ℓ : V i →ₗ[ℂ] ℂ), Continuous fun x => ℓ (F i x)) :
    Continuous fun x => m fun i => F i x := by
  let b := fun i => Module.finBasis ℂ (V i)
  have e : ∀ x, (m fun i => F i x) = ∑ r : ∀ i, Fin (Module.finrank ℂ (V i)),
      (∏ i, (b i).coord (r i) (F i x)) • m fun i => b i (r i) := by
    intro x
    have h1 : (fun i => F i x) = fun i => ∑ j, (b i).coord j (F i x) • b i j := by
      funext i
      simp only [Module.Basis.coord_apply, Module.Basis.sum_repr]
    rw [h1, MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ]
  simp only [e]
  refine continuous_finset_sum _ fun r _ => ?_
  exact (continuous_finset_prod _ fun i _ => hF i _).smul continuous_const

/- English proof (translation)
Introduce `n ι _ _ mu sh`. Use `haveI : ∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) := fun τ => fd_dw n _`. Use `⟨Module.Finite.of_basis (Basis.piTensorProduct fun τ => Module.finBasis ℂ _), fun ℓ u => ?_⟩` and prove the remaining obligations. Establish `h1 : Continuous fun g : ι → GL (Fin n) ℂ => ℓ (GlobalTheory.ExpFrame.grp ℂ n mu g u)`. Proceed by induction on `u using PiTensorProduct.induction_on with`.

Consider the case `smul_tprod c x`. Simplify using `only [map_smul, GlobalTheory.SemilinTransport.grp_tprod]`. Use `Continuous.const_smul ?_ c` and prove the remaining obligations. Conclude with `cont_multi (ℓ.compMultilinearMap (PiTensorProduct.tprod ℂ)) (fun τ (g : ι → GL (Fin n) ℂ) => Formalism.UG.dualWeylRep ℂ n n _ (g τ) (x τ)) (fun τ l => (cont_rep n _ l (x τ)).comp (continuous_apply τ))`. Consider the case `add a b ha hb`.

Simplify using `only [map_add]`. Conclude with `ha.add hb`. Simplify using `only [wtOp_apply, map_smul]`. Establish `h2 : Continuous fun g : ι → GL (Fin n) ℂ => (∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : ℂˣ)`. Use `continuous_finset_prod _ fun τ _ => ?_` and prove the remaining obligations.

Use `Continuous.zpow ?_ _` and prove the remaining obligations. Conclude with `Matrix.GeneralLinearGroup.continuous_det.comp (continuous_apply τ)`. Conclude with `(Units.continuous_val.comp h2).smul h1`.
-/
theorem UpperTheory.finiteDimensional_nablaT_and_continuous_wtOp :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ),
        FiniteDimensional ℂ (NablaT ℂ n mu) ∧ ∀ (ℓ : NablaT ℂ n mu →ₗ[ℂ] ℂ) (u : NablaT ℂ n mu),
          Continuous fun g : ι → GL (Fin n) ℂ => ℓ (wtOp ℂ n mu sh g u) := by
  intro n ι _ _ mu sh
  haveI : ∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) := fun τ => fd_dw n _
  refine ⟨Module.Finite.of_basis (Basis.piTensorProduct fun τ => Module.finBasis ℂ _), fun ℓ u => ?_⟩
  have h1 : Continuous fun g : ι → GL (Fin n) ℂ => ℓ (GlobalTheory.ExpFrame.grp ℂ n mu g u) := by
    induction u using PiTensorProduct.induction_on with
    | smul_tprod c x =>
      simp only [map_smul, GlobalTheory.SemilinTransport.grp_tprod]
      refine Continuous.const_smul ?_ c
      exact cont_multi (ℓ.compMultilinearMap (PiTensorProduct.tprod ℂ))
        (fun τ (g : ι → GL (Fin n) ℂ) => Formalism.UG.dualWeylRep ℂ n n _ (g τ) (x τ))
        (fun τ l => (cont_rep n _ l (x τ)).comp (continuous_apply τ))
    | add a b ha hb =>
      simp only [map_add]
      exact ha.add hb
  simp only [wtOp_apply, map_smul]
  have h2 : Continuous fun g : ι → GL (Fin n) ℂ =>
      (∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : ℂˣ) := by
    refine continuous_finset_prod _ fun τ _ => ?_
    refine Continuous.zpow ?_ _
    exact Matrix.GeneralLinearGroup.continuous_det.comp (continuous_apply τ)
  exact (Units.continuous_val.comp h2).smul h1
