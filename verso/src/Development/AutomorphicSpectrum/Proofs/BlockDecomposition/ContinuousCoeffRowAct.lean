import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.WInfCont

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Introduce `s`. Simplify `(continuous_const : Continuous fun _ : Matrix (Fin r) (Fin r) ℂ => MvPolynomial.coeff s (MvPolynomial.C a))` using `[MvPolynomial.algebraMap_eq]`. Consider the case `add p q hp hq`.

Introduce `s`. Simplify using `only [map_add, MvPolynomial.coeff_add]`. Conclude with `(hp s).add (hq s)`. Consider the case `mul_X p v hp`. Introduce `s`.

Establish `key : ∀ M : Matrix (Fin r) (Fin r) ℂ, MvPolynomial.coeff s (Formalism.GradedWeylDivisibility.rowAct ℂ (n` using `m) M (p * MvPolynomial.X v)) = ∑ b : Fin r, M v.1 b * (if (b, v.2) ∈ s.support then MvPolynomial.coeff (s - Finsupp.single (b, v.2) 1) (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M p) else 0) := by`. Introduce `M`. Establish `hX : Formalism.GradedWeylDivisibility.rowAct ℂ (n` using `m) M (MvPolynomial.X v) = ∑ b : Fin r, MvPolynomial.C (M v.1 b) * MvPolynomial.X (b, v.2) := by`. Simplify using `[Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]`. Rewrite using `[map_mul, hX, Finset.mul_sum, MvPolynomial.coeff_sum]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']`. Simplify using `only [key]`. Use `continuous_finset_sum _ fun b _ => ?_` and prove the remaining obligations. Use `((continuous_id.matrix_elem v.1 b)).mul ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `hp _`. Conclude with `continuous_const`.
-/
theorem continuous_coeff_rowAct {r m : ℕ} (f : MvPolynomial (Fin r × Fin m) ℂ) :
    ∀ s : (Fin r × Fin m) →₀ ℕ, Continuous fun M : Matrix (Fin r) (Fin r) ℂ =>
      MvPolynomial.coeff s (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro s
    simpa [MvPolynomial.algebraMap_eq] using
      (continuous_const : Continuous fun _ : Matrix (Fin r) (Fin r) ℂ => MvPolynomial.coeff s (MvPolynomial.C a))
  | add p q hp hq =>
    intro s
    simp only [map_add, MvPolynomial.coeff_add]
    exact (hp s).add (hq s)
  | mul_X p v hp =>
    intro s
    have key : ∀ M : Matrix (Fin r) (Fin r) ℂ, MvPolynomial.coeff s (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M (p * MvPolynomial.X v)) =
        ∑ b : Fin r, M v.1 b * (if (b, v.2) ∈ s.support then
          MvPolynomial.coeff (s - Finsupp.single (b, v.2) 1) (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M p) else 0) := by
      intro M
      have hX : Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M (MvPolynomial.X v) =
          ∑ b : Fin r, MvPolynomial.C (M v.1 b) * MvPolynomial.X (b, v.2) := by
        simp [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]
      rw [map_mul, hX, Finset.mul_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']
    simp only [key]
    refine continuous_finset_sum _ fun b _ => ?_
    refine ((continuous_id.matrix_elem v.1 b)).mul ?_
    split_ifs
    · exact hp _
    · exact continuous_const

/- English proof (translation)
Establish `h0 : Continuous (Matrix.detMonoidHom : Matrix (Fin n) (Fin n) ℂ →* ℂ)` using `continuous_id.matrix_det`. Establish `h1 : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) ℂ →* ℂˣ)` using `Continuous.units_map _ h0`. Conclude with `Units.continuous_val.comp (h1.zpow c)`.
-/
theorem continuous_detPow (n : ℕ) (c : ℤ) : Continuous fun g : GL (Fin n) ℂ => detPow ℂ n g c := by
  have h0 : Continuous (Matrix.detMonoidHom : Matrix (Fin n) (Fin n) ℂ →* ℂ) := continuous_id.matrix_det
  have h1 : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) ℂ →* ℂˣ) :=
    Continuous.units_map _ h0
  exact Units.continuous_val.comp (h1.zpow c)

/- English proof (translation)
Simplify using `only [sqAct, MvPolynomial.coeff_smul, smul_eq_mul]`. Conclude with `(continuous_detPow n _).mul ((continuous_coeff_rowAct f s).comp Units.continuous_val.matrix_transpose)`.
-/
theorem continuous_coeff_sqAct {n : ℕ} (lam : DomWeight n) (f : MvPolynomial (Fin n × Fin n) ℂ)
    (s : (Fin n × Fin n) →₀ ℕ) :
    Continuous fun g : GL (Fin n) ℂ => MvPolynomial.coeff s (sqAct ℂ n lam g f) := by
  simp only [sqAct, MvPolynomial.coeff_smul, smul_eq_mul]
  exact (continuous_detPow n _).mul
    ((continuous_coeff_rowAct f s).comp Units.continuous_val.matrix_transpose)

/- English proof (translation)
Set `b` to `Module.finBasis ℂ W`. Set `S : Finset (σ →₀ ℕ)` to `Finset.univ.biUnion fun i => (b i : MvPolynomial σ ℂ).support`. Set `L : W →ₗ[ℂ] (S → ℂ)` to `{ toFun := fun p s => MvPolynomial.coeff s.1 p.1 map_add' := fun p q => by funext s; simp map_smul' := fun a p => by funext s; simp }`. Establish `hL : LinearMap.ker L = ⊥`. Use `LinearMap.ker_eq_bot'.2 fun p hp => ?_` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `MvPolynomial.ext _ _ fun s => ?_` and prove the remaining obligations. Distinguish the cases in `hs : s ∈ S`. Simplify `congrFun hp ⟨s, hs⟩` using `[L]`. Establish `h0 : ∀ i, MvPolynomial.coeff s (b i : MvPolynomial σ ℂ) = 0` using `fun i => by`.

Assume the negation of the conclusion as `h`. Conclude with `hs (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, MvPolynomial.mem_support_iff.2 h⟩)`. Establish `hp' : (p : MvPolynomial σ ℂ) = ∑ i, b.repr p i • (b i : MvPolynomial σ ℂ)`. Establish `h` using `congrArg Subtype.val (b.sum_repr p)`. Rewrite `h` using `[AddSubmonoidClass.coe_finset_sum]`.

Conclude with `h.symm`. Rewrite using `[hp']`. Simplify using `[MvPolynomial.coeff_sum, h0]`. Take `⟨ψ, hψ⟩` from `LinearMap.exists_leftInverse_of_injective L hL`. Use `⟨S, fun s => (φ ∘ₗ ψ) fun j => if s = j then 1 else 0, fun p => ?_⟩` and prove the remaining obligations.

Establish `e : φ p = (φ ∘ₗ ψ) (L p)`. Establish `h` using `LinearMap.congr_fun hψ p`. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at h ⊢`. Rewrite using `[h]`. Rewrite using `[e, LinearMap.pi_apply_eq_sum_univ (φ ∘ₗ ψ) (L p)]`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_comm]`. Both sides reduce to the same expression.
-/
theorem exists_finset_factor {σ : Type} (W : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ W]
    (φ : Module.Dual ℂ W) : ∃ (S : Finset (σ →₀ ℕ)) (c : S → ℂ),
      ∀ p : W, φ p = ∑ s : S, c s * MvPolynomial.coeff s.1 p.1 := by
  let b := Module.finBasis ℂ W
  let S : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun i => (b i : MvPolynomial σ ℂ).support
  let L : W →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun p s => MvPolynomial.coeff s.1 p.1
      map_add' := fun p q => by funext s; simp
      map_smul' := fun a p => by funext s; simp }
  have hL : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun p hp => ?_
    apply Subtype.ext
    refine MvPolynomial.ext _ _ fun s => ?_
    by_cases hs : s ∈ S
    · simpa [L] using congrFun hp ⟨s, hs⟩
    · have h0 : ∀ i, MvPolynomial.coeff s (b i : MvPolynomial σ ℂ) = 0 := fun i => by
        by_contra h
        exact hs (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, MvPolynomial.mem_support_iff.2 h⟩)
      have hp' : (p : MvPolynomial σ ℂ) = ∑ i, b.repr p i • (b i : MvPolynomial σ ℂ) := by
        have h := congrArg Subtype.val (b.sum_repr p)
        rw [AddSubmonoidClass.coe_finset_sum] at h
        exact h.symm
      rw [hp']
      simp [MvPolynomial.coeff_sum, h0]
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective L hL
  refine ⟨S, fun s => (φ ∘ₗ ψ) fun j => if s = j then 1 else 0, fun p => ?_⟩
  have e : φ p = (φ ∘ₗ ψ) (L p) := by
    have h := LinearMap.congr_fun hψ p
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h ⊢
    rw [h]
  rw [e, LinearMap.pi_apply_eq_sum_univ (φ ∘ₗ ψ) (L p)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_eq_mul, mul_comm]
  rfl

/- English proof (translation)
Take `⟨S, c, h⟩` from `exists_finset_factor (nablaSq ℂ n lam) φ`. Simplify using `only [h]`. Conclude with `continuous_finset_sum _ fun s _ => continuous_const.mul (continuous_coeff_sqAct lam f.1 s.1)`.
-/
theorem continuous_sqRep_coeff {n : ℕ} (lam : DomWeight n) (f : nablaSq ℂ n lam)
    (φ : Module.Dual ℂ (nablaSq ℂ n lam)) :
    Continuous fun g : GL (Fin n) ℂ => φ (GlobalTheory.Branching.sqRep ℂ n lam g f) := by
  obtain ⟨S, c, h⟩ := exists_finset_factor (nablaSq ℂ n lam) φ
  simp only [h]
  exact continuous_finset_sum _ fun s _ => continuous_const.mul (continuous_coeff_sqAct lam f.1 s.1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end GlobalTheory.CompanionTheory.WInfCont
