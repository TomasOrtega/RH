import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Formalism.GradedWeylDivisibility.FinalD

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

abbrev Laurent (k : Type) [Field k] (N : ℕ) : Type := AddMonoidAlgebra k (Fin N → ℤ)

def laurentVar (k : Type) [Field k] (N : ℕ) (a : Fin N) : (Laurent k N)ˣ where
  val := AddMonoidAlgebra.single (Pi.single a 1) 1
  inv := AddMonoidAlgebra.single (-Pi.single a 1) 1
  val_inv := by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
  inv_val := by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]

/- English proof (translation)
Establish `h : ∀ s : Finset (Fin N), (∏ a ∈ s, ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N) ^ d a) = AddMonoidAlgebra.single (∑ a ∈ s, d a • (Pi.single a 1 : Fin N → ℤ)) 1`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [AddMonoidAlgebra.one_def]`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, ih]`. Simplify using `[laurentVar, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single]`. Rewrite using `[h]`. Use `congr 1`. Use function extensionality and compare the values at `b`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem prod_laurentVar_pow (k : Type) [Field k] (N : ℕ) (d : Fin N → ℕ) :
    (∏ a, ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N) ^ d a) =
      AddMonoidAlgebra.single (fun a => (d a : ℤ)) 1 := by
  have h : ∀ s : Finset (Fin N), (∏ a ∈ s, ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N) ^ d a) =
      AddMonoidAlgebra.single (∑ a ∈ s, d a • (Pi.single a 1 : Fin N → ℤ)) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [AddMonoidAlgebra.one_def]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      simp [laurentVar, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single]
  rw [h]
  congr 1
  funext b
  simp [Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨h, hh, rfl⟩` from `hy`. Introduce `ν`. Distinguish the cases in `hν : ν = 0`.

Use `⟨h, hh, fun m => ?_⟩` and prove the remaining obligations. Substitute `hν` using the available equality. Simplify using `[coeff_map, AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.coeff_single]`. Use `⟨0, zero_mem _, fun m => ?_⟩` and prove the remaining obligations. Simplify using `[coeff_map, AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hν]`.

Consider the case `zero`. Introduce `ν`. Conclude with `⟨0, zero_mem _, fun m => by simp⟩`. Consider the case `add y z _ _ hy hz`. Introduce `ν`.

Take `⟨a, ha, ha'⟩` from `hy ν`. Take `⟨b, hb, hb'⟩` from `hz ν`. Conclude with `⟨a + b, add_mem ha hb, fun m => by simp [ha', hb']⟩`. Consider the case `smul c y _ hy`. Proceed by induction on `c using AddMonoidAlgebra.induction_linear with`.

Consider the case `zero`. Introduce `ν`. Conclude with `⟨0, zero_mem _, fun m => by simp⟩`. Consider the case `add c₁ c₂ h₁ h₂`. Introduce `ν`.

Take `⟨a, ha, ha'⟩` from `h₁ ν`. Take `⟨b, hb, hb'⟩` from `h₂ ν`. Use `⟨a + b, add_mem ha hb, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[add_smul]`. Simplify using `[ha', hb']`.

Consider the case `single u r`. Introduce `ν`. Take `⟨a, ha, ha'⟩` from `hy (-u + ν)`. Use `⟨r • a, Submodule.smul_mem _ _ ha, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_smul, coeff_smul, smul_eq_mul, smul_eq_mul, ha']`.

Conclude with `(AddMonoidAlgebra.coeff_single_mul_apply _ _ _ _).symm`.
-/
theorem exists_coeff_of_mem_span {k : Type} [Field k] {N : ℕ} {σ : Type}
    (M : Submodule k (MvPolynomial σ k)) (x : MvPolynomial σ (Laurent k N))
    (hx : x ∈ Submodule.span (Laurent k N)
      (map (algebraMap k (Laurent k N)) '' (M : Set (MvPolynomial σ k)))) :
    ∀ ν : Fin N → ℤ, ∃ h ∈ M, ∀ m, coeff m h = (coeff m x : Laurent k N).coeff ν := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, hh, rfl⟩ := hy
    intro ν
    by_cases hν : ν = 0
    · refine ⟨h, hh, fun m => ?_⟩
      subst hν
      simp [coeff_map, AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.coeff_single]
    · refine ⟨0, zero_mem _, fun m => ?_⟩
      simp [coeff_map, AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hν]
  | zero =>
    intro ν
    exact ⟨0, zero_mem _, fun m => by simp⟩
  | add y z _ _ hy hz =>
    intro ν
    obtain ⟨a, ha, ha'⟩ := hy ν
    obtain ⟨b, hb, hb'⟩ := hz ν
    exact ⟨a + b, add_mem ha hb, fun m => by simp [ha', hb']⟩
  | smul c y _ hy =>
    induction c using AddMonoidAlgebra.induction_linear with
    | zero =>
      intro ν
      exact ⟨0, zero_mem _, fun m => by simp⟩
    | add c₁ c₂ h₁ h₂ =>
      intro ν
      obtain ⟨a, ha, ha'⟩ := h₁ ν
      obtain ⟨b, hb, hb'⟩ := h₂ ν
      refine ⟨a + b, add_mem ha hb, fun m => ?_⟩
      rw [add_smul]
      simp [ha', hb']
    | single u r =>
      intro ν
      obtain ⟨a, ha, ha'⟩ := hy (-u + ν)
      refine ⟨r • a, Submodule.smul_mem _ _ ha, fun m => ?_⟩
      rw [coeff_smul, coeff_smul, smul_eq_mul, smul_eq_mul, ha']
      exact (AddMonoidAlgebra.coeff_single_mul_apply _ _ _ _).symm

/- English proof (translation)
Establish `h1` using `hM (Laurent k N) (diagGL (Laurent k N) N (laurentVar k N)) f hf`. Establish `hdiag : ((diagGL (Laurent k N) N (laurentVar k N) : GL (Fin N) (Laurent k N)) : Matrix (Fin N) (Fin N) (Laurent k N)).transpose = Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N)` using `by show (Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N)).transpose = _`. Conclude with `Matrix.diagonal_transpose _`. Establish `h2 : rowAct (Laurent k N) (n` using `N) (Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N)) (map (algebraMap k (Laurent k N)) f) ∈ Submodule.span (Laurent k N) (map (algebraMap k (Laurent k N)) '' (M : Set (MvPolynomial (Fin N × Fin N) k))) := by`. Set `u : (Laurent k N)ˣ` to `Matrix.GeneralLinearGroup.det (diagGL (Laurent k N) N (laurentVar k N)) ^ lam.detShift`.

Establish `h3` using `Submodule.smul_mem _ ((u⁻¹ : (Laurent k N)ˣ) : Laurent k N) h1`. Establish `e3 : sqAct (Laurent k N) N lam (diagGL (Laurent k N) N (laurentVar k N)) (map (algebraMap k (Laurent k N)) f) = (u : Laurent k N) • rowAct (Laurent k N) (n` using `N) (Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N)) (map (algebraMap k (Laurent k N)) f) := by`. Unfold `sqAct detPow`. Rewrite using `[hdiag]`. Rewrite `h3` using `[e3, smul_smul, Units.inv_mul, one_smul]`.

Conclude with `h3`. Take `⟨h, hh, hc⟩` from `exists_coeff_of_mem_span M _ h2 (fun a => (μ a : ℤ))`. Establish `e : weightedHomogeneousComponent (rowW N N) μ f = h`. Use extensionality with `m`. Rewrite using `[hc, coeff_weightedHomogeneousComponent, ldrow_coeff_rowAct_diag, coeff_map, prod_laurentVar_pow, AddMonoidAlgebra.coe_algebraMap]`.

Establish `hw : Finsupp.weight (rowW N N) m = μ ↔ (fun a => (rowDeg m a : ℤ)) = fun a => (μ a : ℤ)`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Use function extensionality and compare the values at `a`. Rewrite using `[← ldrow_weight_rowW, hw]`.

Introduce `hw`. Use function extensionality and compare the values at `a`. Use `congrFun hw a` as an intermediate fact. Rewrite using `[ldrow_weight_rowW]`. Conclude with `this` after adjusting the coercions.

Simplify using `[AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hw]`. Rewrite using `[e]`. Conclude with `hh`.
-/
theorem weightedHomogeneousComponent_mem_of_isGLSubmodule (k : Type) [Field k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k)) (hM : GlobalTheory.Published.IsGLSubmodule k N lam M)
    (μ : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) k) (hf : f ∈ M) :
    weightedHomogeneousComponent (rowW N N) μ f ∈ M := by
  have h1 := hM (Laurent k N) (diagGL (Laurent k N) N (laurentVar k N)) f hf
  have hdiag : ((diagGL (Laurent k N) N (laurentVar k N) : GL (Fin N) (Laurent k N)) :
      Matrix (Fin N) (Fin N) (Laurent k N)).transpose =
      Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N) := by
    show (Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N)).transpose = _
    exact Matrix.diagonal_transpose _
  have h2 : rowAct (Laurent k N) (n := N)
      (Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N))
      (map (algebraMap k (Laurent k N)) f) ∈ Submodule.span (Laurent k N)
        (map (algebraMap k (Laurent k N)) '' (M : Set (MvPolynomial (Fin N × Fin N) k))) := by
    let u : (Laurent k N)ˣ :=
      Matrix.GeneralLinearGroup.det (diagGL (Laurent k N) N (laurentVar k N)) ^ lam.detShift
    have h3 := Submodule.smul_mem _ ((u⁻¹ : (Laurent k N)ˣ) : Laurent k N) h1
    have e3 : sqAct (Laurent k N) N lam (diagGL (Laurent k N) N (laurentVar k N))
        (map (algebraMap k (Laurent k N)) f) = (u : Laurent k N) • rowAct (Laurent k N) (n := N)
          (Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N))
          (map (algebraMap k (Laurent k N)) f) := by
      unfold sqAct detPow
      rw [hdiag]
    rw [e3, smul_smul, Units.inv_mul, one_smul] at h3
    exact h3
  obtain ⟨h, hh, hc⟩ := exists_coeff_of_mem_span M _ h2 (fun a => (μ a : ℤ))
  have e : weightedHomogeneousComponent (rowW N N) μ f = h := by
    ext m
    rw [hc, coeff_weightedHomogeneousComponent, ldrow_coeff_rowAct_diag, coeff_map,
      prod_laurentVar_pow, AddMonoidAlgebra.coe_algebraMap]
    have hw : Finsupp.weight (rowW N N) m = μ ↔ (fun a => (rowDeg m a : ℤ)) = fun a => (μ a : ℤ) := by
      constructor
      · intro hw
        funext a
        rw [← ldrow_weight_rowW, hw]
      · intro hw
        funext a
        have := congrFun hw a
        rw [ldrow_weight_rowW]
        exact_mod_cast this
    simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hw]
  rw [e]
  exact hh

end GlobalTheory.Alc
