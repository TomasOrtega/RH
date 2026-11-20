import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
open NumberField
open scoped ContDiff

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] {d : ℕ}

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact i.elim0`. Consider the case `succ k ih`. Rewrite using `[List.ofFn_succ, List.prod_cons]`. Consider the cases of `i using Fin.cases with`.

Consider the case `zero`. Rewrite using `[List.prod_eq_one, mul_one]`. Introduce `x hx`. Take `⟨j, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `h _ (Fin.succ_ne_zero j)`.

Consider the case `succ i`. Rewrite using `[h 0 (Fin.succ_ne_zero i).symm, one_mul]`. Conclude with `ih _ i fun j hj => h _ fun e => hj (Fin.succ_injective _ e)`.
-/
theorem prod_ofFn_eq_of_ne {M : Type*} [Monoid M] {k : ℕ} (f : Fin k → M) (i : Fin k)
    (h : ∀ j, j ≠ i → f j = 1) : (List.ofFn f).prod = f i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ (Fin.succ_ne_zero j)
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact ih _ i fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

/- English proof (translation)
Use `letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra`. Use `haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _`. Set `T : Matrix (Fin d) (Fin d) (Cinf E) →L[ℝ] Lie E d` to `LinearMap.toContinuousLinearMap (LinearMap.id : Lie E d →ₗ[ℝ] Lie E d)`. Establish `hexp : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin d) (Fin d) (Cinf E) → _)` using `contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt`.

Establish `hprod : ∀ (n : ℕ) (g : Fin n → (Fin k → ℝ) → Matrix (Fin d) (Fin d) (Cinf E)), (∀ i, ContDiff ℝ ∞ (g i)) → ContDiff ℝ ∞ (fun t => (List.ofFn fun i => g i t).prod)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro g _`. Simplify using `using contDiff_const`.

Consider the case `succ n ih`. Introduce `g hg`. Simplify using `only [List.ofFn_succ, List.prod_cons]`. Conclude with `(hg 0).mul (ih _ fun i => hg _)`. Establish `h` using `hprod k (fun i t => NormedSpace.exp (t i • X i)) fun i => hexp.comp ((contDiff_apply ℝ ℝ i).smul contDiff_const)`.

Conclude with `T.contDiff.comp (contDiff_const.mul h)`.
-/
theorem contDiff_prodExp (y : Lie E d) {k : ℕ} (X : Fin k → Matrix (Fin d) (Fin d) (Cinf E)) :
    ContDiff ℝ ∞ (fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)) := by
  letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin d) (Fin d) (Cinf E) →L[ℝ] Lie E d :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E d →ₗ[ℝ] Lie E d)
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin d) (Fin d) (Cinf E) → _) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have hprod : ∀ (n : ℕ) (g : Fin n → (Fin k → ℝ) → Matrix (Fin d) (Fin d) (Cinf E)),
      (∀ i, ContDiff ℝ ∞ (g i)) → ContDiff ℝ ∞ (fun t => (List.ofFn fun i => g i t).prod) := by
    intro n
    induction n with
    | zero => intro g _; simpa using contDiff_const
    | succ n ih =>
      intro g hg
      simp only [List.ofFn_succ, List.prod_cons]
      exact (hg 0).mul (ih _ fun i => hg _)
  have h := hprod k (fun i t => NormedSpace.exp (t i • X i))
    fun i => hexp.comp ((contDiff_apply ℝ ℝ i).smul contDiff_const)
  exact T.contDiff.comp (contDiff_const.mul h)

end GlobalTheory.SecondKind

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] {d : ℕ}

/- English proof (translation)
Use `letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra`. Use `haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _`. Set `T : Matrix (Fin d) (Fin d) (Cinf E) →L[ℝ] Lie E d` to `LinearMap.toContinuousLinearMap (LinearMap.id : Lie E d →ₗ[ℝ] Lie E d)`. Establish `h` using `((hasDerivAt_exp_smul_const' (𝕂 := ℝ) Z (0 : ℝ)).const_mul (Matrix.of y))`.

Rewrite `h` using `[zero_smul, NormedSpace.exp_zero, mul_one]`. Conclude with `T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h`.
-/
theorem hasDerivAt_mulExp (y : Lie E d) (Z : Matrix (Fin d) (Fin d) (Cinf E)) :
    HasDerivAt (fun s : ℝ => toL (Matrix.of y * NormedSpace.exp (s • Z))) (toL (Matrix.of y * Z)) 0 := by
  letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin d) (Fin d) (Cinf E) →L[ℝ] Lie E d :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E d →ₗ[ℝ] Lie E d)
  have h := ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) Z (0 : ℝ)).const_mul (Matrix.of y))
  rw [zero_smul, NormedSpace.exp_zero, mul_one] at h
  exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

/- English proof (translation)
Use `set Θ := fun t : Fin k → ℝ => toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)`. Establish `hΘ : HasFDerivAt Θ (fderiv ℝ Θ 0) (0 : Fin k → ℝ)` using `((contDiff_prodExp y X).differentiable (by simp)).differentiableAt.hasFDerivAt`. Set `J : ℝ →L[ℝ] (Fin k → ℝ)` to `ContinuousLinearMap.single ℝ (fun _ : Fin k => ℝ) i`. Establish `hJ0 : J 0 = 0` using `map_zero J`. Establish `h1 : HasFDerivAt (Θ ∘ J) ((fderiv ℝ Θ 0).comp J) 0`.

Establish `hΘ' : HasFDerivAt Θ (fderiv ℝ Θ 0) (J 0)` using `by rw [hJ0]; exact hΘ`. Conclude with `hΘ'.comp (0 : ℝ) J.hasFDerivAt`. Establish `e : Θ ∘ J = fun s : ℝ => toL (Matrix.of y * NormedSpace.exp (s • X i))`. Use function extensionality and compare the values at `s`. Simplify using `only [Function.comp_apply, Θ]`.

Use `congr 2`. Rewrite using `[prod_ofFn_eq_of_ne _ i]`. Simplify using `[J]`. Introduce `j hj`. Simplify using `[J, Pi.single_eq_of_ne hj]`.

Rewrite `h1` using `[e]`. Establish `h2` using `h1.hasDerivAt.unique (hasDerivAt_mulExp y (X i))`. Establish `h3 : Pi.single i c = c • J 1`. Simplify using `[J, ← Pi.single_smul]`. Rewrite using `[h3, map_smul]`.

Simplify using `using congrArg (c • ·) h2`.
-/
theorem fderiv_prodExp (y : Lie E d) {k : ℕ} (X : Fin k → Matrix (Fin d) (Fin d) (Cinf E)) (i : Fin k) (c : ℝ) :
    fderiv ℝ (fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)) 0 (Pi.single i c) =
      c • toL (Matrix.of y * X i) := by
  set Θ := fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)
  have hΘ : HasFDerivAt Θ (fderiv ℝ Θ 0) (0 : Fin k → ℝ) :=
    ((contDiff_prodExp y X).differentiable (by simp)).differentiableAt.hasFDerivAt
  let J : ℝ →L[ℝ] (Fin k → ℝ) := ContinuousLinearMap.single ℝ (fun _ : Fin k => ℝ) i
  have hJ0 : J 0 = 0 := map_zero J
  have h1 : HasFDerivAt (Θ ∘ J) ((fderiv ℝ Θ 0).comp J) 0 := by
    have hΘ' : HasFDerivAt Θ (fderiv ℝ Θ 0) (J 0) := by rw [hJ0]; exact hΘ
    exact hΘ'.comp (0 : ℝ) J.hasFDerivAt
  have e : Θ ∘ J = fun s : ℝ => toL (Matrix.of y * NormedSpace.exp (s • X i)) := by
    funext s
    simp only [Function.comp_apply, Θ]
    congr 2
    rw [prod_ofFn_eq_of_ne _ i]
    · simp [J]
    · intro j hj
      simp [J, Pi.single_eq_of_ne hj]
  rw [e] at h1
  have h2 := h1.hasDerivAt.unique (hasDerivAt_mulExp y (X i))
  have h3 : Pi.single i c = c • J 1 := by
    simp [J, ← Pi.single_smul]
  rw [h3, map_smul]
  simpa using congrArg (c • ·) h2

end GlobalTheory.SecondKind

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

/- English proof (translation)
Introduce `E _ _ d f S hS hf x₀ hx₀`. Use `ContDiffAt.contDiffWithinAt ?_` and prove the remaining obligations. Take `⟨b, hbS, hbspan, hbli⟩` from `exists_linearIndependent ℝ S`. Use `haveI : Module.Finite ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := inferInstance`. Use `haveI : Finite b := hbli.finite`.

Use `letI : Fintype b := Fintype.ofFinite b`. Use `set m := Fintype.card b`. Set `e` to `Fintype.equivFin b`. Set `X : Fin m → Matrix (Fin d) (Fin d) (Cinf E)` to `fun i => (e.symm i).1`. Establish `hXS : ∀ i, X i ∈ S` using `fun i => hbS (e.symm i).2`.

Establish `hXli : LinearIndependent ℝ X` using `hbli.comp e.symm e.symm.injective`. Establish `hXspan : Submodule.span ℝ (Set.range X) = ⊤`. Establish `: Set.range X = b`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, rfl⟩`. Conclude with `(e.symm i).2`. Introduce `hx; exact ⟨e ⟨x, hx⟩, by simp [X]⟩`. Rewrite using `[this, hbspan, hS]`. Set `B : Module.Basis (Fin m) ℝ (Matrix (Fin d) (Fin d) (Cinf E))` to `Module.Basis.mk hXli hXspan.ge`.

Establish `hdim : Module.finrank ℝ (Fin m → ℝ) = Module.finrank ℝ (Lie E d)`. Rewrite using `[Module.finrank_fin_fun]`. Conclude with `(Module.finrank_eq_card_basis B).trans (Fintype.card_fin m) |>.symm`. Set `Lin : (Fin m → ℝ) →ₗ[ℝ] Lie E d` to `{ toFun := fun t => toL (Matrix.of x₀ * ∑ i, t i • X i) map_add' := fun s t => by`. Simplify using `only [Pi.add_apply, add_smul, Finset.sum_add_distrib, mul_add]`.

Both sides reduce to the same expression. Use the proof step `map_smul' := fun c t => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, Matrix.mul_smul]`. Use `rfl }`. Establish `hLinj : Function.Injective Lin`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `t ht`. Establish `h1 : Matrix.of x₀ * ∑ i, t i • X i = Matrix.of x₀ * 0`. Rewrite using `[mul_zero]`. Conclude with `ht`.

Establish `h2` using `(show IsUnit (Matrix.of x₀) from hx₀).mul_left_cancel h1`. Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.1 hXli t h2 i`. Set `L : (Fin m → ℝ) ≃L[ℝ] Lie E d` to `(LinearMap.linearEquivOfInjective Lin hLinj hdim).toContinuousLinearEquiv`. Use `set Θ := fun t : Fin m → ℝ => toL (Matrix.of x₀ * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod) with hΘdef`.

Establish `hΘ : ContDiff ℝ ∞ Θ` using `contDiff_prodExp x₀ X`. Establish `hΘ0 : Θ 0 = x₀`. Simplify using `[Θ]`. Establish `hD : HasFDerivAt Θ (L : (Fin m → ℝ) →L[ℝ] Lie E d) 0`. Establish `h` using `((hΘ.differentiable (by simp)) 0).hasFDerivAt`.

Establish `hE : ((L : (Fin m → ℝ) →L[ℝ] Lie E d) : (Fin m → ℝ) →ₗ[ℝ] Lie E d) = ((fderiv ℝ Θ 0 : (Fin m → ℝ) →L[ℝ] Lie E d) : (Fin m → ℝ) →ₗ[ℝ] Lie E d)`. Use `LinearMap.pi_ext fun i c => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Lin (Pi.single i c) = fderiv ℝ Θ 0 (Pi.single i c)`. Rewrite using `[hΘdef, fderiv_prodExp]`. Simplify using `only [Lin, LinearMap.coe_mk, AddHom.coe_mk]`.

Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]`. Simplify using `only [Pi.single_eq_same, Matrix.mul_smul]`. Both sides reduce to the same expression. Rewrite using `[ContinuousLinearMap.coe_injective hE]`. Conclude with `h`.

Establish `hn : (∞ : ℕ∞ω) ≠ 0` using `by simp`. Establish `hΨ` using `hΘ.contDiffAt.to_localInverse hD hn`. Establish `hinv` using `(hΘ.contDiffAt.hasStrictFDerivAt' hD hn).eventually_right_inverse`. Establish `hc : ContDiffAt ℝ ∞ (f ∘ Θ ∘ hΘ.contDiffAt.localInverse hD hn) (Θ 0)` using `(hf m X hXS x₀ hx₀).contDiffAt.comp _ hΨ`. Rewrite `hc`, `hinv` using `[hΘ0]`.

Use `hc.congr_of_eventuallyEq (hinv.mono fun x hx => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Conclude with `congrArg f hx.symm`.
-/
theorem contDiffOn_of_prodExp : ∀ (E : Type) [Field E] [NumberField E] (d : ℕ) (f : GlobalTheory.CuspRep.Lie E d → ℂ)
    (S : Set (Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E))), Submodule.span ℝ S = ⊤ →
    (∀ (k : ℕ) (X : Fin k → Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)), (∀ i, X i ∈ S) →
      ∀ y ∈ GlobalTheory.CuspRep.invSet E d, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        f (GlobalTheory.CuspRep.toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod))) →
    ContDiffOn ℝ ∞ f (GlobalTheory.CuspRep.invSet E d) := by
  intro E _ _ d f S hS hf x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_

  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℝ S
  haveI : Module.Finite ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := inferInstance
  haveI : Finite b := hbli.finite
  letI : Fintype b := Fintype.ofFinite b
  set m := Fintype.card b
  let e := Fintype.equivFin b
  let X : Fin m → Matrix (Fin d) (Fin d) (Cinf E) := fun i => (e.symm i).1
  have hXS : ∀ i, X i ∈ S := fun i => hbS (e.symm i).2
  have hXli : LinearIndependent ℝ X := hbli.comp e.symm e.symm.injective
  have hXspan : Submodule.span ℝ (Set.range X) = ⊤ := by
    have : Set.range X = b := by
      ext x; constructor
      · rintro ⟨i, rfl⟩; exact (e.symm i).2
      · intro hx; exact ⟨e ⟨x, hx⟩, by simp [X]⟩
    rw [this, hbspan, hS]
  let B : Module.Basis (Fin m) ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Module.Basis.mk hXli hXspan.ge
  have hdim : Module.finrank ℝ (Fin m → ℝ) = Module.finrank ℝ (Lie E d) := by
    rw [Module.finrank_fin_fun]
    exact (Module.finrank_eq_card_basis B).trans (Fintype.card_fin m) |>.symm

  let Lin : (Fin m → ℝ) →ₗ[ℝ] Lie E d :=
    { toFun := fun t => toL (Matrix.of x₀ * ∑ i, t i • X i)
      map_add' := fun s t => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, mul_add]; rfl
      map_smul' := fun c t => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, Matrix.mul_smul]; rfl }
  have hLinj : Function.Injective Lin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    have h1 : Matrix.of x₀ * ∑ i, t i • X i = Matrix.of x₀ * 0 := by
      rw [mul_zero]; exact ht
    have h2 := (show IsUnit (Matrix.of x₀) from hx₀).mul_left_cancel h1
    funext i
    exact Fintype.linearIndependent_iff.1 hXli t h2 i
  let L : (Fin m → ℝ) ≃L[ℝ] Lie E d :=
    (LinearMap.linearEquivOfInjective Lin hLinj hdim).toContinuousLinearEquiv
  set Θ := fun t : Fin m → ℝ =>
      toL (Matrix.of x₀ * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod) with hΘdef
  have hΘ : ContDiff ℝ ∞ Θ := contDiff_prodExp x₀ X
  have hΘ0 : Θ 0 = x₀ := by
    simp [Θ]
  have hD : HasFDerivAt Θ (L : (Fin m → ℝ) →L[ℝ] Lie E d) 0 := by
    have h := ((hΘ.differentiable (by simp)) 0).hasFDerivAt
    have hE : ((L : (Fin m → ℝ) →L[ℝ] Lie E d) : (Fin m → ℝ) →ₗ[ℝ] Lie E d) =
        ((fderiv ℝ Θ 0 : (Fin m → ℝ) →L[ℝ] Lie E d) : (Fin m → ℝ) →ₗ[ℝ] Lie E d) := by
      refine LinearMap.pi_ext fun i c => ?_
      change Lin (Pi.single i c) = fderiv ℝ Θ 0 (Pi.single i c)
      rw [hΘdef, fderiv_prodExp]
      simp only [Lin, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
      simp only [Pi.single_eq_same, Matrix.mul_smul]
      rfl
    rw [ContinuousLinearMap.coe_injective hE]
    exact h
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hΨ := hΘ.contDiffAt.to_localInverse hD hn
  have hinv := (hΘ.contDiffAt.hasStrictFDerivAt' hD hn).eventually_right_inverse
  have hc : ContDiffAt ℝ ∞ (f ∘ Θ ∘ hΘ.contDiffAt.localInverse hD hn) (Θ 0) :=
    (hf m X hXS x₀ hx₀).contDiffAt.comp _ hΨ
  rw [hΘ0] at hc hinv
  refine hc.congr_of_eventuallyEq (hinv.mono fun x hx => ?_)
  simp only [Function.comp_apply]
  exact congrArg f hx.symm

end GlobalTheory.SecondKind
