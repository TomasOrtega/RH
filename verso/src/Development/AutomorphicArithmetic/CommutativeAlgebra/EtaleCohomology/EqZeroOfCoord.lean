import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VInduction

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace F V`. Apply `(TensorProduct.equivFinsuppOfBasisLeft b).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use extensionality with `i`. Establish `key : ∀ w : V ⊗[F] C, (TensorProduct.equivFinsuppOfBasisLeft b w) i = TensorProduct.lid F C (LinearMap.rTensor C (b.coord i) w)`.

Introduce `w`. Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp`. Consider the case `add x y hx hy => simp [hx, hy]`.

Rewrite using `[key, h]`. Both sides reduce to the same expression.
-/
private theorem UpperTheory.Ru.crystallineComparison.eq_zero_of_coord {F V C : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup C] [Module F C] (w : V ⊗[F] C)
    (h : ∀ f : Module.Dual F V, TensorProduct.lid F C (LinearMap.rTensor C f w) = 0) : w = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F V
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  ext i
  have key : ∀ w : V ⊗[F] C, (TensorProduct.equivFinsuppOfBasisLeft b w) i =
      TensorProduct.lid F C (LinearMap.rTensor C (b.coord i) w) := by
    intro w
    induction w with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp [hx, hy]
  rw [key, h]
  rfl

/- English proof (translation)
Introduce `l _ K B₀ ι hι hc hq G Amp hF hE hL e e' hB hP hcomp M hM j κ _ v c u hu`. Take `⟨a⟩` from `hL.ch M hM`. Establish `h0 : (per l K).t ^ u • ∑ k, (show (per l K).A from c k) • e'.e a j (v k) = 0`. Express the relevant statement in the definitionally equal form `((UpperTheory.Ru.crystallineComparison.tA l ^ u • ∑ k, c k • (show (M.MS j).lim from e'.e a j (v k)) : (M.MS j).lim)) = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `n`. Use `hu n` as an intermediate fact. Simplify using `only [UpperTheory.Ru.crystallineComparison.evE] at this`. Simplify `this` using `[Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, hcomp]`. Establish `h1` using `UpperTheory.Ru.crystallineComparison.injAbs l K (per l K) G (dat Amp) hF hE hL e' hB hP M hM a j κ v c u h0`.

Apply `UpperTheory.Ru.crystallineComparison.eq_zero_of_coord` to reduce the goal to its premises. Introduce `f`. Apply `hι` to reduce the goal to its premises. Establish `h2` using `h1 f`. Simplify using `only [UpperTheory.Ru.crystallineComparison.vec, map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, pow_zero, mul_one, map_zero]`.

Simplify using `only [Algebra.smul_def, map_mul, hq, hc]`. Conclude with `h2`.
-/
theorem UpperTheory.Ru.crystallineComparison.injOf :
    UpperTheory.Ru.crystallineComparison.InjOf := by
  intro l _ K B₀ ι hι hc hq G Amp hF hE hL e e' hB hP hcomp M hM j κ _ v c u hu
  obtain ⟨a⟩ := hL.ch M hM
  have h0 : (per l K).t ^ u • ∑ k, (show (per l K).A from c k) • e'.e a j (v k) = 0 := by
    change ((UpperTheory.Ru.crystallineComparison.tA l ^ u • ∑ k, c k • (show (M.MS j).lim from e'.e a j (v k)) : (M.MS j).lim)) = 0
    apply Subtype.ext
    funext n
    have := hu n
    simp only [UpperTheory.Ru.crystallineComparison.evE] at this
    simpa [Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, hcomp] using this
  have h1 := UpperTheory.Ru.crystallineComparison.injAbs l K (per l K) G (dat Amp) hF hE hL e' hB hP M hM a j κ v c u h0
  apply UpperTheory.Ru.crystallineComparison.eq_zero_of_coord
  intro f
  apply hι
  have h2 := h1 f
  simp only [UpperTheory.Ru.crystallineComparison.vec, map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, pow_zero, mul_one, map_zero]
  simp only [Algebra.smul_def, map_mul, hq, hc]
  exact h2
