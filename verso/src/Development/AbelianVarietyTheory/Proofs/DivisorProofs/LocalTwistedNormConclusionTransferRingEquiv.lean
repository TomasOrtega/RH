import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.FinClsLoc

/- English proof (translation)
Introduce `p _ G K K' _ _ _ _ e Y a b b' ⟨u, z, hc, h⟩`. Establish `hq : ∀ q : ℚ, e (algebraMap ℚ K q) = algebraMap ℚ K' q` using `fun q => RingHom.congr_fun (Subsingleton.elim ((e : K →+* K').comp (algebraMap ℚ K)) (algebraMap ℚ K')) q`. Set `e' : K ≃ₐ[ℚ] K'` to `AlgEquiv.ofRingEquiv (f := e) hq`. Set `T : K ⊗[ℚ] G.C ≃ₐ[ℚ] K' ⊗[ℚ] G.C` to `Algebra.TensorProduct.congr e' AlgEquiv.refl`. Establish `hT1 : ∀ c : G.C, T (inC G K c) = inC G K' c`.

Introduce `c`. Simplify using `[T, inC, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]`. Establish `hT2 : ∀ x : K, T (algebraMap K (K ⊗[ℚ] G.C) x) = algebraMap K' (K' ⊗[ℚ] G.C) (e x)`. Introduce `x`. Simplify using `[T, e', Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]`.

Establish `hT3 : ∀ w : K ⊗[ℚ] G.C, (starT G.star K' (T w)).unop = T (starT G.star K w).unop`. Introduce `w`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r x`.

Establish `: T (r ⊗ₜ x) = e r ⊗ₜ x`. Simplify using `[T, e', Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]`. Rewrite using `[this, starT_tmul, starT_tmul]`. Simplify using `[T, e', Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]`. Consider the case `add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]`.

Use `⟨Units.map (e : K →* K') u, Units.map (T : K ⊗[ℚ] G.C →* K' ⊗[ℚ] G.C) z, ?_, ?_⟩` and prove the remaining obligations. Use `hc.map T` as an intermediate fact. Rewrite `this` using `[hT1]`. Conclude with `this`. Establish `h'` using `congrArg T h`.

Rewrite `h'` using `[hT1, map_mul, hT2, map_mul, map_mul, map_mul, hT1, hT1, ← hT3]`. Simplify using `using h'`.
-/
theorem localTransfer : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K K' : Type) [Field K] [Field K'] [Algebra ℚ K] [Algebra ℚ K'],
    (K ≃+* K') → ∀ (Y a b b' : G.C),
    (∃ (u : Kˣ) (z : (K ⊗[ℚ] G.C)ˣ), Commute (z : K ⊗[ℚ] G.C) (inC G K Y) ∧
      inC G K a = algebraMap K (K ⊗[ℚ] G.C) (u : K) * ((z : K ⊗[ℚ] G.C) * inC G K b *
        (starT G.star K (z : K ⊗[ℚ] G.C)).unop * inC G K b')) →
    ∃ (u : K'ˣ) (z : (K' ⊗[ℚ] G.C)ˣ), Commute (z : K' ⊗[ℚ] G.C) (inC G K' Y) ∧
      inC G K' a = algebraMap K' (K' ⊗[ℚ] G.C) (u : K') * ((z : K' ⊗[ℚ] G.C) * inC G K' b *
        (starT G.star K' (z : K' ⊗[ℚ] G.C)).unop * inC G K' b') := by
  intro p _ G K K' _ _ _ _ e Y a b b' ⟨u, z, hc, h⟩
  have hq : ∀ q : ℚ, e (algebraMap ℚ K q) = algebraMap ℚ K' q := fun q =>
    RingHom.congr_fun (Subsingleton.elim ((e : K →+* K').comp (algebraMap ℚ K)) (algebraMap ℚ K')) q
  let e' : K ≃ₐ[ℚ] K' := AlgEquiv.ofRingEquiv (f := e) hq
  let T : K ⊗[ℚ] G.C ≃ₐ[ℚ] K' ⊗[ℚ] G.C := Algebra.TensorProduct.congr e' AlgEquiv.refl
  have hT1 : ∀ c : G.C, T (inC G K c) = inC G K' c := by
    intro c
    simp [T, inC, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  have hT2 : ∀ x : K, T (algebraMap K (K ⊗[ℚ] G.C) x) = algebraMap K' (K' ⊗[ℚ] G.C) (e x) := by
    intro x
    simp [T, e', Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
  have hT3 : ∀ w : K ⊗[ℚ] G.C, (starT G.star K' (T w)).unop = T (starT G.star K w).unop := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      have : T (r ⊗ₜ x) = e r ⊗ₜ x := by
        simp [T, e', Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      rw [this, starT_tmul, starT_tmul]
      simp [T, e', Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]
  refine ⟨Units.map (e : K →* K') u, Units.map (T : K ⊗[ℚ] G.C →* K' ⊗[ℚ] G.C) z, ?_, ?_⟩
  · have := hc.map T
    rw [hT1] at this
    exact this
  · have h' := congrArg T h
    rw [hT1, map_mul, hT2, map_mul, map_mul, map_mul, hT1, hT1, ← hT3] at h'
    simpa using h'

end GlobalTheory.FinClsLoc
