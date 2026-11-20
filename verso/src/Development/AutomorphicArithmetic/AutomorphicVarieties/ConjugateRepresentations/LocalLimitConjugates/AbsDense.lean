import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

/- English proof (translation)
Introduce `G H _ _ _ _ R D A hD hR hA hsym hirr s hs w hw`. Use `set u : D → H := fun v => (A v : H) + (Complex.I * s) • (v : H) with hu`. Establish `hinner : ∀ (g : G) (x y : H), inner ℂ (R g x) (R g y) = inner ℂ x y` using `fun g x y => (LinearIsometry.mk (R g).toLinearMap (hR g)).inner_map_map x y`. Establish `hinv : ∀ (g : G) (y : H), R g (R g⁻¹ y) = y`. Introduce `g y`.

Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]`. Set `W : Submodule ℂ H` to `{ carrier := {x | ∀ v : D, inner ℂ x (u v) = 0} add_mem' := by`. Introduce `a b ha hb v`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[inner_add_left, ha v, hb v, add_zero]`.

Use the proof step `zero_mem' := by`. Introduce `v`. Simplify using `only [Set.mem_setOf_eq, inner_zero_left]`. Use the proof step `smul_mem' := by`. Introduce `c a ha v`.

Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Rewrite using `[inner_smul_left, ha v, mul_zero] }`. Establish `hW : GlobalTheory.AutomorphicL2Unitary.IsSubrep R W`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hset : (W : Set H) = ⋂ v : D, {x | inner ℂ x (u v) = 0}`.

Use extensionality with `x`. Simplify using `[W]`. Rewrite using `[hset]`. Conclude with `isClosed_iInter fun v => isClosed_eq (continuous_id.inner continuous_const) continuous_const`. Introduce `g x hx v show inner ℂ (R g x) (u v) = 0`.

Establish `key : R g⁻¹ (u v) = u ⟨R g⁻¹ v, hD g⁻¹ v v.2⟩`. Simplify using `only [hu, map_add, map_smul]`. Rewrite using `[hA g⁻¹ v]`. Rewrite using `[← hinv g (u v), hinner, key]`. Conclude with `hx _`.

Establish `hWD : W ⊓ D = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Take `⟨hxW, hxD⟩` from `Submodule.mem_inf.mp hx`. Establish `h0 : inner ℂ x (u ⟨x, hxD⟩) = 0` using `hxW ⟨x, hxD⟩`.

Establish `hre : (inner ℂ x (A ⟨x, hxD⟩ : H)).im = 0`. Establish `hs'` using `hsym ⟨x, hxD⟩ ⟨x, hxD⟩`. Rewrite `hs'` using `[← inner_conj_symm]`. Conclude with `Complex.conj_eq_iff_im.mp hs'`. Simplify using `only [hu] at h0`.

Rewrite `h0` using `[inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K]`. Establish `him` using `congrArg Complex.im h0`. Simplify using `[hre, hs] at him`. Rewrite `him` using `[← Complex.ofReal_pow, Complex.ofReal_re]`. Rewrite using `[Submodule.mem_bot]`.

Conclude with `norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp him)`. Establish `hwW : w ∈ W` using `hw`. Rewrite `hwW` using `[hirr W hW hWD]`. Conclude with `(Submodule.mem_bot ℂ).mp hwW`.
-/
theorem UpperTheory.V.Cj.H.absDense :
    UpperTheory.V.Cj.H.AbsDense := by
  intro G H _ _ _ _ R D A hD hR hA hsym hirr s hs w hw
  set u : D → H := fun v => (A v : H) + (Complex.I * s) • (v : H) with hu
  have hinner : ∀ (g : G) (x y : H), inner ℂ (R g x) (R g y) = inner ℂ x y := fun g x y =>
    (LinearIsometry.mk (R g).toLinearMap (hR g)).inner_map_map x y
  have hinv : ∀ (g : G) (y : H), R g (R g⁻¹ y) = y := by
    intro g y
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  let W : Submodule ℂ H :=
    { carrier := {x | ∀ v : D, inner ℂ x (u v) = 0}
      add_mem' := by
        intro a b ha hb v
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [inner_add_left, ha v, hb v, add_zero]
      zero_mem' := by
        intro v
        simp only [Set.mem_setOf_eq, inner_zero_left]
      smul_mem' := by
        intro c a ha v
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [inner_smul_left, ha v, mul_zero] }
  have hW : GlobalTheory.AutomorphicL2Unitary.IsSubrep R W := by
    refine ⟨?_, ?_⟩
    · have hset : (W : Set H) = ⋂ v : D, {x | inner ℂ x (u v) = 0} := by
        ext x
        simp [W]
      rw [hset]
      exact isClosed_iInter fun v => isClosed_eq (continuous_id.inner continuous_const) continuous_const
    · intro g x hx v
      show inner ℂ (R g x) (u v) = 0
      have key : R g⁻¹ (u v) = u ⟨R g⁻¹ v, hD g⁻¹ v v.2⟩ := by
        simp only [hu, map_add, map_smul]
        rw [hA g⁻¹ v]
      rw [← hinv g (u v), hinner, key]
      exact hx _
  have hWD : W ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxD⟩ := Submodule.mem_inf.mp hx
    have h0 : inner ℂ x (u ⟨x, hxD⟩) = 0 := hxW ⟨x, hxD⟩
    have hre : (inner ℂ x (A ⟨x, hxD⟩ : H)).im = 0 := by
      have hs' := hsym ⟨x, hxD⟩ ⟨x, hxD⟩
      rw [← inner_conj_symm] at hs'
      exact Complex.conj_eq_iff_im.mp hs'
    simp only [hu] at h0
    rw [inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at h0
    have him := congrArg Complex.im h0
    simp [hre, hs] at him
    rw [← Complex.ofReal_pow, Complex.ofReal_re] at him
    rw [Submodule.mem_bot]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp him)
  have hwW : w ∈ W := hw
  rw [hirr W hW hWD] at hwW
  exact (Submodule.mem_bot ℂ).mp hwW
