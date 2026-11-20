import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC

open UpperTheory.V.Af UpperTheory.GalN.V

/- English proof (translation)
Rewrite `h`, the goal using `[Polynomial.IsRoot, Matrix.eval_charpoly]`. Establish `key : (Matrix.scalar (Fin n)) α - c • M = c • ((Matrix.scalar (Fin n)) (c⁻¹ * α) - M)`. Rewrite using `[smul_sub, Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]`. Use `congr 2`. Use extensionality with `i`.

Simplify using `[mul_inv_cancel_left₀ hc]`. Rewrite `h` using `[key, Matrix.det_smul]`. Break down `mul_eq_zero.mp h with h1 | h1` into its components or cases. Conclude with `absurd (pow_eq_zero_iff'.mp h1).1 hc`. Conclude with `h1`.
-/
private theorem root_of_smul {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (c : K) (hc : c ≠ 0) (α : K)
    (h : (c • M).charpoly.IsRoot α) : M.charpoly.IsRoot (c⁻¹ * α) := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at h ⊢
  have key : (Matrix.scalar (Fin n)) α - c • M = c • ((Matrix.scalar (Fin n)) (c⁻¹ * α) - M) := by
    rw [smul_sub, Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
    congr 2
    ext i
    simp [mul_inv_cancel_left₀ hc]
  rw [key, Matrix.det_smul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (pow_eq_zero_iff'.mp h1).1 hc
  · exact h1

/- English proof (translation)
Introduce `F Ω _ _ _ _ l _ n ι r δ`. Establish `hc : ∀ s, ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l) ≠ 0` using `fun s => Units.ne_zero _`. Establish `hroot : ∀ s α, (↑((tw r δ) s) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.IsRoot α → (↑(r s) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.IsRoot (((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qb …`. Introduce `s α h`. Rewrite `h` using `[tw_val]`.

Conclude with `root_of_smul _ _ (hc s) α h`. Establish `hnorm : ∀ s α, ‖ι α‖ = ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖ * ‖ι (((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)⁻¹ * α)‖`. Introduce `s α`. Rewrite using `[← norm_mul, ← map_mul, mul_inv_cancel_left₀ (hc s)]`. Establish `hpos : ∀ s, 0 < ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖`.

Introduce `s`. Conclude with `norm_pos_iff.mpr ((map_ne_zero ι).mpr (hc s))`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Introduce `w hw A hA s hs α β hα hβ heq`. Apply `h w hw A hA s hs _ _ (hroot s α hα) (hroot s β hβ)` to reduce the goal to its premises.

Establish `hp` using `hpos s`. Rewrite `heq` using `[hnorm s α, hnorm s β, mul_pow, mul_pow]`. Establish `hp2 : 0 < ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖ ^ 2` using `by positivity`. Use `heq` as an intermediate fact. Rewrite `this` using `[mul_left_comm]`.

Conclude with `mul_left_cancel₀ hp2.ne' this`. Introduce `w hw A hA s hs α β hα hβ`. Establish `key` using `h w hw A hA s hs _ _ (hroot s α hα) (hroot s β hβ)`. Establish `hp` using `hpos s`. Rewrite using `[hnorm s α, hnorm s β, mul_left_comm]`.

Conclude with `mul_lt_mul_of_pos_left key hp`.
-/
theorem UpperTheory.V.Z.Sym.Unl.twOk :
    UpperTheory.V.Z.Sym.Unl.TwOk := by
  intro F Ω _ _ _ _ l _ n ι r δ
  have hc : ∀ s, ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l) ≠ 0 := fun s => Units.ne_zero _
  have hroot : ∀ s α, (↑((tw r δ) s) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.IsRoot α →
      (↑(r s) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.IsRoot (((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)⁻¹ * α) := by
    intro s α h
    rw [tw_val] at h
    exact root_of_smul _ _ (hc s) α h
  have hnorm : ∀ s α, ‖ι α‖ = ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖ *
      ‖ι (((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)⁻¹ * α)‖ := by
    intro s α
    rw [← norm_mul, ← map_mul, mul_inv_cancel_left₀ (hc s)]
  have hpos : ∀ s, 0 < ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖ := by
    intro s
    exact norm_pos_iff.mpr ((map_ne_zero ι).mpr (hc s))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · intro w hw A hA s hs α β hα hβ heq
    apply h w hw A hA s hs _ _ (hroot s α hα) (hroot s β hβ)
    have hp := hpos s
    rw [hnorm s α, hnorm s β, mul_pow, mul_pow] at heq
    have hp2 : 0 < ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖ ^ 2 := by positivity
    have := heq
    rw [mul_left_comm] at this
    exact mul_left_cancel₀ hp2.ne' this
  · intro w hw A hA s hs α β hα hβ
    have key := h w hw A hA s hs _ _ (hroot s α hα) (hroot s β hβ)
    have hp := hpos s
    rw [hnorm s α, hnorm s β, mul_left_comm]
    exact mul_lt_mul_of_pos_left key hp
