import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.TrueGeo
namespace GlobalTheory.TrueGeoModel
variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Set `K` to `v.adicCompletion F`. Establish `h1 : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ < 1` using `(FinitePlace.norm_lt_one_iff_mem F v a).2 ha`. Establish `h0 : FinitePlace.embedding v (algebraMap (𝓞 F) F a) ≠ 0`. Simplify using `using ha0`.

Use `letI : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne ⟨_, h0, h1.ne⟩`. Set `L` to `AlgebraicClosure K`. Use `letI : Algebra F L := ((algebraMap K L).comp (FinitePlace.embedding v)).toAlgebra`. Set `j : AlgebraicClosure F →ₐ[F] L` to `IsAlgClosed.lift`. Set `N` to `spectralMulAlgNorm K L`.

Set `w : AbsoluteValue (AlgebraicClosure F) ℝ` to `(MulRingNorm.mulRingNormEquivAbsoluteValue N.toMulRingNorm).comp (f := j.toRingHom) j.injective`. Establish `hw (x) : w x = spectralNorm K L (j x)` using `rfl`. Establish `hn (x y) : w (x + y) ≤ max (w x) (w y)`. Rewrite using `[hw, hw, hw, map_add]`. Conclude with `isNonarchimedean_spectralNorm _ _`.

Use `⟨⟨w, fun x => ?_, ⟨⟨⟨⟨⟨{x | w x ≤ 1}, ?_⟩, by simp⟩, ?_, by simp⟩, ?_⟩, ?_⟩, fun _ => Iff.rfl⟩⟩` and prove the remaining obligations. Rewrite using `[hw, j.commutes, ← FinitePlace.norm_embedding]`. Conclude with `spectralNorm_extends _`. Introduce `x y hx hy`. Simplify using `only [Set.mem_setOf_eq, map_mul] at *`.

Conclude with `mul_le_one₀ hx (w.nonneg _) hy`. Introduce `x y hx hy`. Conclude with `(hn x y).trans (max_le hx hy)`. Introduce `x hx`. Simplify using `using hx`.

Introduce `x`. Break down `le_total (w x) 1 with h | h` into its components or cases. Conclude with `.inl h`. Use `.inr ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `w x⁻¹ ≤ 1`.

Rewrite using `[map_inv₀]`. Conclude with `inv_le_one_of_one_le₀ h`.
-/
theorem nonempty_ext (v : HeightOneSpectrum (𝓞 F)) : Nonempty (Ext v) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let K := v.adicCompletion F
  have h1 : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ < 1 := (FinitePlace.norm_lt_one_iff_mem F v a).2 ha
  have h0 : FinitePlace.embedding v (algebraMap (𝓞 F) F a) ≠ 0 := by
    simpa using ha0
  letI : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne ⟨_, h0, h1.ne⟩
  let L := AlgebraicClosure K
  letI : Algebra F L := ((algebraMap K L).comp (FinitePlace.embedding v)).toAlgebra
  let j : AlgebraicClosure F →ₐ[F] L := IsAlgClosed.lift
  let N := spectralMulAlgNorm K L
  let w : AbsoluteValue (AlgebraicClosure F) ℝ :=
    (MulRingNorm.mulRingNormEquivAbsoluteValue N.toMulRingNorm).comp (f := j.toRingHom) j.injective
  have hw (x) : w x = spectralNorm K L (j x) := rfl
  have hn (x y) : w (x + y) ≤ max (w x) (w y) := by
    rw [hw, hw, hw, map_add]; exact isNonarchimedean_spectralNorm _ _
  refine ⟨⟨w, fun x => ?_, ⟨⟨⟨⟨⟨{x | w x ≤ 1}, ?_⟩, by simp⟩, ?_, by simp⟩, ?_⟩, ?_⟩, fun _ => Iff.rfl⟩⟩
  · rw [hw, j.commutes, ← FinitePlace.norm_embedding]
    exact spectralNorm_extends _
  · intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul] at *
    exact mul_le_one₀ hx (w.nonneg _) hy
  · intro x y hx hy
    exact (hn x y).trans (max_le hx hy)
  · intro x hx
    simpa using hx
  · intro x
    rcases le_total (w x) 1 with h | h
    · exact .inl h
    · refine .inr ?_
      change w x⁻¹ ≤ 1
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ h

end GlobalTheory.TrueGeoModel
