import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Ar.Lines

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gramMat_eq_gram {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (σ : L →+* ℂ) {i : ℕ} (f : Fin i → B.carrier) :
    gramMat B σ f = Matrix.gram ℂ (fun a => fibreVec B.metric σ (f a)) := by
  rfl

/- English proof (translation)
Rewrite using `[IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]`. Introduce `z hz`. Take `⟨⟨r, hr⟩, hrz⟩` from `(Submodule.mem_torsion_iff z).mp hz`. Rewrite using `[Submodule.mem_bot]`. Establish `hr0 : r ≠ 0` using `nonZeroDivisors.ne_zero hr`.

Establish `hrL : (r : L) ≠ 0`. Introduce `h`. Apply `hr0` to reduce the goal to its premises. Use `first`. Consider the case `exact RingOfIntegers.coe_eq_zero_iff.mp h`.

Consider the case `exact_mod_cast h`. Establish `hσ : σ (r : L) ≠ 0` using `(map_ne_zero σ).mpr hrL`. Express the relevant statement in the definitionally equal form `r • z = 0 at hrz`. Rewrite `hrz` using `[ComplexAt.smul_def]`. Establish `h2` using `congrArg (ComplexAt.ofComplex σ).symm hrz`.

Rewrite `h2` using `[map_mul, AlgEquiv.symm_apply_apply, map_zero]`. Break down `mul_eq_zero.mp h2 with h | h` into its components or cases. Conclude with `absurd h hσ`. Conclude with `(ComplexAt.ofComplex σ).symm.injective (h.trans (map_zero _).symm)`.
-/
private theorem flat_complex_at {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ) :
    Module.Flat (𝓞 L) (ComplexAt σ) := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  intro z hz
  obtain ⟨⟨r, hr⟩, hrz⟩ := (Submodule.mem_torsion_iff z).mp hz
  rw [Submodule.mem_bot]
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  have hrL : (r : L) ≠ 0 := by
    intro h
    apply hr0
    first
      | exact RingOfIntegers.coe_eq_zero_iff.mp h
      | exact_mod_cast h
  have hσ : σ (r : L) ≠ 0 := (map_ne_zero σ).mpr hrL
  change r • z = 0 at hrz
  rw [ComplexAt.smul_def] at hrz
  have h2 := congrArg (ComplexAt.ofComplex σ).symm hrz
  rw [map_mul, AlgEquiv.symm_apply_apply, map_zero] at h2
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h hσ
  · exact (ComplexAt.ofComplex σ).symm.injective (h.trans (map_zero _).symm)

/- English proof (translation)
Use `haveI := flat_complex_at σ`. Establish `hinj` using `Module.Flat.lTensor_preserves_injective_linearMap (M := ComplexAt σ) (Finsupp.linearCombination (𝓞 L) f) hf`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg a`. Establish `hterm : ∀ b, g b • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f b : Fibre σ B.carrier) = (ComplexAt.ofComplex σ (g b)) ⊗ₜ[𝓞 L] f b`.

Introduce `b`. Rewrite using `[TensorProduct.smul_tmul', ComplexAt.complex_smul_def, mul_one]`. Simplify using `only [hterm] at hg`. Use `set T : ComplexAt σ ⊗[𝓞 L] (Fin i →₀ 𝓞 L) := ∑ b, (ComplexAt.ofComplex σ (g b)) ⊗ₜ[𝓞 L] Finsupp.single b (1 : 𝓞 L) with hT`. Establish `hT0 : LinearMap.lTensor (ComplexAt σ) (Finsupp.linearCombination (𝓞 L) f) T = 0`.

Rewrite using `[hT, map_sum]`. Simplify using `only [LinearMap.lTensor_tmul, Finsupp.linearCombination_single, one_smul]`. Conclude with `hg`. Establish `hT1 : T = 0` using `hinj (hT0.trans (map_zero _).symm)`. Establish `h3` using `congrArg (fun t => TensorProduct.rid (𝓞 L) (ComplexAt σ) (LinearMap.lTensor (ComplexAt σ) (Finsupp.lapply a) t)) hT1`.

Simplify using `only [hT, map_sum, LinearMap.lTensor_tmul, Finsupp.lapply_apply, TensorProduct.rid_tmul, Finsupp.single_apply, map_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h3`. Conclude with `(ComplexAt.ofComplex σ).injective (h3.trans (map_zero _).symm)`.
-/
private theorem linear_independent_one_tmul {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (σ : L →+* ℂ) {i : ℕ} (f : Fin i → B.carrier) (hf : LinearIndependent (𝓞 L) f) :
    LinearIndependent ℂ (fun a => ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f a : Fibre σ B.carrier)) := by
  haveI := flat_complex_at σ
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := ComplexAt σ)
    (Finsupp.linearCombination (𝓞 L) f) hf
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have hterm : ∀ b, g b • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f b : Fibre σ B.carrier) =
      (ComplexAt.ofComplex σ (g b)) ⊗ₜ[𝓞 L] f b := by
    intro b
    rw [TensorProduct.smul_tmul', ComplexAt.complex_smul_def, mul_one]
  simp only [hterm] at hg
  set T : ComplexAt σ ⊗[𝓞 L] (Fin i →₀ 𝓞 L) :=
    ∑ b, (ComplexAt.ofComplex σ (g b)) ⊗ₜ[𝓞 L] Finsupp.single b (1 : 𝓞 L) with hT
  have hT0 : LinearMap.lTensor (ComplexAt σ) (Finsupp.linearCombination (𝓞 L) f) T = 0 := by
    rw [hT, map_sum]
    simp only [LinearMap.lTensor_tmul, Finsupp.linearCombination_single, one_smul]
    exact hg
  have hT1 : T = 0 := hinj (hT0.trans (map_zero _).symm)
  have h3 := congrArg (fun t => TensorProduct.rid (𝓞 L) (ComplexAt σ)
    (LinearMap.lTensor (ComplexAt σ) (Finsupp.lapply a) t)) hT1
  simp only [hT, map_sum, LinearMap.lTensor_tmul, Finsupp.lapply_apply, TensorProduct.rid_tmul,
    Finsupp.single_apply, map_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h3
  exact (ComplexAt.ofComplex σ).injective (h3.trans (map_zero _).symm)

/- English proof (translation)
Introduce `L _ _ B i f hf`. Use `⟨fun σ => ?_, fun σ => ?_⟩` and prove the remaining obligations. Rewrite using `[gramMat_eq_gram]`. Use `Matrix.posDef_gram_iff_linearIndependent.mpr ?_` and prove the remaining obligations. Conclude with `linear_independent_one_tmul B σ f hf`.

Use extensionality with `a b`. Establish `hc : ∀ e : B.carrier, conjFS B.metric σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) = (1 : ComplexAt (ComplexEmbedding.conjugate σ)) ⊗ₜ[𝓞 L] e`. Introduce `e`. Use `show conjMap σ B.carrier ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) = _`. Rewrite using `[conjMap_tmul, map_one]`.

Establish `h2` using `conjFS_inner B.metric σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f a) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f b)`. Rewrite `h2` using `[hc, hc]`. Simplify using `only [gramMat, Matrix.of_apply, Matrix.map_apply]`. Conclude with `h2`.
-/
theorem gramMat_posDef_and_conj : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (i : ℕ) (f : Fin i → B.carrier), LinearIndependent (𝓞 L) f →
    (∀ σ, (gramMat B σ f).PosDef) ∧
      ∀ σ, gramMat B (ComplexEmbedding.conjugate σ) f = (gramMat B σ f).map (starRingEnd ℂ) := by
  intro L _ _ B i f hf
  refine ⟨fun σ => ?_, fun σ => ?_⟩
  · rw [gramMat_eq_gram]
    refine Matrix.posDef_gram_iff_linearIndependent.mpr ?_
    exact linear_independent_one_tmul B σ f hf
  · ext a b
    have hc : ∀ e : B.carrier, conjFS B.metric σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) =
        (1 : ComplexAt (ComplexEmbedding.conjugate σ)) ⊗ₜ[𝓞 L] e := by
      intro e
      show conjMap σ B.carrier ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) = _
      rw [conjMap_tmul, map_one]
    have h2 := conjFS_inner B.metric σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f a) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f b)
    rw [hc, hc] at h2
    simp only [gramMat, Matrix.of_apply, Matrix.map_apply]
    exact h2

end GlobalTheory.CompanionTheory.Ar.Lines
