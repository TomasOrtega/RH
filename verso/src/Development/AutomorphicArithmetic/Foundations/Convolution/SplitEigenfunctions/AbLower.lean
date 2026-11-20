import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.IdeleRoots.ClassicalIdeles.ExistsPosBoundsOfIsCompact

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

/- English proof (translation)
Set `f : G1 F → A F × (A F)ᵐᵒᵖ` to `fun p => (p 0 0, MulOpposite.op (p 1 1))`. Apply the tactic sequence `have hf : Continuous f := (M.continuous_entry 0 0).prodMk (MulOpposite.continuous_op.comp (M.continuous_entry 1 1))`. Establish `hS : IsCompact ((Units.embedProduct (A F)) ⁻¹' (f '' Ω))` using `Units.isClosedEmbedding_embedProduct.isCompact_preimage (hΩ.image hf)`. Take `⟨lo, _, hlo, _, hb⟩` from `GroundTheory.BlockD.exists_pos_bounds_of_isCompact hS M.continuous_ab M.ab_pos`. Use `⟨lo, hlo, fun p hp x h0 h1 => (hb x ?_).1⟩` and prove the remaining obligations.

Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Simplify using `[f, Units.embedProduct, h0, h1]`.
-/
private theorem ab_lower {F : Type} [Field F] [NumberField F] {Ω : Set (G1 F)} (hΩ : IsCompact Ω) :
    ∃ lo : ℝ, 0 < lo ∧ ∀ p ∈ Ω, ∀ x : (A F)ˣ, (x : A F) = p 0 0 → ((x⁻¹ : (A F)ˣ) : A F) = p 1 1 → lo ≤ ab x := by
  let f : G1 F → A F × (A F)ᵐᵒᵖ := fun p => (p 0 0, MulOpposite.op (p 1 1))
  have hf : Continuous f :=
    (M.continuous_entry 0 0).prodMk (MulOpposite.continuous_op.comp (M.continuous_entry 1 1))
  have hS : IsCompact ((Units.embedProduct (A F)) ⁻¹' (f '' Ω)) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hΩ.image hf)
  obtain ⟨lo, _, hlo, _, hb⟩ := GroundTheory.BlockD.exists_pos_bounds_of_isCompact hS M.continuous_ab M.ab_pos
  refine ⟨lo, hlo, fun p hp x h0 h1 => (hb x ?_).1⟩
  refine ⟨p, hp, ?_⟩
  simp [f, Units.embedProduct, h0, h1]

/- English proof (translation)
Rewrite using `[← GroundTheory.BlockD.adeleOfParts_posIdele t ht]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Conclude with `(InfinitePlace.Completion.extensionEmbedding w).injective ((h w).trans (GroundTheory.BlockD.extensionEmbedding_posIdele t ht w).symm)`.
-/
private theorem parts_eq {F : Type} [Field F] [NumberField F] {t : ℝ} (ht : 0 < t) (a : InfiniteAdeleRing F)
    (h : ∀ w, InfinitePlace.Completion.extensionEmbedding w (a w) = (t : ℂ)) :
    Formalism.D.adeleOfParts F a 1 = ((GroundTheory.Automorphic.Reduction.posIdele t ht : IdeleGroup F) : AdeleRing (𝓞 F) F) := by
  rw [← GroundTheory.BlockD.adeleOfParts_posIdele t ht]
  congr 1
  funext w
  exact (InfinitePlace.Completion.extensionEmbedding w).injective
    ((h w).trans (GroundTheory.BlockD.extensionEmbedding_posIdele t ht w).symm)

/- English proof (translation)
Introduce `E _ _`. Take `⟨Ω, K, t₀, hΩ, h10, hK, ht₀, H⟩` from `GroundTheory.BlockD.siegelSetsSL2Adelic_holds E`. Take `⟨lo, hlo, hb⟩` from `ab_lower hΩ`. Use `set d : ℕ := Module.finrank ℚ E with hd`. Use `⟨lo * t₀ ^ d, K, by positivity, hK, fun h => ?_⟩` and prove the remaining obligations.

Take `⟨_, ⟨γ, rfl⟩, p, hp, t, ht, a, a', ha, k, hk, heq⟩` from `H h`. Establish `htpos : 0 < t` using `ht₀.trans_le ht`. Use `set z : (A E)ˣ := GroundTheory.Automorphic.Reduction.posIdele t htpos with hz`. Establish `ea : Formalism.D.adeleOfParts E a 1 = (z : A E)` using `parts_eq htpos a fun w => (ha w).2`. Establish `eaa : Formalism.D.adeleOfParts E a 1 * Formalism.D.adeleOfParts E a' 1 = 1`.

Use `Prod.ext (funext fun w => (ha w).1) ?_` and prove the remaining obligations. Use `show (1 : FiniteAdeleRing (𝓞 E) E) * 1 = 1`. Simplify using the standard rewrite rules. Establish `ea' : Formalism.D.adeleOfParts E a' 1 = ((z⁻¹ : (A E)ˣ) : A E)`. Rewrite `eaa` using `[ea]`.

Conclude with `(Units.inv_eq_of_mul_eq_one_right eaa).symm`. Establish `hp10 : p 1 0 = 0` using `h10 p hp`. Establish `hdet : p 0 0 * p 1 1 = 1`. Use `p.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`.

Simplify `this` using `[hp10]`. Set `x : (A E)ˣ` to `⟨p 0 0, p 1 1, hdet, by rw [mul_comm]; exact hdet⟩`. Establish `hx` using `hb p hp x rfl rfl`. Use `⟨γ, p 0 1 * p 0 0, x * z, k, hk, ?_, ?_⟩` and prove the remaining obligations. Use `Subtype.ext ?_` and prove the remaining obligations.

Rewrite using `[M.val_mul, M.val_mul, M.val_mul]`. Use `heq.trans ?_` and prove the remaining obligations. Rewrite using `[ea, ea']`. Use `congr 1`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j`. Simplify using `[nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using `[nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two]`. Take the linear combination `(-(p.1 0 1 * ((z⁻¹ : (A E)ˣ) : A E))) * hdet`. Simplify using `[nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two, hp10]`.

Simplify using `[nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two, hp10, mul_comm]`. Rewrite using `[M.ab_mul]`. Establish `hz' : ab z = t ^ d`. Simplify using `[ab, hz, GroundTheory.Automorphic.Reduction.ideleModule_posIdele, hd]`. Rewrite using `[hz']`.

Establish `: t₀ ^ d ≤ t ^ d` using `pow_le_pow_left₀ ht₀.le ht d`. Conclude with `mul_le_mul hx this (by positivity) (M.ab_pos x).le`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.redE :
    RedE := by
  intro E _ _
  obtain ⟨Ω, K, t₀, hΩ, h10, hK, ht₀, H⟩ := GroundTheory.BlockD.siegelSetsSL2Adelic_holds E
  obtain ⟨lo, hlo, hb⟩ := ab_lower hΩ
  set d : ℕ := Module.finrank ℚ E with hd
  refine ⟨lo * t₀ ^ d, K, by positivity, hK, fun h => ?_⟩
  obtain ⟨_, ⟨γ, rfl⟩, p, hp, t, ht, a, a', ha, k, hk, heq⟩ := H h
  have htpos : 0 < t := ht₀.trans_le ht
  set z : (A E)ˣ := GroundTheory.Automorphic.Reduction.posIdele t htpos with hz
  have ea : Formalism.D.adeleOfParts E a 1 = (z : A E) := parts_eq htpos a fun w => (ha w).2
  have eaa : Formalism.D.adeleOfParts E a 1 * Formalism.D.adeleOfParts E a' 1 = 1 := by
    refine Prod.ext (funext fun w => (ha w).1) ?_
    show (1 : FiniteAdeleRing (𝓞 E) E) * 1 = 1
    simp
  have ea' : Formalism.D.adeleOfParts E a' 1 = ((z⁻¹ : (A E)ˣ) : A E) := by
    rw [ea] at eaa
    exact (Units.inv_eq_of_mul_eq_one_right eaa).symm
  have hp10 : p 1 0 = 0 := h10 p hp
  have hdet : p 0 0 * p 1 1 = 1 := by
    have := p.det_coe
    rw [Matrix.det_fin_two] at this
    simpa [hp10] using this
  let x : (A E)ˣ := ⟨p 0 0, p 1 1, hdet, by rw [mul_comm]; exact hdet⟩
  have hx := hb p hp x rfl rfl
  refine ⟨γ, p 0 1 * p 0 0, x * z, k, hk, ?_, ?_⟩
  · refine Subtype.ext ?_
    rw [M.val_mul, M.val_mul, M.val_mul]
    refine heq.trans ?_
    rw [ea, ea']
    congr 1
    ext i j
    fin_cases i <;> fin_cases j
    · simp [nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-(p.1 0 1 * ((z⁻¹ : (A E)ˣ) : A E))) * hdet
    · simp [nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two, hp10]
    · simp [nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two, hp10, mul_comm]
  · rw [M.ab_mul]
    have hz' : ab z = t ^ d := by
      simp [ab, hz, GroundTheory.Automorphic.Reduction.ideleModule_posIdele, hd]
    rw [hz']
    have : t₀ ^ d ≤ t ^ d := pow_le_pow_left₀ ht₀.le ht d
    exact mul_le_mul hx this (by positivity) (M.ab_pos x).le
