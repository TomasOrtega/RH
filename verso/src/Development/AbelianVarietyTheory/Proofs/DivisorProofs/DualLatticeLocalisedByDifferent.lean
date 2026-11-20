import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer

noncomputable section

namespace GlobalTheory.TraceSelfDualAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

/- English proof (translation)
Establish `hs0 : (s : F) ≠ 0`. Introduce `h0`. Conclude with `hs (by rw [show s = 0 from Subtype.ext h0]; exact zero_mem _)`. Establish `hv : v.valuation F (s : F) = 1`. Conclude with `(v.valuation_of_algebraMap (K := F) s).trans (HeightOneSpectrum.intValuation_eq_one_iff.2 hs)`.

Establish `hinv : algebraMap F (Fv F v) (s : F)⁻¹ ∈ v.adicCompletionIntegers F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Use `le_of_eq ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `v.valuation F (s : F)⁻¹ = 1`. Rewrite using `[map_inv₀, hv, inv_one]`.

Introduce `y hy`. Use `latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _) (fun _ _ => add_mem) (fun _ => neg_mem) hy` and prove the remaining obligations. Establish `h2` using `tmul_mem_latLoc (mul_mem hinv ha) (h x hx)`. Use `h2 using 2 with i` and compare the differences between its conclusion and the goal. Rewrite using `[Pi.smul_apply, algebraMap_smul, ← TensorProduct.smul_tmul, ← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hs0, one_smul]`.
-/
theorem latLoc_le_of_smul_mem {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (s : 𝓞 F) (hs : s ∉ v.asIdeal)
    (L L' : Submodule (𝓞 E) (Fin n → E)) (h : ∀ y ∈ L, algebraMap F E (s : F) • y ∈ L') :
    latLoc F L v ≤ latLoc F L' v := by
  have hs0 : (s : F) ≠ 0 := by
    intro h0
    exact hs (by rw [show s = 0 from Subtype.ext h0]; exact zero_mem _)
  have hv : v.valuation F (s : F) = 1 := by
    exact (v.valuation_of_algebraMap (K := F) s).trans (HeightOneSpectrum.intValuation_eq_one_iff.2 hs)
  have hinv : algebraMap F (Fv F v) (s : F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    refine le_of_eq ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans ?_)
    change v.valuation F (s : F)⁻¹ = 1
    rw [map_inv₀, hv, inv_one]
  intro y hy
  refine latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  have h2 := tmul_mem_latLoc (mul_mem hinv ha) (h x hx)
  convert h2 using 2 with i
  rw [Pi.smul_apply, algebraMap_smul, ← TensorProduct.smul_tmul, ← Algebra.smul_def, smul_smul,
    mul_inv_cancel₀ hs0, one_smul]

/- English proof (translation)
Rewrite using `[← GlobalTheory.HermSelfDualLoc.hE_transpose]`. Simplify using `only [hE, Formalism.UG.hform, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hE_smul_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (δ : E) (x y : Fin n → E) :
    hE σ (δ • Jᵀ) x y = δ * form σ J y x := by
  rw [← GlobalTheory.HermSelfDualLoc.hE_transpose]
  simp only [hE, Formalism.UG.hform, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Simplify using `[form, smul_dotProduct]`.
-/
theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    form σ J (c • y) x = c * form σ J y x := by
  simp [form, smul_dotProduct]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J L hJ0 hL hd v δ s hδ hs ha hb`. Establish `hJ : (δ • Jᵀ).det ≠ 0`. Rewrite using `[Matrix.det_smul, Matrix.det_transpose]`. Conclude with `mul_ne_zero (pow_ne_zero _ hδ) hJ0`. Establish `h1 : ∀ y ∈ L, algebraMap F E ((1 : 𝓞 F) : F) • y ∈ GlobalTheory.AdelicU.SelfDual.dualGlob σ (δ • Jᵀ) L`.

Introduce `y hy`. Establish `e : algebraMap F E ((1 : 𝓞 F) : F) • y = y` using `by simp`. Rewrite using `[e]`. Introduce `x hx`. Rewrite using `[hE_smul_transpose, ← GlobalTheory.HermSelfDualLoc.isIntegral_iff_mem_range]`.

Conclude with `ha _ ((hd y).1 hy x hx)`. Establish `h2 : ∀ y ∈ GlobalTheory.AdelicU.SelfDual.dualGlob σ (δ • Jᵀ) L, algebraMap F E (s : F) • y ∈ L`. Introduce `y hy`. Use `(hd _).2 fun x hx o => ?_` and prove the remaining obligations. Establish `he` using `hy x hx`.

Rewrite `he` using `[hE_smul_transpose, ← GlobalTheory.HermSelfDualLoc.isIntegral_iff_mem_range]`. Rewrite using `[form_smul_left]`. Conclude with `hb _ he o`. Unfold `IsSelfDualAt`. Rewrite using `[← GlobalTheory.AdelicU.SelfDual.latLoc_dualGlob hJ hL]`.

Conclude with `le_antisymm (latLoc_le_of_smul_mem v 1 ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top) _ _ h1) (latLoc_le_of_smul_mem v s hs _ _ h2)`.
-/
theorem isSelfDualAt_smul_transpose : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), J.det ≠ 0 → L.IsLattice E →
    (∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x))) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (δ : E) (s : 𝓞 F), δ ≠ 0 → s ∉ v.asIdeal →
    (∀ t : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * t))) → IsIntegral ℤ (δ * t)) →
    (∀ t : E, IsIntegral ℤ (δ * t) → ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * (algebraMap F E (s : F) * t)))) →
    IsSelfDualAt σ (δ • Jᵀ) L v := by
  intro F E _ _ _ _ _ σ n J L hJ0 hL hd v δ s hδ hs ha hb
  have hJ : (δ • Jᵀ).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hδ) hJ0
  have h1 : ∀ y ∈ L, algebraMap F E ((1 : 𝓞 F) : F) • y ∈ GlobalTheory.AdelicU.SelfDual.dualGlob σ (δ • Jᵀ) L := by
    intro y hy
    have e : algebraMap F E ((1 : 𝓞 F) : F) • y = y := by simp
    rw [e]
    intro x hx
    rw [hE_smul_transpose, ← GlobalTheory.HermSelfDualLoc.isIntegral_iff_mem_range]
    exact ha _ ((hd y).1 hy x hx)
  have h2 : ∀ y ∈ GlobalTheory.AdelicU.SelfDual.dualGlob σ (δ • Jᵀ) L, algebraMap F E (s : F) • y ∈ L := by
    intro y hy
    refine (hd _).2 fun x hx o => ?_
    have he := hy x hx
    rw [hE_smul_transpose, ← GlobalTheory.HermSelfDualLoc.isIntegral_iff_mem_range] at he
    rw [form_smul_left]
    exact hb _ he o
  unfold IsSelfDualAt
  rw [← GlobalTheory.AdelicU.SelfDual.latLoc_dualGlob hJ hL]
  exact le_antisymm (latLoc_le_of_smul_mem v 1 ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top) _ _ h1)
    (latLoc_le_of_smul_mem v s hs _ _ h2)

end GlobalTheory.TraceSelfDualAt

end
