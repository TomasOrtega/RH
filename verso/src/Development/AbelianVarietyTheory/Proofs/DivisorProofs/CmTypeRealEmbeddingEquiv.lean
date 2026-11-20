import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

noncomputable section

namespace GlobalTheory.CMEquiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply, Subfield.subtype_apply]`. Rewrite using `[← IsCMField.complexEmbedding_complexConj, (IsCMField.complexConj_eq_self_iff E _).2 x.2]`.
-/
theorem isReal_res (σ : E →+* ℂ) : ComplexEmbedding.IsReal (σ.comp (maximalRealSubfield E).subtype) := by
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply, Subfield.subtype_apply]
  rw [← IsCMField.complexEmbedding_complexConj, (IsCMField.complexConj_eq_self_iff E _).2 x.2]

def res (σ : E →+* ℂ) : FR E →+* ℝ := (isReal_res σ).embedding

/- English proof (translation)
The claim follows from `ComplexEmbedding.IsReal.coe_embedding_apply _ x`.
-/
theorem res_apply (σ : E →+* ℂ) (x : FR E) : ((res σ x : ℝ) : ℂ) = σ (x : E) :=
  ComplexEmbedding.IsReal.coe_embedding_apply _ x

/- English proof (translation)
Use `letI : Algebra (FR E) ℂ := ψ.toAlgebra`. Set `f : E →ₐ[FR E] ℂ` to `IsAlgClosed.lift`. Conclude with `⟨f.toRingHom, fun x => f.commutes x⟩`.
-/
theorem exists_ext (ψ : FR E →+* ℂ) : ∃ σ : E →+* ℂ, ∀ x : FR E, σ (x : E) = ψ x := by
  letI : Algebra (FR E) ℂ := ψ.toAlgebra
  let f : E →ₐ[FR E] ℂ := IsAlgClosed.lift
  exact ⟨f.toRingHom, fun x => f.commutes x⟩

/- English proof (translation)
Use `set c := IsCMField.complexConj E with hc`. Take `⟨y, hy⟩ : ∃ y, c y ≠ y` from `by by_contra! H`. Conclude with `IsCMField.complexConj_ne_one E (AlgEquiv.ext H)`. Establish `cc : ∀ z, c (c z) = z` using `IsCMField.complexConj_apply_apply E`. Use `set α := y - c y with hα`.

Establish `hα0 : α ≠ 0` using `sub_ne_zero.2 (Ne.symm hy)`. Establish `hcα : c α = -α` using `by rw [hα, map_sub, cc]; ring`. Establish `mem : ∀ z, c z = z → σ' z = σ z` using `fun z hz => h ⟨z, (IsCMField.complexConj_eq_self_iff E z).1 hz⟩`. Establish `hsq : σ' α ^ 2 = σ α ^ 2`. Rewrite using `[← map_pow, ← map_pow]; exact mem _ (by rw [map_pow, hcα]; ring)`.

Establish `dec : ∀ z, ∃ a b, c a = a ∧ c b = b ∧ z = a + b * α ∧ c z = a - b * α`. Introduce `z`. Use `⟨(z + c z) / 2, (z - c z) / (2 * α), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, map_add, cc, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[map_div₀, map_sub, cc, map_mul, map_ofNat, hcα]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hsq' : (σ' α - σ α) * (σ' α + σ α) = 0` using `by linear_combination hsq`. Break down `mul_eq_zero.1 hsq' with h1 | h1` into its components or cases. Use `left`.

Use extensionality with `z`. Take `⟨a, b, ha, hb, hz, -⟩` from `dec z`. Rewrite using `[hz, map_add, map_add, map_mul, map_mul, mem a ha, mem b hb, sub_eq_zero.1 h1]`. Use `right`. Use extensionality with `z`.

Take `⟨a, b, ha, hb, hz, hcz⟩` from `dec z`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, ← IsCMField.complexEmbedding_complexConj, ← hc, hcz, hz, map_add, map_sub, map_mul, map_mul, mem a ha, mem b hb, eq_neg_of_add_eq_zero_left h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eq_or_eq_conj (σ σ' : E →+* ℂ) (h : ∀ x : FR E, σ' (x : E) = σ (x : E)) :
    σ' = σ ∨ σ' = ComplexEmbedding.conjugate σ := by
  set c := IsCMField.complexConj E with hc
  obtain ⟨y, hy⟩ : ∃ y, c y ≠ y := by
    by_contra! H
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext H)
  have cc : ∀ z, c (c z) = z := IsCMField.complexConj_apply_apply E
  set α := y - c y with hα
  have hα0 : α ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hcα : c α = -α := by rw [hα, map_sub, cc]; ring
  have mem : ∀ z, c z = z → σ' z = σ z := fun z hz =>
    h ⟨z, (IsCMField.complexConj_eq_self_iff E z).1 hz⟩
  have hsq : σ' α ^ 2 = σ α ^ 2 := by
    rw [← map_pow, ← map_pow]; exact mem _ (by rw [map_pow, hcα]; ring)
  have dec : ∀ z, ∃ a b, c a = a ∧ c b = b ∧ z = a + b * α ∧ c z = a - b * α := by
    intro z
    refine ⟨(z + c z) / 2, (z - c z) / (2 * α), ?_, ?_, ?_, ?_⟩
    · rw [map_div₀, map_add, cc, map_ofNat]; ring
    · rw [map_div₀, map_sub, cc, map_mul, map_ofNat, hcα]
      field_simp
      ring
    · field_simp; ring
    · field_simp; ring
  have hsq' : (σ' α - σ α) * (σ' α + σ α) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hsq' with h1 | h1
  · left
    ext z
    obtain ⟨a, b, ha, hb, hz, -⟩ := dec z
    rw [hz, map_add, map_add, map_mul, map_mul, mem a ha, mem b hb, sub_eq_zero.1 h1]
  · right
    ext z
    obtain ⟨a, b, ha, hb, hz, hcz⟩ := dec z
    rw [ComplexEmbedding.conjugate_coe_eq, ← IsCMField.complexEmbedding_complexConj, ← hc, hcz, hz,
      map_add, map_sub, map_mul, map_mul, mem a ha, mem b hb, eq_neg_of_add_eq_zero_left h1]
    ring

/- English proof (translation)
Establish `hRC : Function.Bijective (fun τ : FR E →+* ℝ => Complex.ofRealHom.comp τ)`. Prove the components needed by the constructor for the conclusion. Introduce `τ τ' hτ`. Use extensionality with `x`. Conclude with `Complex.ofReal_injective (RingHom.congr_fun hτ x)`.

Introduce `ψ`. Take `⟨σ, hσ⟩` from `exists_ext ψ`. Use `⟨res σ, RingHom.ext fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [RingHom.coe_comp, Function.comp_apply, Complex.ofRealHom_eq_coe]`. Rewrite using `[res_apply, hσ]`.

Set `eRC` to `Equiv.ofBijective _ hRC`. Set `e' : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)` to `(Fintype.equivFinOfCardEq (Embeddings.card (FR E) ℂ)).symm.trans eRC.symm`. Establish `hb : Function.Bijective (fun i => res (φ i))`. Prove the components needed by the constructor for the conclusion. Introduce `i j hij`.

Establish `hx : ∀ x : FR E, φ j (x : E) = φ i (x : E)` using `fun x => by`. Rewrite using `[← res_apply, ← res_apply]`. Conclude with `congrArg (fun τ : FR E →+* ℝ => ((τ x : ℝ) : ℂ)) hij.symm`. Take `⟨k, -, hk⟩` from `hφ (φ j)`. Conclude with `(hk i (eq_or_eq_conj (φ i) (φ j) hx)).trans (hk j (Or.inl rfl)).symm`.

Introduce `τ`. Take `⟨σ, hσ⟩` from `exists_ext (Complex.ofRealHom.comp τ)`. Take `⟨i, hi, -⟩` from `hφ σ`. Use `⟨i, RingHom.ext fun x => Complex.ofReal_injective ?_⟩` and prove the remaining obligations. Rewrite using `[res_apply]`.

Break down `hi with h | h` into its components or cases. Rewrite using `[← h, hσ]`. Both sides reduce to the same expression. Establish `h' : φ i = ComplexEmbedding.conjugate σ`. Use extensionality with `z`.

Rewrite using `[ComplexEmbedding.conjugate_coe_eq, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]`. Rewrite using `[h', ComplexEmbedding.conjugate_coe_eq, hσ]`. Simplify using the standard rewrite rules. Set `b` to `Equiv.ofBijective _ hb`. Use `⟨e'.trans b.symm, e', fun j x => ?_⟩` and prove the remaining obligations.

Establish `hj : res (φ ((e'.trans b.symm) j)) = e' j` using `b.apply_symm_apply (e' j)`. Rewrite using `[← hj, res_apply]`.
-/
theorem cmType_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) :
    ∃ (e : Fin (Module.finrank ℚ (FR E)) ≃ I) (e' : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)),
      ∀ j (x : FR E), ((e' j x : ℝ) : ℂ) = φ (e j) (x : E) := by
  have hRC : Function.Bijective (fun τ : FR E →+* ℝ => Complex.ofRealHom.comp τ) := by
    constructor
    · intro τ τ' hτ
      ext x
      exact Complex.ofReal_injective (RingHom.congr_fun hτ x)
    · intro ψ
      obtain ⟨σ, hσ⟩ := exists_ext ψ
      refine ⟨res σ, RingHom.ext fun x => ?_⟩
      simp only [RingHom.coe_comp, Function.comp_apply, Complex.ofRealHom_eq_coe]
      rw [res_apply, hσ]
  let eRC := Equiv.ofBijective _ hRC
  let e' : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ) :=
    (Fintype.equivFinOfCardEq (Embeddings.card (FR E) ℂ)).symm.trans eRC.symm
  have hb : Function.Bijective (fun i => res (φ i)) := by
    constructor
    · intro i j hij
      have hx : ∀ x : FR E, φ j (x : E) = φ i (x : E) := fun x => by
        rw [← res_apply, ← res_apply]
        exact congrArg (fun τ : FR E →+* ℝ => ((τ x : ℝ) : ℂ)) hij.symm
      obtain ⟨k, -, hk⟩ := hφ (φ j)
      exact (hk i (eq_or_eq_conj (φ i) (φ j) hx)).trans (hk j (Or.inl rfl)).symm
    · intro τ
      obtain ⟨σ, hσ⟩ := exists_ext (Complex.ofRealHom.comp τ)
      obtain ⟨i, hi, -⟩ := hφ σ
      refine ⟨i, RingHom.ext fun x => Complex.ofReal_injective ?_⟩
      rw [res_apply]
      rcases hi with h | h
      · rw [← h, hσ]; rfl
      · have h' : φ i = ComplexEmbedding.conjugate σ := by
          ext z
          rw [ComplexEmbedding.conjugate_coe_eq, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
        rw [h', ComplexEmbedding.conjugate_coe_eq, hσ]
        simp
  let b := Equiv.ofBijective _ hb
  refine ⟨e'.trans b.symm, e', fun j x => ?_⟩
  have hj : res (φ ((e'.trans b.symm) j)) = e' j := b.apply_symm_apply (e' j)
  rw [← hj, res_apply]

end GlobalTheory.CMEquiv
