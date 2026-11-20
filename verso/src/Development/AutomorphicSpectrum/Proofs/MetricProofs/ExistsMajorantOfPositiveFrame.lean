import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TauMaj

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ComplexOrder

section Conj

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev cj (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := A.map (starRingEnd ℂ)

/- English proof (translation)
Use extensionality with `i k`. Simplify using `[cj]`.
-/
theorem cj_cj (A : Matrix ι ι ℂ) : cj (cj A) = A := by
  ext i k; simp [cj]

/- English proof (translation)
The claim follows from `Function.LeftInverse.injective cj_cj`.
-/
theorem cj_injective : Function.Injective (cj : Matrix ι ι ℂ → Matrix ι ι ℂ) :=
  Function.LeftInverse.injective cj_cj

/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
theorem cj_mul (A B : Matrix ι ι ℂ) : cj (A * B) = cj A * cj B := Matrix.map_mul

/- English proof (translation)
Use extensionality with `i k`. Simplify using `[cj]`.
-/
theorem cj_eq (A : Matrix ι ι ℂ) : cj A = Aᴴᵀ := by
  ext i k; simp [cj]

/- English proof (translation)
Rewrite using `[cj_eq, cj_eq, conjTranspose_nonsing_inv, transpose_nonsing_inv]`.
-/
theorem cj_inv (A : Matrix ι ι ℂ) : cj A⁻¹ = (cj A)⁻¹ := by
  rw [cj_eq, cj_eq, conjTranspose_nonsing_inv, transpose_nonsing_inv]

/- English proof (translation)
Use extensionality with `i k`. Simplify using `[cj]`.
-/
theorem cj_conjTranspose (A : Matrix ι ι ℂ) : cj Aᴴ = (cj A)ᴴ := by
  ext i k; simp [cj]

/- English proof (translation)
Establish `: cj P = Pᵀ` using `by rw [cj_eq, h.1.eq]`. Rewrite using `[this]`. Conclude with `h.transpose`.
-/
theorem posDef_cj {P : Matrix ι ι ℂ} (h : P.PosDef) : (cj P).PosDef := by
  have : cj P = Pᵀ := by rw [cj_eq, h.1.eq]
  rw [this]
  exact h.transpose

/- English proof (translation)
Use extensionality with `i`. Simplify using `[cj, mulVec, dotProduct, map_sum]`.
-/
theorem cj_mulVec (A : Matrix ι ι ℂ) (v : ι → ℂ) : cj A *ᵥ star v = star (A *ᵥ v) := by
  ext i; simp [cj, mulVec, dotProduct, map_sum]

/- English proof (translation)
Establish `hu : G *ᵥ star v = star (cj G *ᵥ v)`. Rewrite using `[← cj_mulVec, cj_cj]`. Rewrite using `[hu, cj_mulVec, star_dotProduct_star, dotProduct_comm]`. Simplify using the standard rewrite rules.
-/
theorem re_term_cj (P G : Matrix ι ι ℂ) (v : ι → ℂ) :
    (star (G *ᵥ star v) ⬝ᵥ (cj P *ᵥ (G *ᵥ star v))).re = (star (cj G *ᵥ v) ⬝ᵥ (P *ᵥ (cj G *ᵥ v))).re := by
  have hu : G *ᵥ star v = star (cj G *ᵥ v) := by
    rw [← cj_mulVec, cj_cj]
  rw [hu, cj_mulVec, star_dotProduct_star, dotProduct_comm]
  simp

/- English proof (translation)
Establish `h : (G.map (starRingEnd ℂ))ᵀ * cj P * G = cj ((cj G)ᴴ * P * cj G)`. Rewrite using `[cj_mul, cj_mul, cj_conjTranspose, cj_cj]`. Both sides reduce to the same expression. Rewrite using `[h]`. Conclude with `cj_injective.eq_iff`.
-/
theorem stab_iff_cj (P G : Matrix ι ι ℂ) :
    (G.map (starRingEnd ℂ))ᵀ * cj P * G = cj P ↔ (cj G)ᴴ * P * cj G = P := by
  have h : (G.map (starRingEnd ℂ))ᵀ * cj P * G = cj ((cj G)ᴴ * P * cj G) := by
    rw [cj_mul, cj_mul, cj_conjTranspose, cj_cj]
    rfl
  rw [h]
  exact cj_injective.eq_iff

end Conj

section Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

omit [IsCMField E] in
/- English proof (translation)
The claim follows from `IsFractionRing.lift_algebraMap (intEmb_injective s) a`.
-/
theorem embOf_coe (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : embOf s (a : E) = s a :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) a

omit [IsCMField E] in
/- English proof (translation)
The claim follows from `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (by ext a; simpa using embOf_coe (φ.comp (algebraMap (𝓞 E) E)) a)`.
-/
theorem embOf_comp (φ : E →+* ℂ) : embOf (φ.comp (algebraMap (𝓞 E) E)) = φ :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (by
    ext a; simpa using embOf_coe (φ.comp (algebraMap (𝓞 E) E)) a)

omit [IsCMField E] in
/- English proof (translation)
Introduce `s s' h`. Use extensionality with `a`. Use `congrArg (fun φ : E →+* ℂ => φ (a : E)) h` as an intermediate fact. Simplify `this` using `[embOf_coe]`.
-/
theorem embOf_injective : Function.Injective (embOf : (𝓞 E →+* ℂ) → (E →+* ℂ)) := by
  intro s s' h
  ext a
  have := congrArg (fun φ : E →+* ℂ => φ (a : E)) h
  simpa [embOf_coe] using this

/- English proof (translation)
Establish `hcm` using `F.cm`. Prove the components needed by the constructor for the conclusion. Introduce `τ τ' h`. Break down `InfinitePlace.mk_eq_iff.1 h with h | h` into its components or cases. Conclude with `hcm.1 (embOf_injective h)`.

It suffices to derive a contradiction. Establish `hs : F.σ τ' = (starRingEnd ℂ).comp (F.σ τ)`. Use extensionality with `a`. Use `congrArg (fun φ : E →+* ℂ => φ (a : E)) h` as an intermediate fact. Simplify `this.symm` using `[embOf_coe, ComplexEmbedding.conjugate_coe_eq]`.

Conclude with `((hcm.2 (F.σ τ)).1 ⟨τ, rfl⟩) ⟨τ', hs⟩`. Introduce `w set s : 𝓞 E →+* ℂ := w.embedding.comp (algebraMap (𝓞 E) E) with hs`. Distinguish the cases in `h : ∃ τ, F.σ τ = s`. Take `⟨τ, hτ⟩` from `h`. Use `⟨τ, ?_⟩` and prove the remaining obligations.

Rewrite using `[plc, hτ, hs, embOf_comp, InfinitePlace.mk_embedding]`. Establish `h2 : ∃ τ, F.σ τ = (starRingEnd ℂ).comp s`. Assume the negation of the conclusion as `h3`. Conclude with `h ((hcm.2 s).2 h3)`. Take `⟨τ, hτ⟩` from `h2`.

Use `⟨τ, ?_⟩` and prove the remaining obligations. Establish `he : embOf (F.σ τ) = ComplexEmbedding.conjugate w.embedding`. Rewrite using `[hτ]`. Establish `: (starRingEnd ℂ).comp s = (ComplexEmbedding.conjugate w.embedding).comp (algebraMap (𝓞 E) E)`. Use extensionality with `a`.

Simplify using `[hs, ComplexEmbedding.conjugate_coe_eq]`. Rewrite using `[this, embOf_comp]`. Rewrite using `[plc, he, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]`.
-/
theorem plc_bijective (F : UnivFam E Ψ j j' n g Λ) : Function.Bijective (plc F) := by
  have hcm := F.cm
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact hcm.1 (embOf_injective h)
    · exfalso
      have hs : F.σ τ' = (starRingEnd ℂ).comp (F.σ τ) := by
        ext a
        have := congrArg (fun φ : E →+* ℂ => φ (a : E)) h
        simpa [embOf_coe, ComplexEmbedding.conjugate_coe_eq] using this.symm
      exact ((hcm.2 (F.σ τ)).1 ⟨τ, rfl⟩) ⟨τ', hs⟩
  · intro w
    set s : 𝓞 E →+* ℂ := w.embedding.comp (algebraMap (𝓞 E) E) with hs
    by_cases h : ∃ τ, F.σ τ = s
    · obtain ⟨τ, hτ⟩ := h
      refine ⟨τ, ?_⟩
      rw [plc, hτ, hs, embOf_comp, InfinitePlace.mk_embedding]
    · have h2 : ∃ τ, F.σ τ = (starRingEnd ℂ).comp s := by
        by_contra h3
        exact h ((hcm.2 s).2 h3)
      obtain ⟨τ, hτ⟩ := h2
      refine ⟨τ, ?_⟩
      have he : embOf (F.σ τ) = ComplexEmbedding.conjugate w.embedding := by
        rw [hτ]
        have : (starRingEnd ℂ).comp s =
            (ComplexEmbedding.conjugate w.embedding).comp (algebraMap (𝓞 E) E) := by
          ext a; simp [hs, ComplexEmbedding.conjugate_coe_eq]
        rw [this, embOf_comp]
      rw [plc, he, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

/- English proof (translation)
The claim follows from `(InfinitePlace.embedding_mk_eq (embOf (F.σ τ))).resolve_left h`.
-/
theorem emb_ne (F : UnivFam E Ψ j j' n g Λ) (τ : Ψ) (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    (plc F τ).embedding = ComplexEmbedding.conjugate (embOf (F.σ τ)) :=
  (InfinitePlace.embedding_mk_eq (embOf (F.σ τ))).resolve_left h

def atPlc (F : UnivFam E Ψ j j' n g Λ) (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (τ : Ψ) :
    Matrix (Fin (j + j')) (Fin (j + j')) ℂ := by
  classical
  exact if (plc F τ).embedding = embOf (F.σ τ) then Pt τ else cj (Pt τ)

variable {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

/- English proof (translation)
Rewrite using `[gramAt, h]`. Both sides reduce to the same expression.
-/
theorem gramAt_of_eq {τ : Ψ} (h : (plc F τ).embedding = embOf (F.σ τ)) :
    gramAt C.h (Pi.basisFun E (Fin (j + j'))) (plc F τ) = C.gr τ := by
  rw [gramAt, h]; rfl

/- English proof (translation)
Rewrite using `[gramAt, emb_ne F τ h]`. Use extensionality with `i k`. Simplify using `[LatEmb.gr, ComplexEmbedding.conjugate_coe_eq]`.
-/
theorem gramAt_of_ne {τ : Ψ} (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    gramAt C.h (Pi.basisFun E (Fin (j + j'))) (plc F τ) = cj (C.gr τ) := by
  rw [gramAt, emb_ne F τ h]
  ext i k
  simp [LatEmb.gr, ComplexEmbedding.conjugate_coe_eq]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[vecAt, LatEmb.vec, h]`.
-/
theorem vecAt_of_eq (x : Λ) {τ : Ψ} (h : (plc F τ).embedding = embOf (F.σ τ)) :
    vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x) (plc F τ) = C.vec x τ := by
  ext i
  simp [vecAt, LatEmb.vec, h]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[vecAt, LatEmb.vec, emb_ne F τ h, ComplexEmbedding.conjugate_coe_eq]`.
-/
theorem vecAt_of_ne (x : Λ) {τ : Ψ} (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x) (plc F τ) = star (C.vec x τ) := by
  ext i
  simp [vecAt, LatEmb.vec, emb_ne F τ h, ComplexEmbedding.conjugate_coe_eq]

/- English proof (translation)
Rewrite using `[LatEmb.tm, tauMat, if_pos h]`.
-/
theorem tm_of_eq (a : C.Arch) {τ : Ψ} (h : (plc F τ).embedding = embOf (F.σ τ)) :
    C.tm a τ = ((a : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) := by
  rw [LatEmb.tm, tauMat, if_pos h]

/- English proof (translation)
Rewrite using `[LatEmb.tm, tauMat, if_neg h]`.
-/
theorem tm_of_ne (a : C.Arch) {τ : Ψ} (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    C.tm a τ = cj ((a : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) := by
  rw [LatEmb.tm, tauMat, if_neg h]

/- English proof (translation)
Rewrite using `[atPlc]`. Conclude with `if_pos h`.
-/
theorem atPlc_of_eq (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) {τ : Ψ}
    (h : (plc F τ).embedding = embOf (F.σ τ)) : atPlc F Pt τ = Pt τ := by
  rw [atPlc]; exact if_pos h

/- English proof (translation)
Rewrite using `[atPlc]`. Conclude with `if_neg h`.
-/
theorem atPlc_of_ne (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) {τ : Ψ}
    (h : (plc F τ).embedding ≠ embOf (F.σ τ)) : atPlc F Pt τ = cj (Pt τ) := by
  rw [atPlc]; exact if_neg h

def majOf (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) : Majorant C.h (Pi.basisFun E (Fin (j + j'))) where
  P w := atPlc F Pt ((Equiv.ofBijective _ (plc_bijective F)).symm w)
  posDef w := by
    obtain ⟨τ, rfl⟩ := (plc_bijective F).2 w
    have hτ : (Equiv.ofBijective _ (plc_bijective F)).symm (plc F τ) = τ :=
      Equiv.ofBijective_symm_apply_apply _ _ _
    rw [hτ]
    by_cases h : (plc F τ).embedding = embOf (F.σ τ)
    · rw [atPlc_of_eq Pt h]; exact hP τ
    · rw [atPlc_of_ne Pt h]; exact posDef_cj (hP τ)
  siegel w := by
    obtain ⟨τ, rfl⟩ := (plc_bijective F).2 w
    have hτ : (Equiv.ofBijective _ (plc_bijective F)).symm (plc F τ) = τ :=
      Equiv.ofBijective_symm_apply_apply _ _ _
    rw [hτ]
    by_cases h : (plc F τ).embedding = embOf (F.σ τ)
    · rw [atPlc_of_eq Pt h, gramAt_of_eq C h]; exact hS τ
    · rw [atPlc_of_ne Pt h, gramAt_of_ne C h, ← cj_inv, ← cj_mul, ← cj_mul, hS τ]

/- English proof (translation)
Use `show atPlc F Pt ((Equiv.ofBijective _ (plc_bijective F)).symm (plc F τ)) = _`. Rewrite using `[Equiv.ofBijective_symm_apply_apply]`.
-/
theorem majOf_P (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (τ : Ψ) : (majOf C Pt hP hS).P (plc F τ) = atPlc F Pt τ := by
  show atPlc F Pt ((Equiv.ofBijective _ (plc_bijective F)).symm (plc F τ)) = _
  rw [Equiv.ofBijective_symm_apply_apply]

/- English proof (translation)
Rewrite using `[majOf_P]`. Distinguish the cases in `h : (plc F τ).embedding = embOf (F.σ τ)`. Rewrite using `[atPlc_of_eq Pt h, tm_of_eq C _ h, ← vecAt_of_eq C x h]`. Both sides reduce to the same expression. Rewrite using `[atPlc_of_ne Pt h, tm_of_ne C _ h, ← re_term_cj, ← vecAt_of_ne C x h]`.

Both sides reduce to the same expression.
-/
theorem majOf_term (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (a : C.Arch) (x : Λ) (τ : Ψ) :
    (star (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x)) (plc F τ)) ⬝ᵥ
      ((majOf C Pt hP hS).P (plc F τ) *ᵥ invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x)) (plc F τ))).re =
    (star (C.tm a⁻¹ τ *ᵥ C.vec x τ) ⬝ᵥ (Pt τ *ᵥ (C.tm a⁻¹ τ *ᵥ C.vec x τ))).re := by
  rw [majOf_P]
  by_cases h : (plc F τ).embedding = embOf (F.σ τ)
  · rw [atPlc_of_eq Pt h, tm_of_eq C _ h, ← vecAt_of_eq C x h]
    rfl
  · rw [atPlc_of_ne Pt h, tm_of_ne C _ h, ← re_term_cj, ← vecAt_of_ne C x h]
    rfl

/- English proof (translation)
Rewrite using `[Majorant.len, Real.sq_sqrt]`. Rewrite using `[← (Equiv.ofBijective _ (plc_bijective F)).sum_comp]`. Conclude with `Finset.sum_congr rfl fun τ _ => majOf_term C Pt hP hS a x τ`. Conclude with `Finset.sum_nonneg fun w _ => ((majOf C Pt hP hS).posDef w).posSemidef.re_dotProduct_nonneg _`.
-/
theorem majOf_len (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (a : C.Arch) (x : Λ) :
    (majOf C Pt hP hS).len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x))) ^ 2 =
      ∑ τ, (star (C.tm a⁻¹ τ *ᵥ C.vec x τ) ⬝ᵥ (Pt τ *ᵥ (C.tm a⁻¹ τ *ᵥ C.vec x τ))).re := by
  rw [Majorant.len, Real.sq_sqrt]
  · rw [← (Equiv.ofBijective _ (plc_bijective F)).sum_comp]
    exact Finset.sum_congr rfl fun τ _ => majOf_term C Pt hP hS a x τ
  · exact Finset.sum_nonneg fun w _ => ((majOf C Pt hP hS).posDef w).posSemidef.re_dotProduct_nonneg _

/- English proof (translation)
Establish `hloc : ∀ τ, ((((c : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)).map (starRingEnd ℂ))ᵀ * (majOf C Pt hP hS).P (plc F τ) * ((c : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) = (majOf C Pt …`. Introduce `τ`. Rewrite using `[majOf_P]`. Distinguish the cases in `h : (plc F τ).embedding = embOf (F.σ τ)`. Rewrite using `[atPlc_of_eq Pt h, tm_of_eq C _ h]`.

Both sides reduce to the same expression. Rewrite using `[atPlc_of_ne Pt h, tm_of_ne C _ h]`. Conclude with `stab_iff_cj _ _`. Rewrite using `[Majorant.stab, Subgroup.mem_subgroupOf, Subgroup.mem_pi]`. Prove the components needed by the constructor for the conclusion.

Introduce `hc τ`. Conclude with `(hloc τ).1 (mem_unitaryGroupMatrix.1 (hc (plc F τ) (Set.mem_univ _)))`. Introduce `hc w _`. Take `⟨τ, rfl⟩` from `(plc_bijective F).2 w`. Conclude with `mem_unitaryGroupMatrix.2 ((hloc τ).2 (hc τ))`.
-/
theorem majOf_stab (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (c : C.Arch) :
    c ∈ (majOf C Pt hP hS).stab ↔ ∀ τ, (C.tm c τ)ᴴ * Pt τ * C.tm c τ = Pt τ := by
  have hloc : ∀ τ, ((((c : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)).map
        (starRingEnd ℂ))ᵀ * (majOf C Pt hP hS).P (plc F τ) *
        ((c : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) =
        (majOf C Pt hP hS).P (plc F τ) ↔ (C.tm c τ)ᴴ * Pt τ * C.tm c τ = Pt τ := by
    intro τ
    rw [majOf_P]
    by_cases h : (plc F τ).embedding = embOf (F.σ τ)
    · rw [atPlc_of_eq Pt h, tm_of_eq C _ h]
      rfl
    · rw [atPlc_of_ne Pt h, tm_of_ne C _ h]
      exact stab_iff_cj _ _
  rw [Majorant.stab, Subgroup.mem_subgroupOf, Subgroup.mem_pi]
  constructor
  · intro hc τ
    exact (hloc τ).1 (mem_unitaryGroupMatrix.1 (hc (plc F τ) (Set.mem_univ _)))
  · intro hc w _
    obtain ⟨τ, rfl⟩ := (plc_bijective F).2 w
    exact mem_unitaryGroupMatrix.2 ((hloc τ).2 (hc τ))

end Arch

/- English proof (translation)
Introduce `E _ _ _ Ψ _ j j' n g Λ _ _ F C Pt hP hS`. Conclude with `⟨majOf C Pt hP hS, majOf_len C Pt hP hS, majOf_stab C Pt hP hS⟩`.
-/
theorem exists_majorant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type)
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F)
    (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), (∀ τ, (Pt τ).PosDef) →
    (∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) →
    ∃ M : Majorant C.h (Pi.basisFun E (Fin (j + j'))),
      (∀ (a : C.Arch) (x : Λ), M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x))) ^ 2 =
        ∑ τ, (star (C.tm a⁻¹ τ *ᵥ C.vec x τ) ⬝ᵥ (Pt τ *ᵥ (C.tm a⁻¹ τ *ᵥ C.vec x τ))).re) ∧
      ∀ c : C.Arch, c ∈ M.stab ↔ ∀ τ, (C.tm c τ)ᴴ * Pt τ * C.tm c τ = Pt τ :=
  by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C Pt hP hS
  exact ⟨majOf C Pt hP hS, majOf_len C Pt hP hS, majOf_stab C Pt hP hS⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TauMaj
