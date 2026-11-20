import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TmBasic

/- English proof (translation)
Establish `h2` using `congrArg (fun X : Matrix ι ι ℂ => X.map (starRingEnd ℂ)) h`. Simplify using `only [Matrix.map_mul] at h2`. Establish `e1 : (G.map (starRingEnd ℂ)).map (starRingEnd ℂ) = G` using `by ext i k; simp`. Establish `e2 : ((M.map (starRingEnd ℂ))ᵀ).map (starRingEnd ℂ) = (M.map (starRingEnd ℂ))ᴴ`. Use extensionality with `i k`.

Simplify using `[Matrix.conjTranspose_apply]`. Rewrite `h2` using `[e1, e2]`. Conclude with `h2`.
-/
theorem conj_unitary {ι : Type} [Fintype ι] (M G : Matrix ι ι ℂ)
    (h : (M.map (starRingEnd ℂ))ᵀ * G.map (starRingEnd ℂ) * M = G.map (starRingEnd ℂ)) :
    (M.map (starRingEnd ℂ))ᴴ * G * M.map (starRingEnd ℂ) = G := by
  have h2 := congrArg (fun X : Matrix ι ι ℂ => X.map (starRingEnd ℂ)) h
  simp only [Matrix.map_mul] at h2
  have e1 : (G.map (starRingEnd ℂ)).map (starRingEnd ℂ) = G := by ext i k; simp
  have e2 : ((M.map (starRingEnd ℂ))ᵀ).map (starRingEnd ℂ) = (M.map (starRingEnd ℂ))ᴴ := by
    ext i k; simp [Matrix.conjTranspose_apply]
  rw [e1, e2] at h2
  exact h2

/- English proof (translation)
Introduce `E _ _ _ Ψ _ j j' n g Λ _ _ F C`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b τ`. Simplify using `only [LatEmb.tm, tauMat]`. Use `split_ifs with h`.

Simplify using the standard rewrite rules. Simplify using `[Matrix.map_mul]`. Introduce `τ`. Simplify using `only [LatEmb.tm, tauMat]`. Use `split_ifs with h`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce `a τ`. Establish `hm` using `mem_archUnitary.1 a.2 (plc F τ)`. Simplify using `only [LatEmb.tm, tauMat, LatEmb.gr]`.

Distinguish the cases in `h0 : (plc F τ).embedding = embOf (F.σ τ)`. Rewrite using `[if_pos h0]`. Rewrite `hm` using `[gramAt, h0]`. Establish `e : ((a.1 (plc F τ) : GL (Fin (j + j')) ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)ᴴ = (((a.1 (plc F τ) : GL (Fin (j + j')) ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ).map (starRingEnd ℂ))ᵀ`. Use extensionality with `i k`.

Simplify using `[Matrix.conjTranspose_apply]`. Rewrite using `[e]`. Conclude with `hm`. Establish `h' : (plc F τ).embedding = ComplexEmbedding.conjugate (embOf (F.σ τ))` using `(InfinitePlace.embedding_mk_eq (embOf (F.σ τ))).resolve_left h0`. Rewrite using `[if_neg h0]`.

Apply `conj_unitary` to reduce the goal to its premises. Establish `e : gramAt C.h (Pi.basisFun E (Fin (j + j'))) (plc F τ) = ((gram C.h.toSesq (Pi.basisFun E (Fin (j + j')))).map (embOf (F.σ τ))).map (starRingEnd ℂ)`. Rewrite using `[gramAt, h']`. Use extensionality with `i k`. Simplify using `[ComplexEmbedding.conjugate_coe_eq]`.

Rewrite `hm` using `[e]`. Conclude with `hm`. Introduce `τ`. Simplify using `only [LatEmb.tm, tauMat]`. Establish `hc : Continuous fun a : C.Arch => ((a.1 (plc F τ) : GL _ ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)` using `Units.continuous_val.comp ((continuous_apply (plc F τ)).comp continuous_subtype_val)`.

Use `split_ifs with h`. Conclude with `hc`. Conclude with `hc.matrix_map Complex.continuous_conj`.
-/
theorem tm_basic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F), (∀ (a b : C.Arch) τ, C.tm (a * b) τ = C.tm a τ * C.tm b τ) ∧ (∀ τ, C.tm 1 τ = 1) ∧ (∀ (a : C.Arch) τ, (C.tm a τ)ᴴ * C.gr τ * C.tm a τ = C.gr τ) ∧ ∀ τ, Continuous fun a : C.Arch => C.tm a τ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b τ
    simp only [LatEmb.tm, tauMat]
    split_ifs with h
    · simp
    · simp [Matrix.map_mul]
  · intro τ
    simp only [LatEmb.tm, tauMat]
    split_ifs with h
    · simp
    · simp
  · intro a τ
    have hm := mem_archUnitary.1 a.2 (plc F τ)
    simp only [LatEmb.tm, tauMat, LatEmb.gr]
    by_cases h0 : (plc F τ).embedding = embOf (F.σ τ)
    · rw [if_pos h0]
      rw [gramAt, h0] at hm
      have e : ((a.1 (plc F τ) : GL (Fin (j + j')) ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)ᴴ =
          (((a.1 (plc F τ) : GL (Fin (j + j')) ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ).map
            (starRingEnd ℂ))ᵀ := by
        ext i k; simp [Matrix.conjTranspose_apply]
      rw [e]
      exact hm
    · have h' : (plc F τ).embedding = ComplexEmbedding.conjugate (embOf (F.σ τ)) :=
        (InfinitePlace.embedding_mk_eq (embOf (F.σ τ))).resolve_left h0
      rw [if_neg h0]
      apply conj_unitary
      have e : gramAt C.h (Pi.basisFun E (Fin (j + j'))) (plc F τ) =
          ((gram C.h.toSesq (Pi.basisFun E (Fin (j + j')))).map (embOf (F.σ τ))).map (starRingEnd ℂ) := by
        rw [gramAt, h']
        ext i k
        simp [ComplexEmbedding.conjugate_coe_eq]
      rw [e] at hm
      exact hm
  · intro τ
    simp only [LatEmb.tm, tauMat]
    have hc : Continuous fun a : C.Arch =>
        ((a.1 (plc F τ) : GL _ ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) :=
      Units.continuous_val.comp ((continuous_apply (plc F τ)).comp continuous_subtype_val)
    split_ifs with h
    · exact hc
    · exact hc.matrix_map Complex.continuous_conj

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TmBasic
