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

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

section TmSurj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in

/- English proof (translation)
The claim follows from `IsFractionRing.lift_algebraMap (intEmb_injective s) x`.
-/
theorem embOf_coe (s : 𝓞 E →+* ℂ) (x : 𝓞 E) : embOf s (x : E) = s x :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) x

omit [IsCMField E] in

/- English proof (translation)
Apply `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `using embOf_coe (φ.comp (algebraMap (𝓞 E) E)) x`.
-/
theorem embOf_restrict (φ : E →+* ℂ) : embOf (φ.comp (algebraMap (𝓞 E) E)) = φ := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
  ext x
  simpa using embOf_coe (φ.comp (algebraMap (𝓞 E) E)) x

omit [IsCMField E] in

/- English proof (translation)
Apply `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))` to reduce the goal to its premises. Use extensionality with `x`. Establish `h1` using `embOf_coe ((starRingEnd ℂ).comp s) x`. Establish `h2` using `embOf_coe s x`. Simplify using `only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq]`.

Express the relevant statement in the definitionally equal form `embOf ((starRingEnd ℂ).comp s) (x : E) = starRingEnd ℂ (embOf s (x : E))`. Rewrite using `[h1, h2]`. Both sides reduce to the same expression.
-/
theorem embOf_conj (s : 𝓞 E →+* ℂ) : embOf ((starRingEnd ℂ).comp s) = ComplexEmbedding.conjugate (embOf s) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
  ext x
  have h1 := embOf_coe ((starRingEnd ℂ).comp s) x
  have h2 := embOf_coe s x
  simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq]
  change embOf ((starRingEnd ℂ).comp s) (x : E) = starRingEnd ℂ (embOf s (x : E))
  rw [h1, h2]; rfl

omit [IsCMField E] in

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[← embOf_coe s, ← embOf_coe s', h]`.
-/
theorem embOf_inj {s s' : 𝓞 E →+* ℂ} (h : embOf s = embOf s') : s = s' := by
  ext x
  rw [← embOf_coe s, ← embOf_coe s', h]

variable {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `τ τ' h`. Break down `InfinitePlace.mk_eq_iff.1 h with h | h` into its components or cases. Conclude with `F.cm.1 (embOf_inj h)`. It suffices to derive a contradiction.

Rewrite `h` using `[← embOf_conj]`. Establish `h'` using `embOf_inj h`. Conclude with `(F.cm.2 (F.σ τ)).1 ⟨τ, rfl⟩ ⟨τ', h'.symm⟩`. Introduce `w`. Distinguish the cases in `hs : ∃ τ, F.σ τ = w.embedding.comp (algebraMap (𝓞 E) E)`.

Take `⟨τ, hτ⟩` from `hs`. Use `⟨τ, ?_⟩` and prove the remaining obligations. Simplify using `only [plc, hτ, embOf_restrict, InfinitePlace.mk_embedding]`. Use `not_imp_not.2 (F.cm.2 (w.embedding.comp (algebraMap (𝓞 E) E))).2 hs` as an intermediate fact. Take `⟨τ, hτ⟩` from `not_not.1 this`.

Use `⟨τ, ?_⟩` and prove the remaining obligations. Establish `: embOf (F.σ τ) = ComplexEmbedding.conjugate w.embedding`. Rewrite using `[hτ, ← RingHom.comp_assoc, embOf_restrict]`. Both sides reduce to the same expression. Simplify using `only [plc, this, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]`.
-/
theorem plc_bijective (F : UnivFam E Ψ j j' n g Λ) : Function.Bijective (plc F) := by
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact F.cm.1 (embOf_inj h)
    · exfalso
      rw [← embOf_conj] at h
      have h' := embOf_inj h
      exact (F.cm.2 (F.σ τ)).1 ⟨τ, rfl⟩ ⟨τ', h'.symm⟩
  · intro w
    by_cases hs : ∃ τ, F.σ τ = w.embedding.comp (algebraMap (𝓞 E) E)
    · obtain ⟨τ, hτ⟩ := hs
      refine ⟨τ, ?_⟩
      simp only [plc, hτ, embOf_restrict, InfinitePlace.mk_embedding]
    · have := not_imp_not.2 (F.cm.2 (w.embedding.comp (algebraMap (𝓞 E) E))).2 hs
      obtain ⟨τ, hτ⟩ := not_not.1 this
      refine ⟨τ, ?_⟩
      have : embOf (F.σ τ) = ComplexEmbedding.conjugate w.embedding := by
        rw [hτ, ← RingHom.comp_assoc, embOf_restrict]; rfl
      simp only [plc, this, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

end TmSurj

/- English proof (translation)
Introduce `E _ _ _ Ψ _ j j' n g Λ _ _ F C b hb`. Establish `hbij` using `plc_bijective F`. Set `e : Ψ ≃ InfinitePlace E` to `Equiv.ofBijective (plc F) hbij`. Establish `he : ∀ τ, e.symm (plc F τ) = τ` using `fun τ => e.symm_apply_apply τ`. Establish `hw : ∀ w, plc F (e.symm w) = w` using `fun w => e.apply_symm_apply w`.

Set `v` to `Pi.basisFun E (Fin (j + j'))`. Set `M : InfinitePlace E → Matrix (Fin (j + j')) (Fin (j + j')) ℂ` to `fun w => if w.embedding = embOf (F.σ (e.symm w)) then b (e.symm w) else (b (e.symm w)).map (starRingEnd ℂ)`. Establish `hct : ∀ X : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, (X.map (starRingEnd ℂ))ᵀ = Xᴴ` using `fun X => by`. Use extensionality with `i k`. Simplify using `[Matrix.conjTranspose_apply]`.

Establish `hM : ∀ w, ((M w).map (starRingEnd ℂ))ᵀ * gramAt C.h v w * M w = gramAt C.h v w`. Introduce `w`. Establish `hτ` using `hb (e.symm w)`. Rewrite using `[hct]`. Distinguish the cases in `hc : w.embedding = embOf (F.σ (e.symm w))`.

Establish `hg : gramAt C.h v w = C.gr (e.symm w)`. Simplify using `only [gramAt, LatEmb.gr, hc]`. Both sides reduce to the same expression. Simplify using `only [M, if_pos hc, hg]`. Conclude with `hτ`.

Establish `hconj : w.embedding = ComplexEmbedding.conjugate (embOf (F.σ (e.symm w)))`. Establish `h1 : InfinitePlace.mk (embOf (F.σ (e.symm w))) = InfinitePlace.mk w.embedding`. Rewrite using `[InfinitePlace.mk_embedding]`. Conclude with `hw w`. Break down `InfinitePlace.mk_eq_iff.1 h1 with h | h` into its components or cases.

Conclude with `absurd h.symm hc`. Conclude with `h.symm`. Establish `hg : gramAt C.h v w = (C.gr (e.symm w)).map (starRingEnd ℂ)`. Use extensionality with `i k`. Simplify using `only [gramAt, LatEmb.gr, Matrix.map_apply, hconj]`.

Both sides reduce to the same expression. Establish `h2` using `congrArg (fun X : Matrix (Fin (j + j')) (Fin (j + j')) ℂ => X.map (starRingEnd ℂ)) hτ`. Simplify using `only [Matrix.map_mul] at h2`. Establish `h3 : ((b (e.symm w)).map (starRingEnd ℂ))ᴴ = ((b (e.symm w))ᴴ).map (starRingEnd ℂ)`. Use extensionality with `i k`.

Simplify using `[Matrix.conjTranspose_apply]`. Simplify using `only [M, if_neg hc, hg]`. Rewrite using `[h3]`. Conclude with `h2`. Establish `hH : ∀ w, IsUnit (gramAt C.h v w).det`.

Introduce `w`. Use `(isUnit_det_gram C.h v).map w.embedding` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Conclude with `this`. Set `a : InfinitePlace E → GL (Fin (j + j')) ℂ` to `fun w => Matrix.nonsingInvUnit (M w) (isUnit_det_of_unitary (starRingEnd ℂ) (hH w) (hM w))`.

Establish `ha : a ∈ C.Arch` using `mem_archUnitary.2 fun w => hM w`. Use `⟨⟨a, ha⟩, fun τ => ?_⟩` and prove the remaining obligations. Establish `haM : ∀ w, (a w : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) = M w` using `fun w => rfl`. Simplify using `only [LatEmb.tm, tauMat, haM, M, he]`. Distinguish the cases in `hc : (plc F τ).embedding = embOf (F.σ τ)`.

Simplify using `only [if_pos hc]`. Simplify using `only [if_neg hc]`. Use extensionality with `i k`. Simplify using the standard rewrite rules.
-/
theorem tm_surj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (b : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), (∀ τ, (b τ)ᴴ * C.gr τ * b τ = C.gr τ) → ∃ a : C.Arch, ∀ τ, C.tm a τ = b τ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C b hb
  classical
  have hbij := plc_bijective F
  let e : Ψ ≃ InfinitePlace E := Equiv.ofBijective (plc F) hbij
  have he : ∀ τ, e.symm (plc F τ) = τ := fun τ => e.symm_apply_apply τ
  have hw : ∀ w, plc F (e.symm w) = w := fun w => e.apply_symm_apply w
  let v := Pi.basisFun E (Fin (j + j'))
  let M : InfinitePlace E → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun w =>
    if w.embedding = embOf (F.σ (e.symm w)) then b (e.symm w) else (b (e.symm w)).map (starRingEnd ℂ)
  have hct : ∀ X : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, (X.map (starRingEnd ℂ))ᵀ = Xᴴ := fun X => by
    ext i k; simp [Matrix.conjTranspose_apply]
  have hM : ∀ w, ((M w).map (starRingEnd ℂ))ᵀ * gramAt C.h v w * M w = gramAt C.h v w := by
    intro w
    have hτ := hb (e.symm w)
    rw [hct]
    by_cases hc : w.embedding = embOf (F.σ (e.symm w))
    · have hg : gramAt C.h v w = C.gr (e.symm w) := by
        simp only [gramAt, LatEmb.gr, hc]; rfl
      simp only [M, if_pos hc, hg]
      exact hτ
    · have hconj : w.embedding = ComplexEmbedding.conjugate (embOf (F.σ (e.symm w))) := by
        have h1 : InfinitePlace.mk (embOf (F.σ (e.symm w))) = InfinitePlace.mk w.embedding := by
          rw [InfinitePlace.mk_embedding]; exact hw w
        rcases InfinitePlace.mk_eq_iff.1 h1 with h | h
        · exact absurd h.symm hc
        · exact h.symm
      have hg : gramAt C.h v w = (C.gr (e.symm w)).map (starRingEnd ℂ) := by
        ext i k
        simp only [gramAt, LatEmb.gr, Matrix.map_apply, hconj]
        rfl
      have h2 := congrArg (fun X : Matrix (Fin (j + j')) (Fin (j + j')) ℂ => X.map (starRingEnd ℂ)) hτ
      simp only [Matrix.map_mul] at h2
      have h3 : ((b (e.symm w)).map (starRingEnd ℂ))ᴴ = ((b (e.symm w))ᴴ).map (starRingEnd ℂ) := by
        ext i k; simp [Matrix.conjTranspose_apply]
      simp only [M, if_neg hc, hg]
      rw [h3]
      exact h2
  have hH : ∀ w, IsUnit (gramAt C.h v w).det := by
    intro w
    have := (isUnit_det_gram C.h v).map w.embedding
    rw [RingHom.map_det] at this
    exact this
  let a : InfinitePlace E → GL (Fin (j + j')) ℂ := fun w =>
    Matrix.nonsingInvUnit (M w) (isUnit_det_of_unitary (starRingEnd ℂ) (hH w) (hM w))
  have ha : a ∈ C.Arch := mem_archUnitary.2 fun w => hM w
  refine ⟨⟨a, ha⟩, fun τ => ?_⟩
  have haM : ∀ w, (a w : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) = M w := fun w => rfl
  simp only [LatEmb.tm, tauMat, haM, M, he]
  by_cases hc : (plc F τ).embedding = embOf (F.σ τ)
  · simp only [if_pos hc]
  · simp only [if_neg hc]
    ext i k
    simp

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
